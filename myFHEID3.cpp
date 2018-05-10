/*
 * main.cpp
 *
 *  Created on: Jan 27, 2018
 *      Author: luyaoc
 */

#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <vector>
#include <map>
#include <algorithm>
#include <math.h>
#include <iomanip>
#include <chrono>
#include <random>
#include <thread>
#include <mutex>
#include <limits>
#include <cmath>

#include "timing.h"

#include <cassert>
#include <cstdio>
#include <NTL/BasicThreadPool.h>
#include <NTL/ZZ.h>
#include <NTL/lzz_pXFactoring.h>

NTL_CLIENT

#include "EncryptedArray.h"
#include "FHE.h"

#include "intraSlot.h"
#include "binaryArith.h"
#include "binaryCompare.h"
#include "tableLookup.h"
#include "CtPtrs.h"

#include <cstdlib>
#include <stdexcept>


#ifdef DEBUG_PRINTOUT
#include "debugging.h"
#endif


#include <stdlib.h>
#include <unistd.h>

#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#define ServerAddress "localhost"
//#define ServerAddress "192.168.71.147"
#define MaxBufferSize  262144
#define TcpPort 12345
#define DIRECTMAP 1

// Required by for routine
#include <sys/types.h>

using namespace std;
#define MAX_Attributes 100



/*  ################################################################

FHE Coding

 ###################################################################*/

static std::vector<zzX> unpackSlotEncoding; // a global variable
static ArgMapping amap;
static bool verbose=true;
static bool noPrint = false;
static long bitSize;
static bool bootstrap;
static long outSize;
static bool testSuccess=true;
static long p,r;
class MatrixClsEN;
class eTree;
clock_t begin_time;
int scale,mapScale;
int matrixLookupBits = 7 ;
static long mValues[][15] = {
	// { p, phi(m),   m,   d, m1, m2, m3,    g1,   g2,   g3, ord1,ord2,ord3, B,c}
	  {  2,    48,   105, 12,  3, 35,  0,    71,    76,    0,   2,  2,   0, 25, 2},
	  {  2 ,  600,  1023, 10, 11, 93,  0,   838,   584,    0,  10,  6,   0, 25, 2},
	  {  2,  2304,  4641, 24,  7,  3,221,  3979,  3095, 3760,   6,  2,  -8, 25, 3},
	  {  2, 15004, 15709, 22, 23,683,  0,  4099, 13663,    0,  22, 31,   0, 25, 3},
	  {  2, 27000, 32767, 15, 31,  7, 151, 11628, 28087,25824, 30,  6, -10, 28, 4}
};

static std::vector<zzX> T0,T1,T2;

void compareEntropy (int level, vector<Ctxt>& eMapping,vector<Ctxt>& eMappingCum,
		MatrixClsEN& MatrixEN, FHESecKey& secretKey );
void compareCounts (int target, vector<Ctxt>& eMapping, Ctxt& Result,MatrixClsEN& MatrixEN, FHESecKey& secretKey );
int checkAllValues (int target, vector<Ctxt>& eMapping, Ctxt& Result, MatrixClsEN& MatrixEN, FHESecKey& secretKey );
int rePackBin (int portno,FHESecKey& secretKey, Ctxt& input );
int checkGCBin (int portno ,FHESecKey& secretKey, Ctxt input );
int pageServer (int portno );
void validateETree(string Data_File, int totalAttributes, eTree * etree, FHESecKey& secretKey);
void buildLookupTableBin(std::vector<zzX>& T,// result is encoded and returned in T
		std::function<double(double)> f,
		const long nbits_in, // number of precision bits
		const long scale_in, // scaling factor
		const long sign_in,  // 1: 2's complement signed, 0: unsigned
		const long nbits_out,
		const long scale_out,
		const long sign_out,
		const EncryptedArray& ea);
void Binint2Poly (zzX& result, const EncryptedArray& ea,
        unsigned long data, long nbits);
static double pow2_double(long n);// compute 2^n as double

#ifdef DEBUG_PRINTOUT
#define debugCompare(ea,sk,p,c) {\
  NewPlaintextArray pp(ea);\
  ea.decrypt(c, sk, pp);\
  if (!equals(ea, pp, p)) { \
    std::cout << "oops:\n"; std::cout << p << "\n"; \
    std::cout << pp << "\n"; \
    exit(0); \
  }}
#else
#define debugCompare(ea,sk,p,c)
#endif


FHEcontext FHE_keyGen(int argc, char* argv[]) {

	long prm= 0;
	amap.arg("prm", prm, "parameter size (0-tiny,...,4-huge)");
	bitSize = 10;
	amap.arg("bitSize", bitSize, "bitSize of input integers (<=32)");
	outSize = 0;
	amap.arg("outSize", outSize, "bitSize of output integers", "as many as needed");
	bootstrap = true;
	amap.arg("bootstrap", bootstrap, "test with bootstrapping");
	long seed=0;
	amap.arg("seed", seed, "PRG seed");
	r=1;
	amap.arg("r", seed, "lifting");
	long nthreads=3;
	amap.arg("nthreads", nthreads, "number of threads");

	amap.parse(argc, argv);
	assert(prm >= 0 && prm < 5);
	if (seed) NTL::SetSeed(ZZ(seed));
	if (nthreads>1) NTL::SetNumThreads(nthreads);

	if (bitSize<=0) bitSize=5;

	else if (bitSize>32) bitSize=32;

	long* vals = mValues[prm];
	p = vals[0];
	//  long phim = vals[1];
	long m = vals[2];

	NTL::Vec<long> mvec;
	append(mvec, vals[4]);
	if (vals[5]>1) append(mvec, vals[5]);
	if (vals[6]>1) append(mvec, vals[6]);

	std::vector<long> gens;
	gens.push_back(vals[7]);
	if (vals[8]>1) gens.push_back(vals[8]);
	if (vals[9]>1) gens.push_back(vals[9]);

	std::vector<long> ords;
	ords.push_back(vals[10]);
	if (abs(vals[11])>1) ords.push_back(vals[11]);
	if (abs(vals[12])>1) ords.push_back(vals[12]);

	long B = vals[13];
	long c = vals[14];

		  // Compute the number of levels
	long L;
	if (bootstrap) L= 30; // that should be enough   Org Value 60
		else {
			double nBits =
					(outSize>0 && outSize<2*bitSize)? outSize : (2*bitSize);
		    double three4twoLvls = log(nBits/2) / log(1.5);
		    double add2NumsLvls = log(nBits) / log(2.0);
		    L = 3 + ceil(three4twoLvls + add2NumsLvls);
		}

	cout <<"input bitSize="<<bitSize<<", output size bound="<<outSize <<"\n";
	if (nthreads>1) cout << "  using "<<NTL::AvailableThreads()<<" threads\n";
	cout << "computing key-independent tables..." << std::flush;

	FHEcontext context(m, p, /*r=*/r, gens, ords);
	context.bitsPerLevel = B;
	buildModChain(context, L, c,/*extraBits=*/8);
	if (bootstrap) {
		context.makeBootstrappable(mvec, /*t=*/0,
				/*flag=*/false, /*cacheType=DCRT*/2);
		  }
	buildUnpackSlotEncoding(unpackSlotEncoding, *context.ea);
	cout << " done.\n";
	context.zMStar.printout();
	cout << " L="<<L<<", B="<<B<<endl;

	return context;

};

void buildLookupTableZZX(std::vector<zzX>& T,// result is encoded and returned in T
                      std::function<double(double)> f,
                      const long nbits_in, // number of precision bits
                      const long scale_in, // scaling factor
                      const long sign_in,  // 1: 2's complement signed, 0: unsigned
                      const long nbits_out,
                      const long scale_out,
                      const long sign_out,
                      const EncryptedArray& ea)
{
  FHE_TIMER_START;
  assert(nbits_in <= 16); // tables of size > 2^{16} are not supported
  long sz = 1L << nbits_in;
  T.resize(sz);

  double pow2_scale_in = pow2_double(scale_in);       // 2^{nbits_in}
  double pow2_neg_scale_out = pow2_double(-scale_out);// 2^{-nbits_out}

  // Compute the largest and smallest values that can be in T
  long largest_value, smallest_value;
  if (sign_out) { // values in T are encoded in 2's complement
    largest_value = (1L << (nbits_out-1)) - 1;
    smallest_value = - (1L << (nbits_out-1));
  }
  else {          // values in T are all non-negative
    largest_value = (1L << nbits_out) - 1;
    smallest_value = 0;
  }

  for (long i = 0; i<sz; i++) { // Compute the entries of T
    long x;
    if (sign_in) { // indexes into T are in 2's complement
      long sign_bit = (1L << (nbits_in-1)) & i;
      x = i - 2*sign_bit;
    }
    else x = i;    // indexes into T are all non-negative

    // Compute the value that should go in the table as rounded double
    double scaled_x = double(x)*pow2_scale_in;
    double y = round(f(scaled_x)*pow2_neg_scale_out);

    // saturated arithmetic (set to smallest or largest values)
    // NOTE: this should work fine even if y is an infinity
    long value;
    if (std::isnan(y))           value = 0;
    else if (y > largest_value)  value = largest_value;
    else if (y < smallest_value) value = smallest_value;
    else                         value = y;

    // convert to unsigned and mask to nbits_out bits
    unsigned long uvalue = value;
    uvalue &= ((1UL << nbits_out) -1UL); // keep only bottom nbits_out bits

    packConstant(T[i], uvalue, nbits_out, ea);
    /*

     */
  }
}

void buildLookupTableBin(std::vector<zzX>& T,// result is encoded and returned in T
                      std::function<double(double)> f,
                      const long nbits_in, // number of precision bits
                      const long scale_in, // scaling factor
                      const long sign_in,  // 1: 2's complement signed, 0: unsigned
                      const long nbits_out,
                      const long scale_out,
                      const long sign_out,
                      const EncryptedArray& ea)
{
  FHE_TIMER_START;
  assert(nbits_in <= 16); // tables of size > 2^{16} are not supported
  long sz = 1L << nbits_in;
  T.resize(sz);

  double pow2_scale_in = pow2_double(scale_in);       // 2^{nbits_in}
  double pow2_neg_scale_out = pow2_double(-scale_out);// 2^{-nbits_out}

  // Compute the largest and smallest values that can be in T
  long largest_value, smallest_value;
  if (sign_out) { // values in T are encoded in 2's complement
    largest_value = (1L << (nbits_out-1)) - 1;
    smallest_value = - (1L << (nbits_out-1));
  }
  else {          // values in T are all non-negative
    largest_value = (1L << nbits_out) - 1;
    smallest_value = 0;
  }

  for (long i = 0; i<sz; i++) { // Compute the entries of T
    long x;
    if (sign_in) { // indexes into T are in 2's complement
      long sign_bit = (1L << (nbits_in-1)) & i;
      x = i - 2*sign_bit;
    }
    else x = i;    // indexes into T are all non-negative

    // Compute the value that should go in the table as rounded double
    double scaled_x = double(x)*pow2_scale_in;
    double y = round(f(scaled_x)*pow2_neg_scale_out);

    // saturated arithmetic (set to smallest or largest values)
    // NOTE: this should work fine even if y is an infinity
    long value;
    if (std::isnan(y))           value = 0;
    else if (y > largest_value)  value = largest_value;
    else if (y < smallest_value) value = smallest_value;
    else                         value = y;

    // convert to unsigned and mask to nbits_out bits
    unsigned long uvalue = value;
    uvalue &= ((1UL << nbits_out) -1UL); // keep only bottom nbits_out bits

    Binint2Poly(T[i] ,ea, uvalue , bitSize );

    /*

     */
  }
}

void Binint2Poly (zzX& result, const EncryptedArray& ea,
        unsigned long data, long nbits) {

	   NTL::GF2X acc_poly;

	   const EncryptedArrayDerived<PA_GF2>& rep = ea.getDerived(PA_GF2());

	   long d = rep.getDegree(); // size of each slot

	    assert(nbits >= 0 && nbits <= d);

	     const NTL::Mat<NTL::GF2> CB= rep.getNormalBasisMatrix();
	    // CB contains a description of the normal-basis transformation

	    NTL::Vec<NTL::GF2> acc;
	    acc.SetLength(d);
	    clear(acc); // clear all d bits in acc, length stays =d

	    for (long i = 0; i < nbits; i++) {  // compute sum_i bit_i * X^{p^i}
	      if ((data >> i) & 1)
 	        add(acc, acc, CB[i]); // add each CB[i][j] to acc[j]
	       // cout << i << " - " << ((data >> i) & 1) << " - " <<  acc <<endl;
	    }

	    conv(acc_poly, acc); // convert from vec<R> to a polynomial RX

	    convert(result,acc_poly);

}



static double pow2_double(long n) // compute 2^n as double
{
   double res = 1;
   long abs_n = std::labs(n);

   for (long i = 0; i < abs_n; i++) res *= 2;
   if (n < 0) res = 1/res;
   return res;
}


class MatrixClsEN
{
private:
	vector < vector < Ctxt > > MatrixEN;
	vector < vector < Ctxt > > MatrixRefEN;
	vector < vector < Ctxt > > MatrixNegEN;
	int Instances=0;

public:
	MatrixClsEN(string Data_File, FHESecKey& secretKey) {

	 	const FHEPubKey& publicKey = secretKey;

	    MatrixEN.erase(MatrixEN.begin(),MatrixEN.end());
	    MatrixRefEN.erase(MatrixRefEN.begin(),MatrixRefEN.end());
	    MatrixNegEN.erase(MatrixNegEN.begin(),MatrixNegEN.end());
		ifstream Data(Data_File);
		string line;
		int item;
		vector < Ctxt> RowEN;
		vector < Ctxt> RowRefEN;
		vector < Ctxt> RowNegEN;
		getline(Data, line);    //skip the header
  		while(!Data.eof())
		{
			getline(Data, line);
		 	istringstream iss(line);
			while(iss >> item)
			{

				if (item >= 0 && item <= MAX_Attributes)
				{
					  Ctxt itemEN(publicKey);
					  secretKey.Encrypt(itemEN, ZZX(item &1));
					  RowEN.push_back(itemEN);

					  Ctxt itemRefEN(publicKey);
					  secretKey.Encrypt(itemRefEN, ZZX(1));
					  RowRefEN.push_back(itemRefEN);

					  Ctxt itemNegEN(publicKey);
					  secretKey.Encrypt(itemNegEN, ZZX((1-item)&1));
					  RowNegEN.push_back(itemNegEN);
				}
			}

			if(line.length())
			{
				MatrixEN.push_back(RowEN);
				MatrixRefEN.push_back(RowRefEN);
				MatrixNegEN.push_back(RowNegEN);
				RowEN.erase(RowEN.begin(),RowEN.end());
				RowRefEN.erase(RowRefEN.begin(),RowRefEN.end());
				RowNegEN.erase(RowNegEN.begin(),RowNegEN.end());
			}
		}
		Instances =  MatrixEN.size();

		cout << "Data Read MatrixEN:" << MatrixEN.size() << " rows, " <<  MatrixEN[0].size() << " columns\n";
		cout << "Data Read MatrixRefEN:" << MatrixRefEN.size() << " rows, " <<  MatrixRefEN[0].size() << " columns\n";
		cout << "Data Read MatrixNegEN:" << MatrixNegEN.size() << " rows, " <<  MatrixNegEN[0].size() << " columns\n";

		Data.close();
}

	MatrixClsEN(MatrixClsEN& MatrixClsENA,vector<Ctxt>& eMapping,int reversal, FHESecKey& secretKey) {

		const EncryptedArray& ea = *(secretKey.getContext().ea);
		const FHEPubKey& publicKey = secretKey;

	    MatrixEN.erase(MatrixEN.begin(),MatrixEN.end());
	    MatrixRefEN.erase(MatrixRefEN.begin(),MatrixRefEN.end());
	    MatrixNegEN.erase(MatrixNegEN.begin(),MatrixNegEN.end());
	 	vector < Ctxt> RowEN;
		vector < Ctxt> RowRefEN;
		vector < Ctxt> RowNegEN;
		Instances = MatrixClsENA.Instances;

		// dupdate the org matrix first
		for ( int i = 0; i < MatrixClsENA.SizeY();i++){
			for ( int j = 0; j < MatrixClsENA.SizeX();j++){
				 Ctxt itemEN(MatrixClsENA.MatrixEN[i][j]);
	 			 RowEN.push_back(itemEN);

				 Ctxt itemRefEN(MatrixClsENA.MatrixRefEN[i][j]);
 				 RowRefEN.push_back(itemRefEN);

				 Ctxt itemNegEN(MatrixClsENA.MatrixNegEN[i][j]);
 				 RowNegEN.push_back(itemNegEN);
			}
			MatrixEN.push_back(RowEN);
			MatrixRefEN.push_back(RowRefEN);
			MatrixNegEN.push_back(RowNegEN);
			RowEN.erase(RowEN.begin(),RowEN.end());
			RowRefEN.erase(RowRefEN.begin(),RowRefEN.end());
			RowNegEN.erase(RowNegEN.begin(),RowNegEN.end());
		}


	   vector<Ctxt> eMappingCol(MatrixClsENA.SizeY(), Ctxt(publicKey));

	    for ( size_t i = 0; i < eMappingCol.size(); i++ ) {
	     	for ( int j = 0; j < eMapping.size(); j++ ) {
 	     	  Ctxt cell (publicKey);
	    	  cell = MatrixEN[i][j];
	    	  cell.multiplyBy(eMapping[j]);
 	    	  if ( j == 0) {
	    		  eMappingCol[i] = cell;
 	    	  }
	    	  else {
	    		  eMappingCol[i].addCtxt(cell);
 	    	  }
	     	 }
	     	if (reversal == 1 ) eMappingCol[i].addConstant(ZZX(1));
	 	    }


	    for ( size_t i = 0; i < eMappingCol.size(); i++ ) {
	    	for ( int j = 0; j < MatrixClsENA.SizeX(); j++ ) {
	    		MatrixRefEN[i][j].multiplyBy(eMappingCol[i]);
	    	}
	    }
		cout << "MatrixEN duplicated\n";
	}


	MatrixClsEN(){ };
	~MatrixClsEN(){ };

	Ctxt Element(int i,int j)
	{
		return MatrixEN[i][j];
	}

	int SizeX()  //Attributes
	{
		return MatrixEN[0].size();
	}

	std::size_t SizeY() // instances (rows)
	{
		return MatrixEN.size();
	}

	vector < Ctxt > GetAttributes()
    {
		vector < Ctxt > Attribute;
		std::size_t j;
		for(j = 0; j < MatrixEN[0].size()-1; j++)
		{
			Attribute.push_back(MatrixEN[0][j]);
		}
		return Attribute;
    }

void Count_1_FHE (int columnID, CtPtrs_VecCt& countEN,FHESecKey& secretKey){

		const EncryptedArray& ea = *(secretKey.getContext().ea);
		const FHEPubKey& publicKey = secretKey;

		NTL::Vec<Ctxt> eData,eDataRef;
	 	resize(eData, bitSize, Ctxt(publicKey));
		resize(eDataRef, bitSize, Ctxt(publicKey));

		NTL::Vec< NTL::Vec<Ctxt> > numbers(INIT_SIZE,this->SizeY());


		for ( size_t i = 0; i < this->SizeY(); i ++ ) {

			eData[0] = MatrixEN[i][columnID];
			eDataRef[0] = MatrixRefEN[i][columnID];

			NTL::Vec<Ctxt> eTemp;
			resize(eTemp, bitSize, Ctxt(publicKey));
			CtPtrs_VecCt tempEN(eTemp);

		 	multTwoNumbers(tempEN,CtPtrs_VecCt(eData),CtPtrs_VecCt(eDataRef),false,bitSize, &unpackSlotEncoding);
		 	NTL::Vec<Ctxt> etest=tempEN.v;
		    numbers[i] = etest;
    	}
 		CtPtrMat_VecCt rows(numbers);
		addManyNumbers(countEN, rows, bitSize, &unpackSlotEncoding );


	}


void Count_0_FHE (int columnID,CtPtrs_VecCt& countEN, FHESecKey& secretKey){

	const EncryptedArray& ea = *(secretKey.getContext().ea);
	const FHEPubKey& publicKey = secretKey;

	NTL::Vec<Ctxt> eData,eDataRef;
	resize(eData, bitSize, Ctxt(publicKey));
	resize(eDataRef, bitSize, Ctxt(publicKey));


	NTL::Vec< NTL::Vec<Ctxt> > numbers(INIT_SIZE,this->SizeY());

	for ( size_t i = 0; i < this->SizeY(); i ++ ) {

		eData[0] = MatrixNegEN[i][columnID];
		eDataRef[0] = MatrixRefEN[i][columnID];

		NTL::Vec<Ctxt> eTemp;
		resize(eTemp, bitSize, Ctxt(publicKey));
		CtPtrs_VecCt tempEN(eTemp);

		multTwoNumbers(tempEN,CtPtrs_VecCt(eData),CtPtrs_VecCt(eDataRef),false,bitSize, &unpackSlotEncoding);
	 	NTL::Vec<Ctxt> etest=tempEN.v;
	 	numbers[i] = etest;
	}
	CtPtrMat_VecCt rows(numbers);
	addManyNumbers(countEN, rows, bitSize, &unpackSlotEncoding );




}


void Count_1_Final_FHE (CtPtrs_VecCt& countEN,FHESecKey& secretKey){

		const EncryptedArray& ea = *(secretKey.getContext().ea);
		const FHEPubKey& publicKey = secretKey;

		NTL::Vec<Ctxt> eData,eDataRef;
	 	resize(eData, bitSize, Ctxt(publicKey));
		resize(eDataRef, bitSize, Ctxt(publicKey));

		NTL::Vec< NTL::Vec<Ctxt> > numbers(INIT_SIZE,this->SizeY());

		for ( size_t i = 0; i < this->SizeY(); i ++ ) {

			eData[0] = MatrixEN[i][this->SizeX()-1];
			eDataRef[0] = MatrixRefEN[i][1];

			NTL::Vec<Ctxt> eTemp;
			resize(eTemp, bitSize, Ctxt(publicKey));
			CtPtrs_VecCt tempEN(eTemp);

		 	multTwoNumbers(tempEN,CtPtrs_VecCt(eData),CtPtrs_VecCt(eDataRef),false,bitSize, &unpackSlotEncoding);
		 	NTL::Vec<Ctxt> etest=tempEN.v;
		    numbers[i] = etest;
    	}
 		CtPtrMat_VecCt rows(numbers);
		addManyNumbers(countEN, rows, bitSize, &unpackSlotEncoding );
	}


void Count_0_Final_FHE (CtPtrs_VecCt& countEN,FHESecKey& secretKey){

		const EncryptedArray& ea = *(secretKey.getContext().ea);
		const FHEPubKey& publicKey = secretKey;

		NTL::Vec<Ctxt> eData,eDataRef;
	 	resize(eData, bitSize, Ctxt(publicKey));
		resize(eDataRef, bitSize, Ctxt(publicKey));

		NTL::Vec< NTL::Vec<Ctxt> > numbers(INIT_SIZE,this->SizeY());

		for ( size_t i = 0; i < this->SizeY(); i ++ ) {

			eData[0] = MatrixNegEN[i][this->SizeX()-1];
			eDataRef[0] = MatrixRefEN[i][1];

			NTL::Vec<Ctxt> eTemp;
			resize(eTemp, bitSize, Ctxt(publicKey));
			CtPtrs_VecCt tempEN(eTemp);

		 	multTwoNumbers(tempEN,CtPtrs_VecCt(eData),CtPtrs_VecCt(eDataRef),false,bitSize, &unpackSlotEncoding);
		 	NTL::Vec<Ctxt> etest=tempEN.v;
		    numbers[i] = etest;
    	}
 		CtPtrMat_VecCt rows(numbers);
		addManyNumbers(countEN, rows, bitSize, &unpackSlotEncoding );
	}

void  Count_1_1_FHE (int columnID, CtPtrs_VecCt& countEN, FHESecKey& secretKey){

		const EncryptedArray& ea = *(secretKey.getContext().ea);
		const FHEPubKey& publicKey = secretKey;


		NTL::Vec<Ctxt> eData,eDataRef,eDataClass;
 		resize(eDataClass, bitSize, Ctxt(publicKey));
 		resize(eData, bitSize, Ctxt(publicKey));
		resize(eDataRef, bitSize, Ctxt(publicKey));

		NTL::Vec< NTL::Vec<Ctxt> > numbers(INIT_SIZE,this->SizeY());

		for ( size_t i = 0; i < this->SizeY(); i ++ ) {

			eData[0] = MatrixEN[i][columnID];
			eDataRef[0] = MatrixRefEN[i][columnID];
			eDataClass[0] = MatrixEN[i][this->SizeX()-1];  // result

			NTL::Vec<Ctxt> eTemp;
			resize(eTemp, bitSize, Ctxt(publicKey));
			CtPtrs_VecCt tempEN(eTemp);
			NTL::Vec<Ctxt> eTemp1;
			resize(eTemp1, bitSize, Ctxt(publicKey));
			CtPtrs_VecCt tempEN1(eTemp1);

			multTwoNumbers(tempEN1,CtPtrs_VecCt(eData),CtPtrs_VecCt(eDataRef),false,bitSize, &unpackSlotEncoding);
		 	multTwoNumbers(tempEN,CtPtrs_VecCt(eDataClass),tempEN1,false,bitSize, &unpackSlotEncoding);
		 	NTL::Vec<Ctxt> etest=tempEN.v;
		    numbers[i] = etest;
		}

 		CtPtrMat_VecCt rows(numbers);
  		addManyNumbers(countEN, rows, bitSize, &unpackSlotEncoding );
  	}

void  Count_1_0_FHE (int columnID,CtPtrs_VecCt& countEN, FHESecKey& secretKey){

		const EncryptedArray& ea = *(secretKey.getContext().ea);
		const FHEPubKey& publicKey = secretKey;

		NTL::Vec<Ctxt>  eData,eDataRef,eDataClass;
		resize(eDataClass, bitSize, Ctxt(publicKey));
 		resize(eData, bitSize, Ctxt(publicKey));
		resize(eDataRef, bitSize, Ctxt(publicKey));

		NTL::Vec< NTL::Vec<Ctxt> > numbers(INIT_SIZE,this->SizeY());


		for ( size_t i = 0; i < this->SizeY(); i ++ ) {

			eData[0] = MatrixEN[i][columnID];
			eDataRef[0] = MatrixRefEN[i][columnID];
			eDataClass[0] = MatrixNegEN[i][this->SizeX()-1];


			NTL::Vec<Ctxt> eTemp;
			resize(eTemp, bitSize, Ctxt(publicKey));
			CtPtrs_VecCt tempEN(eTemp);

			NTL::Vec<Ctxt> eTemp1;
			resize(eTemp1, bitSize, Ctxt(publicKey));
			CtPtrs_VecCt tempEN1(eTemp1);

			multTwoNumbers(tempEN1,CtPtrs_VecCt(eData),CtPtrs_VecCt(eDataRef),false,bitSize, &unpackSlotEncoding);
		 	multTwoNumbers(tempEN,CtPtrs_VecCt(eDataClass),tempEN1,false,bitSize, &unpackSlotEncoding);
		 	NTL::Vec<Ctxt> etest=tempEN.v;
		    numbers[i] = etest;
    	}
 		CtPtrMat_VecCt rows(numbers);
		addManyNumbers(countEN, rows, bitSize, &unpackSlotEncoding );

}

void  Count_0_1_FHE (int columnID, CtPtrs_VecCt& countEN,FHESecKey& secretKey){

		const EncryptedArray& ea = *(secretKey.getContext().ea);
		const FHEPubKey& publicKey = secretKey;

		NTL::Vec<Ctxt> eData,eDataRef,eDataClass;
 		resize(eDataClass, bitSize, Ctxt(publicKey));
 		resize(eData, bitSize, Ctxt(publicKey));
		resize(eDataRef, bitSize, Ctxt(publicKey));

		NTL::Vec< NTL::Vec<Ctxt> > numbers(INIT_SIZE,this->SizeY());

		for ( size_t i = 0; i < this->SizeY(); i ++ ) {

			eData[0] = MatrixNegEN[i][columnID];
			eDataRef[0] = MatrixRefEN[i][columnID];
			eDataClass[0] = MatrixEN[i][this->SizeX()-1];


			NTL::Vec<Ctxt> eTemp;
			resize(eTemp, bitSize, Ctxt(publicKey));
			CtPtrs_VecCt tempEN(eTemp);

			NTL::Vec<Ctxt> eTemp1;
			resize(eTemp1, bitSize, Ctxt(publicKey));
			CtPtrs_VecCt tempEN1(eTemp1);

			multTwoNumbers(tempEN1,CtPtrs_VecCt(eData),CtPtrs_VecCt(eDataRef),false,bitSize, &unpackSlotEncoding);
		 	multTwoNumbers(tempEN,CtPtrs_VecCt(eDataClass),tempEN1,false,bitSize, &unpackSlotEncoding);
		 	NTL::Vec<Ctxt> etest=tempEN.v;
		    numbers[i] = etest;
    	}
 		CtPtrMat_VecCt rows(numbers);
		addManyNumbers(countEN, rows, bitSize, &unpackSlotEncoding );

	}

void  Count_0_0_FHE (int columnID, CtPtrs_VecCt& countEN,FHESecKey& secretKey){

		const EncryptedArray& ea = *(secretKey.getContext().ea);
		const FHEPubKey& publicKey = secretKey;

		NTL::Vec<Ctxt> eData,eDataRef,eDataClass;
 		resize(eDataClass, bitSize, Ctxt(publicKey));
 		resize(eData, bitSize, Ctxt(publicKey));
		resize(eDataRef, bitSize, Ctxt(publicKey));

		NTL::Vec< NTL::Vec<Ctxt> > numbers(INIT_SIZE,this->SizeY());

		for ( size_t i = 0; i < this->SizeY(); i ++ ) {

			eData[0] = MatrixNegEN[i][columnID];
			eDataRef[0] = MatrixRefEN[i][columnID];
			eDataClass[0] = MatrixNegEN[i][this->SizeX()-1];


			NTL::Vec<Ctxt> eTemp;
			resize(eTemp, bitSize, Ctxt(publicKey));
			CtPtrs_VecCt tempEN(eTemp);

			NTL::Vec<Ctxt> eTemp1;
			resize(eTemp1, bitSize, Ctxt(publicKey));
			CtPtrs_VecCt tempEN1(eTemp1);

			multTwoNumbers(tempEN1,CtPtrs_VecCt(eData),CtPtrs_VecCt(eDataRef),false,bitSize, &unpackSlotEncoding);
		 	multTwoNumbers(tempEN,CtPtrs_VecCt(eDataClass),tempEN1,false,bitSize, &unpackSlotEncoding);
		 	NTL::Vec<Ctxt> etest=tempEN.v;
		    numbers[i] = etest;
    	}
 		CtPtrMat_VecCt rows(numbers);
		addManyNumbers(countEN, rows, bitSize, &unpackSlotEncoding );

	}


	void Display(FHESecKey secretKey)
	{
		std::size_t i, j;
		cout << "Decrypt Data Matrix: \n";
		for(i = 0; i < MatrixEN.size(); i++)
		{
			for(j = 0; j < MatrixEN[0].size(); j++)
			{
				ZZX item;
				secretKey.Decrypt(item, MatrixEN[i][j]);
				cout << " " << item[0] ;
			}
			cout << endl;
		}
		cout << "Decrypt Reference Matrix: \n";
			for(i = 0; i < MatrixRefEN.size(); i++)
			{
				for(j = 0; j < MatrixRefEN[0].size(); j++)
				{
					ZZX item;
					secretKey.Decrypt(item, MatrixRefEN[i][j]);
					cout << " " << item[0] ;
				}
				cout << endl;
			}
		cout << "Decrypt Negative Matrix: \n";
			for(i = 0; i < MatrixNegEN.size(); i++)
			{
				for(j = 0; j < MatrixNegEN[0].size(); j++)
				{
					ZZX item;
					secretKey.Decrypt(item, MatrixNegEN[i][j]);
					cout << " " << item[0] ;
				}
				cout << endl;
			}


	} // display

};

// a quick version, only work for A,B < 32)
double  EntropyMapping ( int count){
	double countA,countB,countAB;
	double entropy ;

//	countA =  count / 32;                 // 32*32 matrix
//	countB =  count % 32;
	int sc = pow2_double(matrixLookupBits);
	countA =  count / sc;				  // 128 * 128 matrix
	countB =  count % sc;

	countAB = countA +countB;

	if ( countA == 0 || countB == 0 ) {
		entropy = 0;
	}
	else {
		entropy = -(countA/countAB)*log(countA/countAB)/log(2.0)
				  -(countB/countAB)*log(countB/countAB)/log(2.0);
	}
// 	cout << "entropy" << entropy << endl;
	return entropy ;

}

double  LogMapping ( double x ){

	double result;

	if ( x == 0 ) {
		result = 0;
	}
	else {
		result = log(x)/log(2)*32;
	}
 	return result ;

}

double  InverseMapping ( double x ){

	double result;

	if ( x == 0 ) {
		result = 0;
	}
	else {
		result =  1024 / x ;
	}

	return result ;

}

void  EntropyMapEnc (   NTL::Vec<Ctxt>& eEntropyVec, NTL::Vec<Ctxt>& eAVec,NTL::Vec<Ctxt>& eBVec, FHESecKey& secretKey ){
	    const EncryptedArray& ea = *(secretKey.getContext().ea);
		const FHEPubKey& publicKey = secretKey;
		// not required now
}
void  EntropyCalEnc ( NTL::Vec<Ctxt>& eEntropyVec, NTL::Vec<Ctxt>& eAVec,NTL::Vec<Ctxt>& eBVec,  FHESecKey& secretKey ){

	const EncryptedArray& ea = *(secretKey.getContext().ea);
	  const FHEPubKey& publicKey = secretKey;


	  long n=2;
	  long d = ea.getDegree(); // size of each slot

	  std::vector<zzX> unpackSlotEncoding;
	  buildUnpackSlotEncoding(unpackSlotEncoding, ea);

	  std::vector<Ctxt> EA(n, Ctxt(publicKey)),EB(n, Ctxt(publicKey)),
			  EAB(n, Ctxt(publicKey)),DAB(n, Ctxt(publicKey));

	  NTL::Vec<Ctxt> eABVec;
	  resize(eABVec, bitSize, Ctxt(publicKey));

	  CtPtrs_VecCt countAMap(eAVec);
	  CtPtrs_VecCt countBMap(eBVec);
	  CtPtrs_VecCt countABMap(eABVec);

	  addTwoNumbers(countABMap,countAMap,countBMap,
	    			10, &unpackSlotEncoding);

	  tableLookup(EA[0], T1, countAMap ,&unpackSlotEncoding );
	  tableLookup(EB[0], T1, countBMap ,&unpackSlotEncoding );
	  tableLookup(EAB[0], T1, countABMap ,&unpackSlotEncoding );
	  tableLookup(DAB[0], T2, countABMap ,&unpackSlotEncoding );


	  cout << "  (4)Lookup done" << endl;

	  NewPlaintextArray PA1(ea);
	  vector<ZZX> arrayZZX (ea.size());
	  encode(ea,PA1,arrayZZX);
	  ea.encrypt(EA[1],publicKey,PA1);
	  ea.encrypt(EB[1],publicKey,PA1);
	  ea.encrypt(EAB[1],publicKey,PA1);
	  ea.encrypt(DAB[1],publicKey,PA1);


	  // Unpack them to Binary encoding
	 vector<Ctxt> logAxtmp(d*n -1, Ctxt(publicKey));
	 vector<Ctxt> logBxtmp(d*n -1, Ctxt(publicKey));
	 vector<Ctxt> logABxtmp(d*n -1, Ctxt(publicKey));
	 vector<Ctxt> divABxtmp(d*n -1, Ctxt(publicKey));
	 unpack(CtPtrs_vectorCt(logAxtmp), CtPtrs_vectorCt(EA), ea, unpackSlotEncoding);
	 unpack(CtPtrs_vectorCt(logBxtmp), CtPtrs_vectorCt(EB), ea, unpackSlotEncoding);
	 unpack(CtPtrs_vectorCt(logABxtmp), CtPtrs_vectorCt(EAB), ea, unpackSlotEncoding);
	 unpack(CtPtrs_vectorCt(divABxtmp), CtPtrs_vectorCt(DAB), ea, unpackSlotEncoding);



	 NTL::Vec<Ctxt> elogAVec,elogBVec,elogABVec,edivABVec;
	 resize(elogAVec, bitSize, Ctxt(publicKey));
	 resize(elogBVec, bitSize, Ctxt(publicKey));
	 resize(elogABVec, bitSize, Ctxt(publicKey));
	 resize(edivABVec, bitSize, Ctxt(publicKey));
	 for ( long j = 0; j < lsize(elogAVec);j++) {
		 elogAVec[j] = logAxtmp[j];
		 elogBVec[j] = logBxtmp[j];
		 elogABVec[j] = logABxtmp[j]; // logABxtmp[j+1] if SHIFT 	TO RIGHT TO DEVIDE BY 2 ( 1 digits)
		 edivABVec[j] = divABxtmp[j];

	 }

	 CtPtrs_VecCt elogA(elogAVec);
	 CtPtrs_VecCt elogB(elogBVec);
	 CtPtrs_VecCt elogAB(elogABVec);
	 CtPtrs_VecCt edivAB(edivABVec);


	 vector<long> slots;
	 decryptBinaryNums(slots, elogA, secretKey, ea);
	 cout<< "log A " << slots[0] <<endl;
	 decryptBinaryNums(slots, elogB, secretKey, ea);
	 cout<< "log B " << slots[0] <<endl;
	 decryptBinaryNums(slots, elogAB, secretKey, ea);
	 	 cout<< "log AB " << slots[0] <<endl;
	 decryptBinaryNums(slots, edivAB, secretKey, ea);
	 cout<< "Div A+B " << slots[0] <<endl;

	cout << "  mapping done" << endl;


    NTL::Vec<Ctxt> eGainA1Vec,eGainA2Vec,eGainA3Vec,
				   eGainB1Vec,eGainB2Vec,eGainB3Vec,
				   eGainA1Vec10,eGainB1Vec10,
				   eEntropyNegVec,eEntropySumVec;

	resize(eGainA1Vec, 20, Ctxt(publicKey));
	resize(eGainA1Vec10, 10, Ctxt(publicKey));
	resize(eGainA2Vec, 20, Ctxt(publicKey));
	resize(eGainA3Vec, 10, Ctxt(publicKey));
	resize(eGainB1Vec, 20, Ctxt(publicKey));
	resize(eGainB1Vec10, 10, Ctxt(publicKey));
	resize(eGainB2Vec, 20, Ctxt(publicKey));
	resize(eGainB3Vec, 10, Ctxt(publicKey));
	resize(eEntropyNegVec, 10, Ctxt(publicKey));
	resize(eEntropySumVec, 10, Ctxt(publicKey));

	CtPtrs_VecCt eGainA1(eGainA1Vec);
	CtPtrs_VecCt eGainA2(eGainA2Vec);
	CtPtrs_VecCt eGainA3(eGainA3Vec);
	CtPtrs_VecCt eGainB1(eGainB1Vec);
	CtPtrs_VecCt eGainB2(eGainB2Vec);
	CtPtrs_VecCt eGainB3(eGainB3Vec);
	CtPtrs_VecCt eEntropy(eEntropyVec);
	CtPtrs_VecCt eEntropyNeg(eEntropyNegVec);
	CtPtrs_VecCt eEntropySum(eEntropySumVec);

 	multTwoNumbers(eGainA1,CtPtrs_VecCt(eAVec),elogA,false,
   		                 20, &unpackSlotEncoding);
 	multTwoNumbers(eGainB1,CtPtrs_VecCt(eBVec),elogB,false,
 	   		             20, &unpackSlotEncoding);

 	decryptBinaryNums(slots, eGainA1, secretKey, ea);
 		 cout<< "mul A*log2A " << slots[0] <<endl;

 	decryptBinaryNums(slots, eGainB1, secretKey, ea);
 		 cout<< "mul B*log2A " << slots[0] <<endl;

 	for (int i = 0; i< 10; i++){
 		eGainA1Vec10[i] = eGainA1Vec[i+10];
 		eGainB1Vec10[i] = eGainB1Vec[i+10];
 	}


 	decryptBinaryNums(slots, CtPtrs_VecCt(eGainA1Vec10), secretKey, ea);
 	cout<< "shrink A*log2A " << slots[0] <<endl;
 	decryptBinaryNums(slots, CtPtrs_VecCt(eGainB1Vec10), secretKey, ea);
 	cout<< "shrink B*log2A " << slots[0] <<endl;

 	multTwoNumbers(eGainA2,CtPtrs_VecCt(eGainA1Vec10),edivAB,false,
 	   		                 20, &unpackSlotEncoding);
	multTwoNumbers(eGainB2,CtPtrs_VecCt(eGainB1Vec10),edivAB,false,
 	   		                 20, &unpackSlotEncoding);

	decryptBinaryNums(slots, eGainA2, secretKey, ea);
	cout<< "mul A*log2A*1/AB " << slots[0] <<endl;
	decryptBinaryNums(slots, eGainB2, secretKey, ea);
	cout<< "mul B*log2B*1/AB " << slots[0] <<endl;

	for (int i = 0; i< bitSize; i++){
	 		eGainA3Vec[i] = eGainA2Vec[i + 0];
	 		eGainB3Vec[i] = eGainB2Vec[i + 0];
	 	}

 	decryptBinaryNums(slots, eGainA3, secretKey, ea);
 	cout<< "shrinked A*log2A*1/AB " << slots[0] <<endl;
 	decryptBinaryNums(slots, eGainB3, secretKey, ea);
 	cout<< "shrinked B*log2B*1/AB " << slots[0] <<endl;

    addTwoNumbers(eEntropySum,eGainA3,eGainB3,
    		10, &unpackSlotEncoding);
	decryptBinaryNums(slots, eEntropySum, secretKey, ea);
	cout<< "shrinked (A*log2A*1/AB + B*log2B*1/AB)" << slots[0] <<endl;

 	NTL::Vec<Ctxt> eSub,enc1;
 	resize(enc1, 1, Ctxt(secretKey));
 	resize(eSub, bitSize+1, Ctxt(secretKey));

 	CtPtrs_VecCt eesub(eSub);
 	secretKey.Encrypt(enc1[0], ZZX(1));
 	multTwoNumbers(eEntropyNeg,eEntropySum,CtPtrs_VecCt(enc1),/*negative=*/true,
 	  		 		 	10, &unpackSlotEncoding);   // get neg of eEntropySum
 	addTwoNumbers(eesub, elogAB ,eEntropyNeg,
 						10, &unpackSlotEncoding);

  	for (int i = 0; i< bitSize; i++){
  		eEntropyVec[i] = eSub[i];
  	}

 	decryptBinaryNums(slots, eEntropy, secretKey, ea);
 	cout<< " Entropy gain log AB - (A+B) " << slots[0] <<endl;


    cout << "  Calculation Done" << endl;

}

void compareCounts (int target, vector<Ctxt>& eMapping, Ctxt& Result, MatrixClsEN& MatrixEN, FHESecKey& secretKey ) {

		const EncryptedArray& ea = *(secretKey.getContext().ea);
		const FHEPubKey& publicKey = secretKey;

		NTL::Vec<Ctxt> countVec1,countVec0,count1ENSumVec,count0ENSumVec;
	 	resize(countVec1, bitSize, Ctxt(publicKey));
	 	resize(countVec0, bitSize, Ctxt(publicKey));
	 	resize(count1ENSumVec, bitSize, Ctxt(publicKey));
	 	resize(count0ENSumVec, bitSize, Ctxt(publicKey));
	 	CtPtrs_VecCt count1EN(countVec1);
	 	CtPtrs_VecCt count0EN(countVec0);
	 	CtPtrs_VecCt count1ENSum(count1ENSumVec);
	 	CtPtrs_VecCt count0ENSum(count0ENSumVec);

	 	cout << " Comapre For -- " << target << endl;
	 	for ( int i =0; i < (MatrixEN.SizeX() -1 );i++) {
	 		if (target == 0) {
	 			MatrixEN.Count_0_1_FHE(i,count1EN, secretKey);
	 			MatrixEN.Count_0_0_FHE(i,count0EN, secretKey);
	 		} else {
	 		 	MatrixEN.Count_1_1_FHE(i,count1EN, secretKey);
	 		 	MatrixEN.Count_1_0_FHE(i,count0EN, secretKey);
	 		}



	 		for ( int j = 0; j< bitSize; j++ ) {
	 			countVec1[j].multiplyBy(eMapping[i]);
	 			countVec0[j].multiplyBy(eMapping[i]);
	 			if (i==0) {
	 				count1ENSumVec[j] =  countVec1[j];
	 				count0ENSumVec[j] =  countVec0[j];
	 			}
	 			else {
	 				count1ENSumVec[j].addCtxt(countVec1[j]);
	 				count0ENSumVec[j].addCtxt(countVec0[j]);
	 			}
	  		}

	 	}
	 	vector<long> slotsa;
	 	decryptBinaryNums(slotsa, count1ENSum, secretKey, ea);
	 	cout << "     Count of 1 is: ** " << slotsa[0] << endl;
	 	decryptBinaryNums(slotsa, count0ENSum, secretKey, ea);
	 	cout << "     Count of 0 is: ** " << slotsa[0] << endl;

	    NTL::Vec<Ctxt> eMaxVec, eMinVec;
	    resize(eMaxVec, bitSize, Ctxt(publicKey));
	 	resize(eMinVec, bitSize, Ctxt(publicKey));
	 	Ctxt ni(publicKey);
  	    CtPtrs_VecCt wMax(eMaxVec);
	 	CtPtrs_VecCt wMin(eMinVec);

	 	compareTwoNumbers(wMax, wMin, Result, ni,
	 			count1ENSum, count0ENSum,
	 			&unpackSlotEncoding);
};

int checkAllValues ( int target, vector<Ctxt>& eMapping, Ctxt& Result, MatrixClsEN& MatrixEN, FHESecKey& secretKey ) {

		const EncryptedArray& ea = *(secretKey.getContext().ea);
		const FHEPubKey& publicKey = secretKey;

		NTL::Vec<Ctxt> countVec1,countVec0,count1ENSumVec,count0ENSumVec;
	 	resize(countVec1, bitSize, Ctxt(publicKey));
	 	resize(countVec0, bitSize, Ctxt(publicKey));
	 	resize(count1ENSumVec, bitSize, Ctxt(publicKey));
	 	resize(count0ENSumVec, bitSize, Ctxt(publicKey));
	 	CtPtrs_VecCt count1EN(countVec1);
	 	CtPtrs_VecCt count0EN(countVec0);
	 	CtPtrs_VecCt count1ENSum(count1ENSumVec);
	 	CtPtrs_VecCt count0ENSum(count0ENSumVec);

	 	cout << " Check For -- " << target << endl;
	 	for ( int i =0; i < (MatrixEN.SizeX() -1 );i++) {
	 		if (target == 0) {
	 			MatrixEN.Count_0_1_FHE(i,count1EN, secretKey);
	 			MatrixEN.Count_0_0_FHE(i,count0EN, secretKey);
	 		} else {
	 		 	MatrixEN.Count_1_1_FHE(i,count1EN, secretKey);
	 		 	MatrixEN.Count_1_0_FHE(i,count0EN, secretKey);
	 		}


	 	 for ( int j = 0; j< bitSize; j++ ) {
	 		 countVec1[j].multiplyBy(eMapping[i]);
	 		 countVec0[j].multiplyBy(eMapping[i]);
	 		 if (i==0) {
	 			 count1ENSumVec[j] =  countVec1[j];
	 				count0ENSumVec[j] =  countVec0[j];
	 			}
	 		 else {
	 				count1ENSumVec[j].addCtxt(countVec1[j]);
	 				count0ENSumVec[j].addCtxt(countVec0[j]);
	 			}
	  		}

	 	}



	 	vector<long> slotsa;
	 	decryptBinaryNums(slotsa, count1ENSum, secretKey, ea);
	 	cout << "     Count of 1 is: ** " << slotsa[0] << endl;
	 	decryptBinaryNums(slotsa, count0ENSum, secretKey, ea);
	 	cout << "     Count of 0 is: ** " << slotsa[0] << endl;

	 	// after cout 0's and 1's
	 	// wheck whether all 0's and 1's


	    NTL::Vec<Ctxt> eMaxVec, eMinVec, eZeroCountVec;
	    resize(eMaxVec, bitSize, Ctxt(publicKey));
	    resize(eZeroCountVec, bitSize, Ctxt(publicKey));
	 	resize(eMinVec, bitSize, Ctxt(publicKey));
	 	Ctxt exitsAll(publicKey);
	 	Ctxt mu1(publicKey);
		Ctxt mu0(publicKey);
	 	Ctxt ni1(publicKey);
	 	Ctxt ni0(publicKey);
  	    CtPtrs_VecCt wMax(eMaxVec);
	 	CtPtrs_VecCt wMin(eMinVec);
	 	CtPtrs_VecCt eZeroCount(eZeroCountVec);

	 	for ( int i = 0; i < bitSize; i++) {
	 		secretKey.Encrypt(eZeroCountVec[0],ZZX(0));
	 	}

	 	// if mu1 or mu0 = zero, there is zero counts
	 	compareTwoNumbers(wMax, wMin, mu1, ni1,
	 			count1ENSum, eZeroCount,
	 			&unpackSlotEncoding);

	 	compareTwoNumbers(wMax, wMin, mu0, ni0,
		 			count0ENSum, eZeroCount,
		 			&unpackSlotEncoding);



	 	exitsAll = mu1;
	 	exitsAll.multiplyBy(mu0);
	 	exitsAll.addConstant(ZZX(1));

//	 	vector<long> slots;
//	 	ea.decrypt(exitsAll, secretKey, slots);
//	 	cout<< " *** check All " << ":  " << slots[0]<<endl;


	 	Result = mu1;

	 	int alls = checkGCBin (TcpPort,secretKey,exitsAll);
	 	cout << "$$$$$ Terminate branch test is " << alls << endl;
	 	return alls;
};



void compareEntropy (int level, vector<Ctxt>& eMapping,vector<Ctxt>& eMappingCum, MatrixClsEN& MatrixEN, FHESecKey& secretKey ) {


		const EncryptedArray& ea = *(secretKey.getContext().ea);
		const FHEPubKey& publicKey = secretKey;

		vector<CtPtrs_VecCt> eGains;
		vector<NTL::Vec<Ctxt>> eGainVecs(MatrixEN.SizeX()-1);

	  	for ( int i = 0; i <  MatrixEN.SizeX()-1 ; i ++) {

	  		cout << "Working on feature -- " << i << endl;
	  		cout << "<<<<" << float( clock () - begin_time ) /  CLOCKS_PER_SEC  << endl;;

	 		NTL::Vec<Ctxt> countVec1,countVec0,countVec1_1,countVec1_0,countVec0_1,countVec0_0;
	 		resize(countVec1, bitSize, Ctxt(publicKey));
	 		resize(countVec0, bitSize, Ctxt(publicKey));
	 		resize(countVec1_1, bitSize, Ctxt(publicKey));
	 		resize(countVec1_0, bitSize, Ctxt(publicKey));
	 		resize(countVec0_1, bitSize, Ctxt(publicKey));
	 		resize(countVec0_0, bitSize, Ctxt(publicKey));
	 		CtPtrs_VecCt count1EN(countVec1);
	 		CtPtrs_VecCt count0EN(countVec0);
	 		CtPtrs_VecCt count1_1EN(countVec1_1);
	 		CtPtrs_VecCt count1_0EN(countVec1_0);
	 		CtPtrs_VecCt count0_1EN(countVec0_1);
	 		CtPtrs_VecCt count0_0EN(countVec0_0);

	 		//Display the couting resultentropy
	 		vector<long> slotsa;

	 		MatrixEN.Count_1_FHE(i,count1EN, secretKey);
	 		decryptBinaryNums(slotsa, count1EN, secretKey, ea);
	 		cout << "   Count of 1 is: ** " << slotsa[0] << endl;

	 		MatrixEN.Count_0_FHE (i, count0EN,secretKey);
	 		decryptBinaryNums(slotsa, count0EN, secretKey, ea);
	 		cout << "   Count of 0 is: ** " << slotsa[0] << endl;

	 		MatrixEN.Count_1_1_FHE (i, count1_1EN, secretKey);
	 		decryptBinaryNums(slotsa, count1_1EN, secretKey, ea);
	 		cout << "   Count of 1-1 is: ** " << slotsa[0] << endl;

	 		MatrixEN.Count_1_0_FHE (i, count1_0EN,secretKey);
	 		decryptBinaryNums(slotsa, count1_0EN, secretKey, ea);
	 		cout << "   Count of 1-0 is: ** " << slotsa[0] << endl;

	 		MatrixEN.Count_0_1_FHE (i, count0_1EN, secretKey);
	 		decryptBinaryNums(slotsa, count0_1EN, secretKey, ea);
	 	 	cout << "   Count of 0-1 is: ** " << slotsa[0] << endl;

	 		MatrixEN.Count_0_0_FHE (i, count0_0EN,secretKey);
	 	 	decryptBinaryNums(slotsa, count0_0EN, secretKey, ea);
	 	 	cout << "   Count of 0-0 is: ** " << slotsa[0] << endl;

	 		cout << "<<<<" << float( clock () - begin_time ) /  CLOCKS_PER_SEC  << endl;;
 	 		cout << " (6)Counted" << endl;

	 		 vector<long> slots;
	 		 long n=2;
	 		 long d = ea.getDegree(); // size of each slot

	 		 std::vector<zzX> unpackSlotEncoding;
	 		 buildUnpackSlotEncoding(unpackSlotEncoding, ea);

	 		 NTL::Vec<Ctxt> eResult1,eResult0;
	 		 resize(eResult1, bitSize, Ctxt(publicKey));
	 		 resize(eResult0, bitSize, Ctxt(publicKey));

	 		 // start of a small table inquiry if the matrix is not so big

	 		 if ( DIRECTMAP == 1 ) {
				 std::vector<Ctxt> E1(n, Ctxt(publicKey)),E0(n, Ctxt(publicKey));

				 NTL::Vec<Ctxt> count1_1Map=count1_1EN.v;
				 NTL::Vec<Ctxt> count1_0Map=count1_0EN.v;
				 NTL::Vec<Ctxt> count0_1Map=count0_1EN.v;
				 NTL::Vec<Ctxt> count0_0Map=count0_0EN.v;

				 NTL::Vec<Ctxt> entropy1_Map;
				 NTL::Vec<Ctxt> entropy0_Map;
				 resize(entropy1_Map, 14, Ctxt(publicKey));
				 resize(entropy0_Map, 14, Ctxt(publicKey));


				  for ( int j = 0; j< matrixLookupBits ; j++ ) {             // change to 5 for 32*32 table lookup
					 entropy1_Map[j+ matrixLookupBits] =  count1_0Map[j + mapScale];
					 entropy0_Map[j+ matrixLookupBits] =  count0_0Map[j + mapScale];
					 entropy1_Map[j] =  count1_1Map[j + mapScale];
					 entropy0_Map[j] =  count0_1Map[j + mapScale];
					  }

				  CtPtrs_VecCt entropy1(entropy1_Map);
				  CtPtrs_VecCt entropy0(entropy0_Map);


				  decryptBinaryNums(slots, entropy1, secretKey, ea);
				  cout<< "   table lookup map 1 " << slots[0] <<endl;

				  tableLookup(E1[0], T0, entropy1 ,&unpackSlotEncoding );
				  tableLookup(E0[0], T0, entropy0 ,&unpackSlotEncoding );

				  cout << "<<<<" << float( clock () - begin_time ) /  CLOCKS_PER_SEC  << endl;;
				  cout << " (2) Lookup done" << endl;

				  NewPlaintextArray PA1(ea);
				  vector<ZZX> arrayZZX (ea.size());
				  encode(ea,PA1,arrayZZX);
				  ea.encrypt(E1[1],publicKey,PA1);
				  ea.encrypt(E0[1],publicKey,PA1);


				  // Unpack them to Binary encoding
				 vector<Ctxt> entropy1xtmp(d*n -1, Ctxt(publicKey));
				 vector<Ctxt> entropy0xtmp(d*n -1, Ctxt(publicKey));
				 unpack(CtPtrs_vectorCt(entropy1xtmp), CtPtrs_vectorCt(E1), ea, unpackSlotEncoding);
				 unpack(CtPtrs_vectorCt(entropy0xtmp), CtPtrs_vectorCt(E0), ea, unpackSlotEncoding);



				 for ( long j = 0; j < lsize(eResult1);j++) {
						eResult1[j] = entropy1xtmp[j];
						eResult0[j] = entropy0xtmp[j];
				 }

	 		 }
	 		 // End of a small table inquiry if the matrix is not so big



	 		 // for bigger matrix , call the EntropyCalEnc to calculate them

	 		 if ( DIRECTMAP == 0 ) {
	 			 EntropyCalEnc (  eResult1,countVec1_1, countVec1_0,secretKey );
	 			 EntropyCalEnc (  eResult0,countVec0_1, countVec0_0,secretKey );
	 		 }

	 		 //	 end of bigger matrix , call the EntropyCalEnc to calculate them



	 		 CtPtrs_VecCt entropy1x(eResult1);
	 		 CtPtrs_VecCt entropy0x(eResult0);

	 		 decryptBinaryNums(slots, entropy1x, secretKey, ea);
	     	 cout<< "   entropy 1-x ** " << slots[0] <<endl;
	      	 decryptBinaryNums(slots, entropy0x, secretKey, ea);
	     	 cout<< "   entropy 0-x ** " << slots[0] <<endl;

	     	cout << "<<<<" << float( clock () - begin_time ) /  CLOCKS_PER_SEC  << endl;;
	 		cout << "  entropy done" << endl;

	 	  	resize(eGainVecs[i], bitSize, Ctxt(publicKey));
	 	    CtPtrs_VecCt eGain(eGainVecs[i]);

	 	    NTL::Vec<Ctxt> eGain0Vec,eGain1Vec,eGainTempVec;
	     	resize(eGain0Vec, 20, Ctxt(publicKey));
	     	resize(eGain1Vec, 20, Ctxt(publicKey));
	     	resize(eGainTempVec, 20, Ctxt(publicKey));

	     	CtPtrs_VecCt eGain0(eGain0Vec);
	     	CtPtrs_VecCt eGain1(eGain1Vec);
	     	CtPtrs_VecCt eGainTemp(eGainTempVec);


	       	multTwoNumbers(eGain1,entropy1x,count1EN,false,
	         		                 20, &unpackSlotEncoding);

	        decryptBinaryNums(slots, eGain1, secretKey, ea);
	        cout<< "   Conditional entropy eGain1 - ** " << slots[0] <<endl;

	      	multTwoNumbers(eGain0,entropy0x,count0EN,false,
	     		                 20, &unpackSlotEncoding);

	      	decryptBinaryNums(slots, eGain0, secretKey, ea);
	      	cout<< "   Conditional entropy eGain0 - ** " << slots[0] <<endl;

	        addTwoNumbers(eGainTemp,eGain1,eGain0,
	      	        			20, &unpackSlotEncoding);

			decryptBinaryNums(slots, eGainTemp, secretKey, ea);
			cout<< "   Conditional entropy eGainsum  - ** " << slots[0] <<endl;

	        for (int j = 0; j< bitSize; j++){  // devided by 2^scale
	        	eGainVecs[i][j] = eGainTempVec[j+scale];
	        	eGainVecs[i][j] = eGainTempVec[j+scale];
	    	}


	 		 decryptBinaryNums(slots, eGain, secretKey, ea);
	     	 cout<< "   Conditional entropy - ** " << slots[0] <<endl;


	        //void compareTwoNumbers(CtPtrs& max, CtPtrs& min, Ctxt& mu, Ctxt& ni,
	         //                      const CtPtrs& a, const CtPtrs& b,
	         //                      std::vector<zzX>* unpackSlotEncoding=nullptr);

	     	cout << "<<<<" << float( clock () - begin_time ) /  CLOCKS_PER_SEC  << endl;;
	        cout << " Calculation Done" << endl;
	        eGains.push_back(eGain);


	   	} // for loop

	  	vector<long> slots;
	    for (int i =0; i < eGains.size();i++ ) {
	    	decryptBinaryNums(slots, eGains[i], secretKey, ea);
	    	cout<< "Gain - " << i << ":"<< slots[0] <<endl;
	    }

	    // Get Smallest entropy ( biggest entropy gain)

	    NTL::Vec<Ctxt> eMaxVec, eMinVec,eSmaller;
	    resize(eMaxVec, bitSize, Ctxt(publicKey));
	    resize(eMinVec, bitSize, Ctxt(publicKey));
	    resize(eSmaller, bitSize, Ctxt(publicKey));

	    Ctxt mu(publicKey), ni(publicKey);

	    NTL::Vec<Ctxt> eMappingTemp;
	    resize(eMappingTemp, eGains.size()+1, Ctxt(publicKey));
	  //  vector<Ctxt> eMapping(eGains.size(), $$$$Ctxt(publicKey));

	    CtPtrs_VecCt wMax(eMaxVec);
	    CtPtrs_VecCt wMin(eMinVec);

	    secretKey.Encrypt(eMappingTemp[0], ZZX(0));

	    // check if the feature should be excluded by change to FFFF
	    NTL::Vec<Ctxt> eFFFF;
		resize(eFFFF, bitSize, Ctxt(publicKey));
		for (int i=0; i < bitSize ;i ++) {
			secretKey.Encrypt(eFFFF[i], ZZX(1));
			}

	    for (int i=0; i < eGains.size();i ++) {

	    	// set data to FFFF if already beem compared before compare
	    	NTL::Vec<Ctxt> eChecked,eTemp1Vec,eTemp2Vec,eTemp3Vec;
	    	resize(eChecked, bitSize, Ctxt(publicKey));
	    	resize(eTemp1Vec, bitSize, Ctxt(publicKey));
	    	resize(eTemp2Vec, bitSize, Ctxt(publicKey));
	    	resize(eTemp3Vec, bitSize, Ctxt(publicKey));
	    	CtPtrs_VecCt eTemp1(eTemp1Vec);
	    	CtPtrs_VecCt eTemp2(eTemp2Vec);
	    	CtPtrs_VecCt eTemp3(eTemp3Vec);

	    	vecCopy(eTemp1Vec,eFFFF );
	    	eChecked[0] = eMappingCum[i];
	//    	multTwoNumbers(eTemp1,CtPtrs_VecCt(eChecked),CtPtrs_VecCt(eFFFF),false, bitSize, &unpackSlotEncoding);
	    	for ( int j=0; j < bitSize; j++ ) {
	    		eTemp1Vec[j].multiplyBy(eChecked[0]);
	    	}

	    	eChecked[0].addConstant(ZZX(1));
	    	vecCopy(eTemp2Vec,eGainVecs[i]);
	//    	multTwoNumbers(eTemp2,CtPtrs_VecCt(eChecked),CtPtrs_VecCt(eGainVecs[i]),false,bitSize, &unpackSlotEncoding);
	    	for ( int j=0; j < bitSize; j++ ) {
	    		eTemp2Vec[j].multiplyBy(eChecked[0]);
	    	}

	//    	addTwoNumbers(eTemp3,eTemp1,eTemp2,	bitSize, &unpackSlotEncoding);
	    	vecCopy(eTemp3Vec,eTemp2Vec);
	    	for ( int j=0; j < bitSize; j++ ) {
	    		eTemp3Vec[j].addCtxt(eTemp1Vec[j]);
	    	}

			vector<long> slots;
			decryptBinaryNums(slots, eTemp1, secretKey, ea);
			cout<< "== CumIndex  " << i << ":  " << slots[0]<<endl;
			decryptBinaryNums(slots, eTemp2, secretKey, ea);
			cout<< "== cal   " << i << ":  " << slots[0]<<endl;
			decryptBinaryNums(slots, eTemp3, secretKey, ea);
			cout<< "== total  " << i << ":  " << slots[0]<<endl;

			vecCopy(eGainVecs[i],eTemp3Vec);

	    	//compare
	    	if ( i == 0 ) vecCopy(eSmaller,eTemp3Vec);
	    	else {
	    		compareTwoNumbers(wMax, wMin, mu, ni,
	    			CtPtrs_VecCt(eSmaller), eTemp3,
					&unpackSlotEncoding);
	    		vecCopy(eSmaller,eMinVec);
	    		}
	    }

	    decryptBinaryNums(slots, CtPtrs_VecCt(eSmaller), secretKey, ea);
	    cout<< "== Smaller :  " << slots[0]<<endl;
		cout << "<<<<" << float( clock () - begin_time ) /  CLOCKS_PER_SEC  << endl;;

		for (int i=0; i < eGains.size();i ++) {
//			vector<long> slots;
			compareTwoNumbers(wMax, wMin, mu, ni,
	    			CtPtrs_VecCt(eSmaller), CtPtrs_VecCt(eGainVecs[i]),
	    			&unpackSlotEncoding);
//			ea.decrypt(eMappingTemp[i], secretKey, slots);
//			cout << "#   debug array " << i << " eMappingTemp " << slots[0] << endl;
	    	mu = eMappingTemp[i];
	    	mu.addConstant(ZZX(1));
	    	ni.multiplyBy(mu) ;
	    	ni.addConstant(ZZX(1));

	    	eMappingTemp[i+1]=ni;

//			ea.decrypt(ni, secretKey, slots);
//			cout << "#   debug array " << i << " new ni " << slots[0] << endl;

			eMapping[i] = ni;
	    	eMapping[i].addCtxt(eMappingTemp[i]);

//	   	    ea.decrypt(eMapping[i], secretKey, slots);
//	    	cout << "#   debug array" << i << " final " << slots[0] << endl;

	    	if (i==0)  	cout << "#   Noise before repack " << eMapping[i].getNoiseVar() << endl;
	    	rePackBin(TcpPort,secretKey, eMapping[i]);
	    	rePackBin(TcpPort,secretKey, eMappingTemp[i+1]);
 	       	if (i==0)  	cout << "#   Noise after repack " << eMapping[i].getNoiseVar() << endl;


	    }
		cout << "<<<<" << float( clock () - begin_time ) /  CLOCKS_PER_SEC  << endl;;

}  // end of  compareEntropy


class eTree
{
public:
	vector<Ctxt> eMapping;
	vector<Ctxt> eMappingCum;
	vector<Ctxt> Decision;
	vector < eTree * > Children;
	int Features;
	int Level;
	eTree(int level,int Features,vector<Ctxt>& eMappingCumIn, FHESecKey& secretKey ) {
		this-> Features=Features;
		this-> Level=level ;
			for ( int i = 0; i < Features; i++ ) {
			eMapping.push_back(Ctxt(secretKey));
			eMappingCum.push_back(Ctxt(secretKey));
			eMappingCum[i]=eMappingCumIn[i];
			}
	};

	~eTree(){ };

	void BuildeTree(MatrixClsEN& Remain_MatrixEN, FHESecKey& secretKey);
	void PrinteTree(int level, FHESecKey& secretKey);
  };

void eTree::BuildeTree(MatrixClsEN& Remain_MatrixEN,FHESecKey& secretKey) {

	const EncryptedArray& ea = *(secretKey.getContext().ea);

	cout << "FHE Binary Tree Level " << Level  <<" - start" << endl;

	// Remain_MatrixEN.Display(secretKey);

	if ( Level <  (Features - 1)  ) {
		compareEntropy (Level, eMapping,eMappingCum, Remain_MatrixEN, secretKey ) ;

	}
	else  {
		// at the most detailed level
		// neg the eMappingCum to left the last column only
		for (int i=0; i < Remain_MatrixEN.SizeX()-1;i ++) {
					eMapping[i] = eMappingCum[i];
					eMapping[i].addConstant(ZZX(1));
					}
		Ctxt Result(secretKey);
		compareCounts (0,eMapping,Result, Remain_MatrixEN, secretKey );
		Decision.push_back(Result);
		compareCounts (1,eMapping,Result, Remain_MatrixEN, secretKey );
		Decision.push_back(Result);
		vector<long> slots;
		ea.decrypt(Decision[0], secretKey, slots);
		cout<< "The Decision 0 is : ** " << slots[0]<< endl;
		ea.decrypt(Decision[1], secretKey, slots);
		cout<< "The Decision 1 is : ** " << slots[0]<< endl;
	}

	for (int i=0; i < Remain_MatrixEN.SizeX()-1;i ++) {
	    	 vector<long> slots;
	    	 ea.decrypt(eMapping[i], secretKey, slots);
	    	 cout<< "The array index is  " << i << ":  " << slots[0]<<endl;
	}


	cout << "FHE Binary Tree Level " << Level  <<" - end " << endl;

	if ( Level <  (Features - 1) ) {

		for (int i=0; i < Features;i++) {
			eMappingCum[i].addCtxt(eMapping[i]);
		}
		MatrixClsEN MatrixENNew0( Remain_MatrixEN,eMapping,1,secretKey);

		Ctxt allresult0(secretKey);
		int checkall0 = checkAllValues ( 0, eMapping, allresult0, Remain_MatrixEN,  secretKey );

		if ( checkall0 == 1 ) {
			Decision.push_back(allresult0);
			Children.push_back(NULL);
		}
		else {
				eTree * child0 =new eTree(Level+1,Features,eMappingCum,secretKey);
				Decision.push_back(Ctxt(secretKey));
				Children.push_back(child0);
				child0->BuildeTree(MatrixENNew0,secretKey);
		}

		MatrixClsEN MatrixENNew1( Remain_MatrixEN,eMapping,0,secretKey);
		Ctxt allresult1(secretKey);
		int checkall1 = checkAllValues ( 1, eMapping, allresult1, Remain_MatrixEN,  secretKey );


		if ( checkall1 == 1 ) {
			Decision.push_back(allresult1);
			Children.push_back(NULL);
		}
		else {
			eTree * child1 =new eTree(Level+1,Features,eMappingCum,secretKey);
			Decision.push_back(Ctxt(secretKey));
			Children.push_back(child1);
			child1->BuildeTree(MatrixENNew1,secretKey);
		}
	}

	cout << "FHE Binary Tree Level " << Level  <<" - end with children " << Children.size() << endl;

}

void eTree::PrinteTree(int level, FHESecKey& secretKey) {
	const EncryptedArray& ea = *(secretKey.getContext().ea);
 	for (int i = 1; i <= level; i++  ) cout << "     ";
	for (int i = 0; i < Features; i++  ) {
		vector<long> slots;
		ea.decrypt(eMapping[i], secretKey, slots);
		cout<< slots[0];
	};
	if (level ==(Features -1) ) {
		cout<< " 0 --> " ;
		vector<long> slots;
		ea.decrypt(Decision[0], secretKey, slots);
		cout<< slots[0];
		cout<< "| 1 --> " ;
		ea.decrypt(Decision[1], secretKey, slots);
		cout<< slots[0];
	}
	cout << endl;
	if (level < (Features - 1) ) {

		for (int i = 1; i <= level; i++  ) cout << "     ";
		cout << " =0= \n" ;
		if ( Children[0] )
			Children[0]->PrinteTree(level+1, secretKey);
		else {
			for (int i = 1; i <= level; i++  ) cout << "     ";
			vector<long> slots;
			ea.decrypt(Decision[0], secretKey, slots);
			cout<< " --> " ;
			cout<< slots[0]<<endl;
		}

		for (int i = 1; i <= level; i++  ) cout << "     ";
		cout << " =1= \n" ;
		if ( Children[1] )
			Children[1]->PrinteTree(level+1, secretKey);
		else {
			for (int i = 1; i <= level; i++  ) cout << "     ";
			vector<long> slots;
			ea.decrypt(Decision[1], secretKey, slots);
			cout<< " --> " ;
			cout<< slots[0]<<endl;
		}
	}

}

Ctxt TesteTree(eTree * etree, int level, vector < Ctxt > Attributes , FHESecKey& secretKey){
	const EncryptedArray& ea = *(secretKey.getContext().ea);
	Ctxt levelMapping(secretKey);
	Ctxt levelMappingTmp(secretKey);
	Ctxt levelValue(secretKey);
	Ctxt levelValue0(secretKey);
	Ctxt levelValue1(secretKey);


	// mapping the attribute to the sequence of the decision tree
	for (int i=0; i < Attributes.size();i++) {
		levelMappingTmp = etree->eMapping[i];
		levelMappingTmp.multiplyBy(Attributes[i]);
		if ( i == 0 ) {
			levelMapping = levelMappingTmp;
		}
		else {
			levelMapping.addCtxt(levelMappingTmp);
		}
	}

//	vector<long> slots;
// 	ea.decrypt(levelMapping, secretKey, slots);
//	cout<< "Level "<< level <<" attribute mapping is **" <<  slots[0]<<endl;

//	if (level ==  (Attributes.size() -1)) {
//		ea.decrypt(etree->Decision[0], secretKey, slots);
//		cout<< "   Level "<< level <<" decision 0 **" <<  slots[0]<<endl;
//		ea.decrypt(etree->Decision[1], secretKey, slots);
//		cout<< "   Level "<< level <<" decision 1 **" <<  slots[0]<<endl;
//	}
	levelValue0 = levelMapping;
	levelValue0.addConstant(ZZX(1));
	if ((level < (Attributes.size() -1)) && (etree->Children[0]))
		levelValue0.multiplyBy(TesteTree(etree->Children[0],level+1,Attributes,secretKey));
	else
		levelValue0.multiplyBy(etree->Decision[0]);

//	ea.decrypt(levelValue0, secretKey, slots);
//	cout<< "	levelValue0 "<<" value  is **" <<  slots[0]<<endl;

	levelValue1 = levelMapping;
	if ((level < (Attributes.size() -1)) && (etree->Children[1]))
		levelValue1.multiplyBy(TesteTree(etree->Children[1],level+1,Attributes,secretKey));
	else
		levelValue1.multiplyBy(etree->Decision[1]);

	levelValue = levelValue0;
	levelValue.addCtxt(levelValue1);

//	ea.decrypt(levelValue1, secretKey, slots);
//	cout<< "	levelValue1 "<<" value  is **" <<  slots[0]<<endl;

//	ea.decrypt(levelValue, secretKey, slots);
//	cout<< "Level "<< level <<" attribute value  is **" <<  slots[0]<<endl;

	return levelValue;
}



void Build_ID3_FHE (FHESecKey& secretKey){

	cout << "FHE Binary Tree - start:" << endl;

	const EncryptedArray& ea = *(secretKey.getContext().ea);
	const FHEPubKey& publicKey = secretKey;

//	buildLookupTableBin(T0, [](double x){ return EntropyMapping(x)*32 ;},
//			                   10,  /*scale_in=*/0, /*sign_in=*/0,
//			                   /*nbits_out*/ 10, /*scale_out=*/0, /*sign_out=*/0,
//			                   ea);

	MatrixClsEN MatrixEN("Train.dat",secretKey);

	scale = log(MatrixEN.SizeY())/log(2.0) + 1;
	cout << " scale " << scale << endl;
 	if ( scale > 7 ) matrixLookupBits = 7;
 		else matrixLookupBits = scale;
 	cout << " mapping scale " << matrixLookupBits << endl;
	if ( scale <=matrixLookupBits )  mapScale = 0;
	else mapScale = scale -matrixLookupBits;
 	cout << " table lookup map scale " << mapScale << endl;


	buildLookupTableBin(T0, [](double x){ return EntropyMapping(x)*512 ;},	// 9 bits output
			                   2*matrixLookupBits,  /*scale_in=*/0, /*sign_in=*/0,           // size = 14 for 128*128 ,matrix
			                   /*nbits_out*/ 10, /*scale_out=*/0, /*sign_out=*/0,
			                   ea);


	cout << "Map Entropy Lookup table size:"<<lsize(T0)<<"\n";


    buildLookupTableBin(T1, [](double x){ return LogMapping(x)  ;},
			                   10,  /*scale_in=*/0, /*sign_in=*/0,
			                   /*nbits_out*/ 10, /*scale_out=*/0, /*sign_out=*/0,
			                   ea);

    cout << "Log Lookup table size:"<<lsize(T1)<<"\n";

    buildLookupTableBin(T2, [](double x){ return InverseMapping(x) ;},
			                   10,  /*scale_in=*/0, /*sign_in=*/0,
			                   /*nbits_out*/ 10, /*scale_out=*/0, /*sign_out=*/0,
			                   ea);




	// MatrixEN.Display(secretKey);

	vector<Ctxt> eMappingCum(MatrixEN.SizeX()-1, Ctxt(publicKey));
	for ( int i; i < eMappingCum.size();i++ )
		secretKey.Encrypt(eMappingCum[i], ZZX(0));


	cout << "<<<<" << float( clock () - begin_time ) /  CLOCKS_PER_SEC  << endl;;

	eTree * root =new eTree(0,MatrixEN.SizeX()-1,eMappingCum,secretKey);



 	root->BuildeTree(MatrixEN,secretKey);

 	cout<< "**** Printing the tree  " <<endl;

 	root->PrinteTree(0,secretKey);

 	cout << "<<<<" << float( clock () - begin_time ) /  CLOCKS_PER_SEC  << endl;;

 	cout<< "**** Printing the tree -- finished  " <<endl <<endl;

 	cout << "Training data validation: \n";

 	validateETree("Train.dat", MatrixEN.SizeX()-1 , root, secretKey);
 	cout << "<<<<" << float( clock () - begin_time ) /  CLOCKS_PER_SEC  << endl;;

//	cout << "Training data validation: \n";
//	validateETree("Test.dat", MatrixEN.SizeX()-1 , root, secretKey);
//	cout << "<<<<" << float( clock () - begin_time ) /  CLOCKS_PER_SEC  << endl;;

 	cout << "All done! \n";

 	delete root;

}


const char * endCode="end!";
const char * checkGCBinCode="checkGCBin";
const char * OKCode="OK";
const char * sendCode="Send";
const char * echoCode="Echo";
const char * repackCode = "rePack";

void error(const char *msg)
{
    perror(msg);
    exit(0);
}
int secureRead(char party,int sockfd, char* buffer, int maxSize) {
	 char * SizeText = new char[100];
	 read(sockfd,SizeText,100);
	 stringstream strValue;
	 strValue << SizeText;
	 int Size;
	 strValue >> Size;

//	 cout << party<<"-@@text size to be received " << Size << endl;

	 int n;
	 do {
		 	 std::this_thread::sleep_for(std::chrono::milliseconds(120));
		 	 bzero(buffer,maxSize);
		 	 n = read(sockfd,buffer,maxSize);
//			 cout << party<< "-@@text received " << n << endl;
			 if ( n != Size ) {
				 write(sockfd,sendCode,strlen(sendCode));
//				 cout << party<< "-@@resend request send " << sendCode << endl;
			 }
 	 } while (n != Size);
//	 cout << party<<"-@@text receive confirmed " << n << endl;
	 write(sockfd,OKCode,strlen(OKCode));

	 return n;
}

int secureWrite(char party,int sockfd,const char* buffer,int Size){
	 string s = to_string(Size);
	 const char * sizeText = s.c_str();
	 write(sockfd,sizeText,strlen(sizeText));
//	 cout << party<<"-@@text size to be send " << sizeText << endl;

	 int n;
	 char * readCode = new char[100];
	 do {
		 n = write(sockfd,buffer,Size);
//		 cout << party<<"-@@text send " << n << endl;
		 do {
			 bzero(readCode,100);
			 n = read(sockfd,readCode,100);
//			 cout << party<<"-@@feedback received " << n << endl;
			 } while ( strcmp(readCode,OKCode) && strcmp(readCode,sendCode) );
	 } while(strcmp(readCode,OKCode));
//	 cout << party<<"-@@text write confirmed " << n << endl;
  	 return n;
}


int launchServer (int portno,FHESecKey& secretKey)
{
	 const EncryptedArray& ea = *(secretKey.getContext().ea);

	 cout << "++++ Server launched \n";

	 int sockfd, newsockfd;
     socklen_t clilen;
     char buffer[MaxBufferSize];
     struct sockaddr_in serv_addr, cli_addr;
     int n;
     sockfd = socket(AF_INET, SOCK_STREAM, 0);
     if (sockfd < 0)
        error("ERROR opening socket");
     bzero((char *) &serv_addr, sizeof(serv_addr));
     serv_addr.sin_family = AF_INET;
     serv_addr.sin_addr.s_addr = INADDR_ANY;
     serv_addr.sin_port = htons(portno);
     if (bind(sockfd, (struct sockaddr *) &serv_addr,
              sizeof(serv_addr)) < 0)
              error("ERROR on binding");
     listen(sockfd,5);
     clilen = sizeof(cli_addr);


     bool  messageEnd= false;
     while (! messageEnd ) {


       	 newsockfd = accept(sockfd,
        	                 (struct sockaddr *) &cli_addr,
        	                 &clilen);
         if (newsockfd < 0)
                 error("ERROR on accept");

//         cout << "++++ Server connection Opened\n";

    	 bzero(buffer,MaxBufferSize);
		 n = read(newsockfd,buffer,MaxBufferSize);
		 if (n < 0) error("ERROR reading from socket");

		 // if code is "checkGCBin"


		 if (!strcmp(buffer,echoCode)) {
			 // do nothing
			 cout << " -- page server -- \n";
		 }

		 if (!strcmp(buffer,repackCode)) {

//			 cout << " -- RePack -- \n";

			 write(newsockfd,OKCode,strlen(OKCode));

			 bzero(buffer,MaxBufferSize);
			 n = secureRead('S',newsockfd,buffer,MaxBufferSize);
			 if (n < 0) error("ERROR Reading from socket");
//			 cout << " received  text " << strlen(buffer) << endl;
			 Ctxt eBit(secretKey);
			 istringstream CtxtStreamIn(buffer);
			 CtxtStreamIn >> eBit;
			 vector <long> SLot;
			 ea.decrypt(eBit, secretKey, SLot);
			 secretKey.Encrypt(eBit, ZZX(SLot[0]&1));
//  		     cout << "$$$$  repack received data " << SLot[0] << endl;

			 ostringstream CtxtStreamOut;
			 CtxtStreamOut << eBit;
			 std::string strCtxt =  CtxtStreamOut.str();
			 const char* chr = strCtxt.c_str();
//			 cout << " feedback  length " << strlen(chr) << endl;
			 n = secureWrite('S',newsockfd,chr,strlen(chr));
			 if (n < 0) error("ERROR writing to socket");


		 }


		 if (!strcmp(buffer,checkGCBinCode)) {

//			 cout << " -- checkGCBinCode -- \n";
			 write(newsockfd,OKCode,strlen(OKCode));

			 int decodedResult = 0;
			 Ctxt eBit(secretKey);
			 for ( int i =0; i < bitSize; i++) {

				 bzero(buffer,MaxBufferSize);
				 n = secureRead('S', newsockfd,buffer,MaxBufferSize);
				 if (n < 0) error("ERROR reading from socket");
//				 cout << " read " << i << " , length " << strlen(buffer) << endl;

				 istringstream CtxtStreamIn(buffer);
				 CtxtStreamIn >> eBit;
				 vector <long> SLot;
				 ea.decrypt(eBit, secretKey, SLot);
//				 cout << "Server Decrypted bit " << i <<": " << SLot[0] << endl;
				 decodedResult += SLot[0]*pow(2,i);
			 } // For each bit

//			 cout << "Server Decrypted Data " << decodedResult << endl;
			 string s = to_string(decodedResult);
			 const char * resultText = s.c_str();
			 n = write(newsockfd,resultText,strlen(resultText));
			 if (n < 0) error("ERROR writing to socket");

 		 }  // checkGCBinCode


		 /*

		 char text[] = "Reply Message";
		 string s = to_string(globalVariable);
		 char * newArray = new char[strlen(text)+strlen(s.c_str())+1];
		 strcpy(newArray,text);
		 strcat(newArray,s.c_str());
		 */

		 /*
		 Ctxt bitTest1(secretKey);
	     istringstream CtxtStreamIn(buffer);
	     CtxtStreamIn >> bitTest1;

		 vector <long> bitTestSLot;
		 ea.decrypt(bitTest1, secretKey, bitTestSLot);
		 cout << "Server Decrypted data: " << bitTestSLot[0] << endl;

	     bitTest1.addConstant(ZZX(1));
		 ostringstream CtxtStreamOut;
		 CtxtStreamOut << bitTest1;
		 std::string strCtxt =  CtxtStreamOut.str();
		 const char* chr = strCtxt.c_str();

		 n = write(newsockfd,chr,strlen(chr));
		 if (n < 0) error("ERROR writing to socket");

		 */

		 if (!strcmp(buffer,endCode)) {
			 cout << "++++ Stop request received\n";
			 messageEnd = true;
		 }
 //		 cout << "++++ Server connection closed\n";

		 close(newsockfd);


  	  }  // while



      close(sockfd);

     cout << "++++ Server Stopped\n";

     return 0;


}

int rePackBin (int portno, FHESecKey& secretKey, Ctxt& input ){

	const EncryptedArray& ea = *(secretKey.getContext().ea);

	int sockfd, n;
	struct sockaddr_in serv_addr;
	struct hostent *server;

	char buffer[MaxBufferSize];

	sockfd = socket(AF_INET, SOCK_STREAM, 0);
	if (sockfd < 0)
		error("ERROR opening socket");
		server = gethostbyname(ServerAddress);
	if (server == NULL) {
	        fprintf(stderr,"ERROR, no such host\n");
	        exit(0);
	    }

	bzero((char *) &serv_addr, sizeof(serv_addr));
	serv_addr.sin_family = AF_INET;
	bcopy((char *)server->h_addr,
			(char *)&serv_addr.sin_addr.s_addr,
			server->h_length);
	serv_addr.sin_port = htons(portno);

	if (connect(sockfd,(struct sockaddr *) &serv_addr,sizeof(serv_addr)) < 0)
		error("ERROR connecting");

//	cout << "Encrypted Data repack \n ";

	n = write(sockfd,repackCode,strlen(repackCode));
	if (n < 0) error("ERROR writing to socket");


	do {
		bzero(buffer,100);
		n = read(sockfd,buffer,100) ;
	}  while (n==0);

	if (n < 0) error("ERROR writing to socket");
//	else cout <<"Server is ready!! " << buffer << endl;

	ostringstream CtxtStreamOut;
	CtxtStreamOut << input;
	std::string strCtxt =  CtxtStreamOut.str();
	const char* chr = strCtxt.c_str();
	n = secureWrite('C',sockfd,chr,strlen(chr));
	if (n < 0) error("ERROR writing to socket");

	bzero(buffer,MaxBufferSize);
	n = secureRead('C',sockfd,buffer,MaxBufferSize);
	istringstream CtxtStreamIn(buffer);
//	cout << " Received from server "<< strlen(buffer) << endl;
 	CtxtStreamIn >> input;

	vector <long> SLot;
	ea.decrypt(input, secretKey, SLot);
//	cout << "$$$$  repack send back data " << SLot[0] << endl;

   	close(sockfd);
	return 0;
}

int checkGCBin (int portno ,FHESecKey& secretKey, Ctxt input )
{

	const EncryptedArray& ea = *(secretKey.getContext().ea);

    int sockfd, n;
    struct sockaddr_in serv_addr;
    struct hostent *server;

    char buffer[MaxBufferSize];

    sockfd = socket(AF_INET, SOCK_STREAM, 0);
    if (sockfd < 0)
        error("ERROR opening socket");
    server = gethostbyname(ServerAddress);
    if (server == NULL) {
        fprintf(stderr,"ERROR, no such host\n");
        exit(0);
    }

    bzero((char *) &serv_addr, sizeof(serv_addr));
    serv_addr.sin_family = AF_INET;
    bcopy((char *)server->h_addr,
         (char *)&serv_addr.sin_addr.s_addr,
         server->h_length);
    serv_addr.sin_port = htons(portno);

    if (connect(sockfd,(struct sockaddr *) &serv_addr,sizeof(serv_addr)) < 0)
        error("ERROR connecting");

//   cout << "Garbled Circuit Binary check connected \n ";

    const char * checkGCBinCode = "checkGCBin";

    n = write(sockfd,checkGCBinCode,strlen(checkGCBinCode));
    if (n < 0) error("ERROR writing to socket");

//    cout << "checkGCBin sent \n ";


	do {
		bzero(buffer,100);
		n = read(sockfd,buffer,100) ;
	}  while (n==0);

	if (n < 0) error("ERROR writing to socket");
//	else cout <<"Server is ready!! " << buffer << endl;


  	long mask = RandomBits_long(bitSize);
//   cout << "Random mask:" << mask << endl;

    NTL::Vec<Ctxt> eData ;
    resize(eData, bitSize, Ctxt(secretKey));
    for (long i=0; i<bitSize; i++) {
    	secretKey.Encrypt(eData[i], ZZX((mask>>i)&1));
    }
    eData[0].addCtxt(input);


    for (long i=0; i<bitSize; i++) {
    	ostringstream CtxtStreamOut;
    	CtxtStreamOut << eData[i];
    	std::string strCtxt =  CtxtStreamOut.str();
    	const char* chr = strCtxt.c_str();
//     	cout << " write " << i << " , length " << strlen(chr) << endl;
   		n = secureWrite('C', sockfd,chr,strlen(chr));
   	    if (n < 0) error("ERROR writing to socket");

    }

    // read the clear masked text from server
	bzero(buffer,MaxBufferSize);
	n = read(sockfd,buffer,MaxBufferSize);
	if (n < 0) error("ERROR Reading from socket");

// 	cout << " Received from server "<< buffer << endl;

	std::stringstream str(buffer);
	int readin;
	str >> readin;
	int result = readin^mask;

    close(sockfd);

    return result ;
}


int stopServer (int portno )
{
    int sockfd, n;
    struct sockaddr_in serv_addr;
    struct hostent *server;

    char buffer[MaxBufferSize];
    sockfd = socket(AF_INET, SOCK_STREAM, 0);
    if (sockfd < 0)
        error("ERROR opening socket");
    server = gethostbyname(ServerAddress);
    if (server == NULL) {
        fprintf(stderr,"ERROR, no such host\n");
        exit(0);
    }

    bzero((char *) &serv_addr, sizeof(serv_addr));
    serv_addr.sin_family = AF_INET;
    bcopy((char *)server->h_addr,
         (char *)&serv_addr.sin_addr.s_addr,
         server->h_length);
    serv_addr.sin_port = htons(portno);
    if (connect(sockfd,(struct sockaddr *) &serv_addr,sizeof(serv_addr)) < 0)
        error("ERROR connecting");

    cout << "++++ Bye-bye \n ";


    n = write(sockfd,endCode,strlen(endCode));
    if (n < 0) error("ERROR writing to socket");

    close(sockfd);
    return 0 ;
}


int pageServer (int portno )
{
    int sockfd, n;
    struct sockaddr_in serv_addr;
    struct hostent *server;

    char buffer[MaxBufferSize];
    sockfd = socket(AF_INET, SOCK_STREAM, 0);
    if (sockfd < 0)
        error("ERROR opening socket");
    server = gethostbyname(ServerAddress);
    if (server == NULL) {
        fprintf(stderr,"ERROR, no such host\n");
        exit(0);
    }

    bzero((char *) &serv_addr, sizeof(serv_addr));
    serv_addr.sin_family = AF_INET;
    bcopy((char *)server->h_addr,
         (char *)&serv_addr.sin_addr.s_addr,
         server->h_length);
    serv_addr.sin_port = htons(portno);
    if (connect(sockfd,(struct sockaddr *) &serv_addr,sizeof(serv_addr)) < 0)
        error("ERROR connecting");


    n = write(sockfd,echoCode,strlen(echoCode));
    if (n < 0) error("ERROR writing to socket");

    close(sockfd);
    return 0 ;
}

void validateETree(string Data_File, int totalAttributes, eTree * etree, FHESecKey& secretKey) {

	const EncryptedArray& ea = *(secretKey.getContext().ea);
	const FHEPubKey& publicKey = secretKey;

	cout << "Evl Start<<<<" << float( clock () - begin_time ) /  CLOCKS_PER_SEC  << endl;;

	ifstream Data(Data_File);
	string line;
	int item;
	vector < Ctxt> RowEN;
	vector < Ctxt> resultSetEN;
	vector < Ctxt> resultSetNegEN;
	vector < Ctxt> referenceSetEN;
	vector < Ctxt> referenceSetNegEN;
	vector < Ctxt> countTmp;
 	getline(Data, line); // skip the header
 	int lineCount = 0;
	while(!Data.eof())
	{
		getline(Data, line);
	 	istringstream iss(line);
	 	int count = 0 ;
		while(iss >> item )
		{
			Ctxt itemEN(publicKey);
			secretKey.Encrypt(itemEN, ZZX(item &1));

			if ( count < totalAttributes )  {
				  RowEN.push_back(itemEN);
 			}
			else {
				Ctxt itemNegEN(publicKey);
				itemNegEN = itemEN;
				itemNegEN.addConstant(ZZX(1));
				referenceSetEN.push_back(itemEN);
				referenceSetNegEN.push_back(itemNegEN);
			}
			count ++;
		}
// 		cout << "line " << lineCount ++ << " data " << line << endl;
//		cout << "attribute number: " << RowEN.size() << endl;

		Ctxt rowResultEN(publicKey);
		Ctxt rowResultNegEN(publicKey);
	 	rowResultEN = TesteTree(etree, 0, RowEN, secretKey);
	 	rowResultNegEN = rowResultEN;
	 	rowResultNegEN.addConstant(ZZX(1));
	 	resultSetEN.push_back(rowResultEN);
	 	resultSetNegEN.push_back(rowResultNegEN);
		RowEN.erase(RowEN.begin(),RowEN.end());
 	}
	Data.close();
	cout << "Evl End<<<<" << float( clock () - begin_time ) /  CLOCKS_PER_SEC  << endl;;
	cout << "Total processed "  << resultSetEN.size() << " lines \n";

	for ( int i =0; i < resultSetEN.size(); i++ ) {

	 	vector <long> SLot;
		ea.decrypt(resultSetEN[i], secretKey, SLot);
		cout << " Line " << i <<  " - Predict: " << SLot[0];
 		ea.decrypt(referenceSetEN[i], secretKey, SLot);
		cout << " Reference: " << SLot[0] << endl;
	}


	NTL::Vec< NTL::Vec<Ctxt> > confusion_1_1_Vec(INIT_SIZE,resultSetEN.size());
	NTL::Vec< NTL::Vec<Ctxt> > confusion_1_0_Vec(INIT_SIZE,resultSetEN.size());
	NTL::Vec< NTL::Vec<Ctxt> > confusion_0_1_Vec(INIT_SIZE,resultSetEN.size());
	NTL::Vec< NTL::Vec<Ctxt> > confusion_0_0_Vec(INIT_SIZE,resultSetEN.size());


	NTL::Vec<Ctxt> count_confusion_1_1_Vec;
	NTL::Vec<Ctxt> count_confusion_1_0_Vec;
	NTL::Vec<Ctxt> count_confusion_0_1_Vec;
	NTL::Vec<Ctxt> count_confusion_0_0_Vec;
	resize(count_confusion_1_1_Vec, bitSize, Ctxt(publicKey));
	resize(count_confusion_1_0_Vec, bitSize, Ctxt(publicKey));
	resize(count_confusion_0_1_Vec, bitSize, Ctxt(publicKey));
	resize(count_confusion_0_0_Vec, bitSize, Ctxt(publicKey));
	CtPtrs_VecCt count_confusion_1_1(count_confusion_1_1_Vec);
	CtPtrs_VecCt count_confusion_0_1(count_confusion_0_1_Vec);
	CtPtrs_VecCt count_confusion_1_0(count_confusion_1_0_Vec);
	CtPtrs_VecCt count_confusion_0_0(count_confusion_0_0_Vec);

	NTL::Vec<Ctxt> temp1EN_vec;
	resize(temp1EN_vec, bitSize, Ctxt(publicKey));
	CtPtrs_VecCt temp1EN(temp1EN_vec);

	NTL::Vec<Ctxt> temp2EN_vec;
	resize(temp2EN_vec, bitSize, Ctxt(publicKey));
	CtPtrs_VecCt temp2EN(temp2EN_vec);

 	for ( int i =0; i < resultSetEN.size(); i++ ) {

		temp1EN_vec[0] = resultSetEN[i];
		temp2EN_vec[0] =  referenceSetEN[i];

		NTL::Vec<Ctxt> tempEN11_vec;
		resize(tempEN11_vec, bitSize, Ctxt(publicKey));
		CtPtrs_VecCt tempEN11(tempEN11_vec);

	 	multTwoNumbers(tempEN11, temp1EN ,temp2EN,false,bitSize, &unpackSlotEncoding);
	 	NTL::Vec<Ctxt> tempEN_vec_out = tempEN11.v;
	 	confusion_1_1_Vec[i] = tempEN_vec_out;
   	}

	CtPtrMat_VecCt confusion_1_1_Mat(confusion_1_1_Vec);
	addManyNumbers(count_confusion_1_1, confusion_1_1_Mat, bitSize, &unpackSlotEncoding );

	for ( int i =0; i < resultSetEN.size(); i++ ) {

		temp1EN_vec[0] = resultSetEN[i];
		temp2EN_vec[0] = referenceSetNegEN[i];

		NTL::Vec<Ctxt> tempEN10_vec;
		resize(tempEN10_vec, bitSize, Ctxt(publicKey));
		CtPtrs_VecCt tempEN10(tempEN10_vec);

	 	multTwoNumbers(tempEN10, temp1EN ,temp2EN,false,bitSize, &unpackSlotEncoding);
	 	NTL::Vec<Ctxt> tempEN_vec_out = tempEN10.v;
	 	confusion_1_0_Vec[i] = tempEN_vec_out;

   	}

	CtPtrMat_VecCt confusion_1_0_Mat(confusion_1_0_Vec);
	addManyNumbers(count_confusion_1_0, confusion_1_0_Mat, bitSize, &unpackSlotEncoding );

	for ( int i =0; i < resultSetEN.size(); i++ ) {

		temp1EN_vec[0] = resultSetNegEN[i];
		temp2EN_vec[0] =  referenceSetEN[i];

		NTL::Vec<Ctxt> tempEN01_vec;
		resize(tempEN01_vec, bitSize, Ctxt(publicKey));
		CtPtrs_VecCt tempEN01(tempEN01_vec);

		multTwoNumbers(tempEN01, temp1EN ,temp2EN,false,bitSize, &unpackSlotEncoding);
	 	NTL::Vec<Ctxt> tempEN_vec_out = tempEN01.v;
	 	confusion_0_1_Vec[i] = tempEN_vec_out;

   	}

	CtPtrMat_VecCt confusion_0_1_Mat(confusion_0_1_Vec);
	addManyNumbers(count_confusion_0_1, confusion_0_1_Mat, bitSize, &unpackSlotEncoding );

	for ( int i =0; i < resultSetEN.size(); i++ ) {

		temp1EN_vec[0] = resultSetNegEN[i];
		temp2EN_vec[0] =  referenceSetNegEN[i];

		NTL::Vec<Ctxt> tempEN00_vec;
		resize(tempEN00_vec, bitSize, Ctxt(publicKey));
		CtPtrs_VecCt tempEN00(tempEN00_vec);

	 	multTwoNumbers(tempEN00, temp1EN ,temp2EN,false,bitSize, &unpackSlotEncoding);
	 	NTL::Vec<Ctxt> tempEN_vec_out = tempEN00.v;
	 	confusion_0_0_Vec[i] = tempEN_vec_out;

   	}
	CtPtrMat_VecCt confusion_0_0_Mat(confusion_0_0_Vec);
	addManyNumbers(count_confusion_0_0, confusion_0_0_Mat, bitSize, &unpackSlotEncoding );

	vector<long> slotsa;
	decryptBinaryNums(slotsa, count_confusion_1_1, secretKey, ea);
	cout << "Confusion matrix 1-1 ** " << slotsa[0] << endl;
	decryptBinaryNums(slotsa, count_confusion_1_0, secretKey, ea);
	cout << "Confusion matrix 1-0 ** " << slotsa[0] << endl;
	decryptBinaryNums(slotsa, count_confusion_0_1, secretKey, ea);
	cout << "Confusion matrix 0-1 ** " << slotsa[0] << endl;
	decryptBinaryNums(slotsa, count_confusion_0_0, secretKey, ea);
	cout << "Confusion matrix 0-0 ** " << slotsa[0] << endl<< endl;
}


int main (int argc, char *argv[]) {

	FHEcontext context  = FHE_keyGen(argc, argv);


	cout << "\ncomputing key-dependent tables..." << std::flush;

    std::cout << "\n security=" << context.securityLevel()<<endl;
    std::cout << "# ctxt primes = " << context.ctxtPrimes.card() << "\n";
    std::cout << "# bits in ctxt primes = "
	 << long(context.logOfProduct(context.ctxtPrimes)/log(2.0) + 0.5) << "\n";
    std::cout << "# special primes = " << context.specialPrimes.card() << "\n";
    std::cout << "# bits in special primes = "
	 << long(context.logOfProduct(context.specialPrimes)/log(2.0) + 0.5) << "\n";

	FHESecKey secretKey(context);
	const FHEPubKey& publicKey = secretKey;
	secretKey.GenSecKey(/*Hweight=*/128);
	addSome1DMatrices(secretKey); // compute key-switching matrices
	addFrbMatrices(secretKey);
	if (bootstrap) secretKey.genRecryptData();
	cout << " + done\n";

	pid_t pID = fork();

	if (pID == 0)   {
		// Code only executed by child process

		cout << "Client thread started!!" << endl;

		begin_time = clock();


		pageServer(TcpPort);  // check connection

		Build_ID3_FHE(secretKey);

		stopServer(TcpPort);

		printAllTimers(cout);

	 	}
	else if (pID < 0) { // fail to fork
	      cerr << "Failed to fork" << endl;
		  exit(1);
		          // Throw exception
		}
	else  { // parent
		// Code only executed by parent process

		cout << "Server thread!!" << endl;
	   	launchServer (TcpPort,secretKey);
		cout << "Server thread end !!" << endl;

	}

}
