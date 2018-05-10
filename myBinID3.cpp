/*
 * myID3.cpp
 *
 *  Created on: Feb 01, 2018
 *      Author: luyaoc
 *      ref: https://github.com/zgyao/DecisionTree_ID3/blob/master/DecisionTree_ID3.cpp
 */

#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <vector>
#include <map>
#include <algorithm>
#include <math.h>
#include <time.h>


using namespace std;

#define MAX_Attributes 100

int treeNodes;
clock_t begin_time;

int IntCompare(int a,int b)
{
	if (a>b) return 1;
	else if (a==b) return 0;
	else return -1;
}

int SumVector(vector < int > a)
{
	std::size_t i;
	int result = 0;
	for ( i = 0; i < a.size(); i++) {
		result += a[i];
	}
	return result;
}

class MatrixCls
{
private:
	vector < vector < int > > Matrix;
public:
	MatrixCls(string Data_File)
{
		Matrix.erase(Matrix.begin(),Matrix.end());
		ifstream Data(Data_File);
		string line;
		int item;
		vector < int > Row;
		while(!Data.eof())
		{
			getline(Data, line);
			istringstream iss(line);
			while(iss >> item)
			{
				if (item >= 0 && item <= MAX_Attributes)
				{
					Row.push_back(item);
				}
			}

			if(line.length())
			{
				Matrix.push_back(Row);
				Row.erase(Row.begin(),Row.end());
			}
		}
		Data.close();
}

	MatrixCls(vector < vector < int > > A_Matrix)
	{
		for(std::size_t i = 0; i < A_Matrix.size(); i++)
		{
			Matrix.push_back(A_Matrix[i]);
		}
	}

	MatrixCls(){ };
	~MatrixCls(){ };

	int Element(int i,int j)
	{
		return Matrix[i][j];
	}

	int SizeX()  //Attributes
	{
		return Matrix[0].size();
	}

	std::size_t SizeY() // instances + 1 (rows)
	{
		return Matrix.size();
	}

	vector < int > GetAttributes()
    {
		vector < int > Attribute;
		std::size_t j;
		for(j = 0; j < Matrix[0].size()-1; j++)
		{
			Attribute.push_back(Matrix[0][j]);
		}
		return Attribute;
    }

	map < int, vector < int > > GetAttributesValues()
    {
		map < int, vector < int > > Attributes_Values;
		vector < int > Attribute_Values;
		std::size_t i, j ;

		for(j = 0; j < Matrix[0].size(); j++) {
			int count = 0, numbers = 0 ;
			for(i = 1; i < Matrix.size(); i++) {
				numbers += Matrix[i][j];
				count ++;
						}
			if (IntCompare(numbers,count) == 0 ) {
				Attribute_Values.push_back(1);
			}
			else if (IntCompare(numbers,count) == 0 ) {
				Attribute_Values.push_back(0);
						}
			else {
				Attribute_Values.push_back(0);
				Attribute_Values.push_back(1);
			}
			Attributes_Values[Matrix[0][j]] = Attribute_Values;
			Attribute_Values.erase(Attribute_Values.begin(),Attribute_Values.end());
		}

		return Attributes_Values;
    }

	vector < int > GetAttributeValues(int The_Attribute)
    	{
		return GetAttributesValues()[The_Attribute];
    						}

	vector < int > GetClassRange()  // List of Predicted values
    	{
		return GetAttributesValues()[Matrix[0][SizeX()-1]];
    						}

	int AttributeIndex(int The_Attribute) // sequence in the matrix for the attributes
	{
		int Index = 0;
		for(int i = 0; i < SizeX(); i++)
		{
			if(IntCompare(Matrix[0][i],The_Attribute) == 0)
			{
				Index = i;
				break;
			}
		}
		return Index;
	}

	// for the Attribute, list classes of each attribute value
	map < int, vector < int > > GetAttributeValuesClasses(int The_Attribute)
    						{
	 	std::size_t i;
		int Index = AttributeIndex(The_Attribute);
		map < int, vector < int > > Attribute_Values_Classes;
		vector < int > Row_Zeros,Row_Ones;

		for(i = 1; i < SizeY(); i++)
				{
				if(IntCompare(Matrix[i][Index],0) == 0)
					Row_Zeros.push_back(Matrix[i][SizeX()-1]);
				else
					Row_Ones.push_back(Matrix[i][SizeX()-1]);
				}
		Attribute_Values_Classes[0] = Row_Zeros;
		Attribute_Values_Classes[1] = Row_Ones;

		/*
		vector < int > Attribute_Values = GetAttributesValues()[The_Attribute];
		vector < int > Row;
		for(k = 0; k < Attribute_Values.size(); k++)
		{
			for(i = 1; i < SizeY(); i++)
			{
				if(IntCompare(Matrix[i][Index],Attribute_Values[k]) == 0)
				{
					Row.push_back(Matrix[i][SizeX()-1]);
				}
			}
			Attribute_Values_Classes[Attribute_Values[k]] = Row;
			Row.erase(Row.begin(),Row.end());
		}
		*/


	return Attribute_Values_Classes;
    }

	vector < int > GetClasses()  // all predicted values from row 2
    						{
		vector < int > Classes;
		for( std::size_t i = 1; i < Matrix.size(); i++)
		{
			Classes.push_back(Matrix[i][Matrix[0].size()-1]);
		}
		return Classes;
    	}

	MatrixCls operator() (MatrixCls A_Matrix, int The_Attribute, int The_Value)
	{
		Matrix.erase(Matrix.begin(),Matrix.end());
		int j;
		std::size_t i;
		int Index = 0;
		vector < int > Row;
		for( j = 0; j < A_Matrix.SizeX(); j++)
		{
			if(IntCompare(A_Matrix.Element(0,j),The_Attribute) != 0)
			{
				Row.push_back(A_Matrix.Element(0,j));
			}
			else if(IntCompare(A_Matrix.Element(0,j),The_Attribute) == 0)
			{
				Index = j;
			}
		}
		if(Row.size() != 0)
		{
			Matrix.push_back(Row);
			Row.erase(Row.begin(),Row.end());
		}

		for(i = 1; i < A_Matrix.SizeY(); i++)
		{
			for( j = 0; j < A_Matrix.SizeX(); j++)
			{
				if(IntCompare(A_Matrix.Element(0,j),The_Attribute) != 0 && IntCompare(A_Matrix.Element(i,Index),The_Value) == 0)
				{
					Row.push_back(A_Matrix.Element(i,j));
				}
			}
			if(Row.size() != 0)
			{
				Matrix.push_back(Row);
				Row.erase(Row.begin(),Row.end());
			}
		}

		return *this;
	}

	void Display()
	{
		std::size_t i, j;
		for(i = 0; i < Matrix.size(); i++)
		{
			for(j = 0; j < Matrix[0].size(); j++)
			{
				cout << " " << Matrix[i][j];
			}
			cout << endl;
		}
	}
};

vector < int > GetUniqueClasses(vector < int > Classes)
						{
	sort(Classes.begin(), Classes.end());
	Classes.erase(unique(Classes.begin(), Classes.end()), Classes.end());
	return Classes;
						}

int GetFrequentClass(vector < int > Classes)
{

	int ones= SumVector (Classes);
    int zeros = Classes.size() - ones;

    if (IntCompare(ones,zeros) == 1) { return 1;}
    else return 0;

}

double ComputeEntropy(vector < int > Classes)
{

	if(Classes.size() == 0)
	{
		return 0.;
	}
	else
	{
		int ones= SumVector (Classes);
		int zeros = Classes.size() - ones;

		vector < int > Class_Range;

		Class_Range.push_back(zeros);
		Class_Range.push_back(ones);

		double TheEntropy = 0.;
		std::size_t j;
		int Count[Class_Range.size()] = {zeros,ones};

		double Temp_Entropy;
		double Temp_P;
		for(j = 0; j < Class_Range.size(); j++)
		{
			if(Count[j] == 0)
			{
				Temp_Entropy = 0.;
			} else {
				Temp_P = (double)Count[j]/(double)(Classes.size());
				Temp_Entropy = -Temp_P*log(Temp_P)/log(2.);
			}
			TheEntropy = TheEntropy + Temp_Entropy;
		}
		return TheEntropy;
	}
}

double ComputeAttributeEntropyGain(MatrixCls Remain_Matrix, int The_Attribute)
{
	double Original_Entropy = 0., Gained_Entropy = 0.;
	vector < int > Classes = Remain_Matrix.GetClasses();


	Original_Entropy = ComputeEntropy(Classes);

	// get Attribute Values for all instants
	vector < int > Attribute_Values = Remain_Matrix.GetAttributeValues(The_Attribute);

	double After_Entropy = 0.;
	double Temp_Entropy;
	vector < int > Temp_Classes;
	std::size_t i;

	// for the Attribute, list classes of each attribute value
	map < int, vector < int > > Values_Classes = Remain_Matrix.GetAttributeValuesClasses(The_Attribute);

	for(i = 0; i < Attribute_Values.size(); i++)
	{
		Temp_Classes = Values_Classes[Attribute_Values[i]];
		Temp_Entropy = ComputeEntropy(Temp_Classes)*(double)Temp_Classes.size()/(double)Classes.size();
		After_Entropy = After_Entropy + Temp_Entropy;
	}
	Gained_Entropy = Original_Entropy -  After_Entropy;
	return Gained_Entropy;
}



class Tree
{
public:
	int Node;
	int Branch;
	vector < Tree * > Child;
	Tree();
	~Tree();
	Tree * BuildTree(Tree * tree, MatrixCls Remain_Matrix);
	void PrintTree(Tree * tree, int Depth);

	int Temp_TestTree(Tree * tree, vector < int > Attributes, vector < int > Values, vector < int > Class_Range);
	int Test_Bin_Tree(Tree * tree, vector < int > Attributes, vector < int > Values);

	vector < int > TestTree(Tree * tree, MatrixCls The_Matrix);
};

int Tree::Test_Bin_Tree(Tree * tree, vector < int > The_Attributes, vector < int > The_Values)
{
	std::size_t i,j;
	int result = 0;
	vector < int > Remain_Attributes,Remain_Values;
	for ( i = 0; i< The_Attributes.size();i++) {
		if (tree->Node == The_Attributes [i] ) {

			Remain_Attributes =The_Attributes;
			Remain_Attributes.erase ( Remain_Attributes.begin()+i);
			Remain_Values = The_Values;
			Remain_Values.erase ( Remain_Values.begin()+i);

			for(j = 0; j < tree->Child.size(); j++) {
				if (IntCompare(The_Values[i],tree->Child[j]->Branch) ==0 && tree->Child[j]->Child.size() == 0 ) {
					return tree->Child[j]->Node;
				} else {
					if (IntCompare(The_Values[i],tree->Child[j]->Branch) ==0 ) {
						result = Test_Bin_Tree (tree->Child[j],Remain_Attributes,Remain_Values);
						return result;
					}
				}

			}
		}
	}
	return result;
}

Tree::Tree()
{
	Node = -1;
	Branch = -1;
}
Tree::~Tree(){ };

Tree * Tree::BuildTree(Tree * tree, MatrixCls Remain_Matrix)
{
	cout << "current size " << Remain_Matrix.SizeX() <<  " -  " << Remain_Matrix.SizeY() << endl;

	if(tree == NULL)
	{
		tree = new Tree();
	}

	bool No_Ones=false ,No_Zeros = false ;

	int Class_Ones =SumVector ( Remain_Matrix.GetClasses());
	if (IntCompare( Class_Ones , 0) == 0) No_Ones = true;

	int Class_Zeross = Remain_Matrix.GetClasses().size() - Class_Ones;
	if (IntCompare( Class_Zeross , 0) == 0) No_Zeros = true;

	if (No_Ones)  {
		tree->Node = 0;
		return tree;

	}

	if (No_Zeros)  {
			tree->Node = 1;
			return tree;

		}

	vector < int > Unique_Classes ={0,1};

	if(Remain_Matrix.SizeX() == 1)
	{
		int Frequent_Class = GetFrequentClass(Remain_Matrix.GetClasses());
		tree->Node = Frequent_Class;
		return tree;
	}

	double Max_Gain = 0., Temp_Gain;
	std::size_t j;
	int Max_Attribute = 0 ;
	vector < int > Attributes = Remain_Matrix.GetAttributes();
	for(j = 0; j < Attributes.size(); j++)
	{
//		cout << "Attributes: " << j << endl;
		Temp_Gain =  ComputeAttributeEntropyGain(Remain_Matrix,Attributes[j]);
		if((Temp_Gain - Max_Gain) > 1.e-8)
		{
			Max_Gain = Temp_Gain;
			Max_Attribute = Attributes[j];
		}
	}
	tree->Node = Max_Attribute;
	vector < int > Values = Remain_Matrix.GetAttributeValues(Max_Attribute);

	cout << "---------Attribute:"<< Max_Attribute << endl;
	cout << "---------Values:";
	for ( std::size_t c=0 ; c < Values.size(); c++) cout << Values[c] <<"," ;
	cout << endl;

	std::size_t k;
	MatrixCls New_Matrix;
	for(k = 0; k < Values.size(); k++)
	{
		cout << "-------Process Value:"<< Values[k] << endl;
		New_Matrix = New_Matrix.operator()(Remain_Matrix, Max_Attribute, Values[k]);
		Tree * New_tree = new Tree();
		New_tree->Branch = Values[k];
		if(New_Matrix.SizeX() == 1)
		{
			vector < int > reminClasses = New_Matrix.GetClasses();
			New_tree->Node = GetFrequentClass(reminClasses);
		}
		else
		{
			BuildTree(New_tree, New_Matrix);
		}
		tree->Child.push_back(New_tree);
	//	cout << "#############"<< endl;
	//	tree->PrintTree(tree,-1);
	//	cout << "#############"<< endl;
	}


	return tree;

}

void Tree::PrintTree(Tree * tree, int Depth = -1)
{
	treeNodes += 1;
	for(int i = 0; i < Depth; i++) cout << "\t";
	if(IntCompare(tree->Branch,-1) != 0)
	{
		cout << tree->Branch << endl;
		for(int i = 0; i < Depth+1; i++) cout << "\t";
	}
	if(Depth == -1 && IntCompare(tree->Branch,-1) != 0)
	{
		cout << "\t";
	}
	cout << tree->Node << endl;
	for(std::size_t i = 0; i < tree->Child.size(); i++)
	{
		PrintTree(tree->Child[i], Depth+1);
	}
}

vector < int > Tree::TestTree(Tree * tree, MatrixCls The_Matrix)
{
	vector < int > Test_Classes;
	vector < int > Attributes = The_Matrix.GetAttributes();
	vector < int > Class_Range = The_Matrix.GetClassRange();
	vector < int > Values;
	for(std::size_t i = 1; i < The_Matrix.SizeY(); i++)
	{
		for(std::size_t j = 0; j < Attributes.size(); j++)
		{
			Values.push_back(The_Matrix.Element(i,j));
		}
		// int result = Temp_TestTree(tree, Attributes, Values, Class_Range);

		int result = Test_Bin_Tree(tree, Attributes, Values);

		Test_Classes.push_back(result);
		Values.erase(Values.begin(),Values.end());
	}

	return Test_Classes;
}

int main()
{
	cout << "Binary Tree Round 1:" << endl;

	MatrixCls Matrix("Train.dat");
	MatrixCls Matrix_Test("Test.dat");

	begin_time = clock();

	map < int, vector < int > > Attributes_Values;

	Tree * root =new Tree();
	root = root->BuildTree(root, Matrix);
	treeNodes = 0;
	root->PrintTree(root);
	cout << "total nodes " << treeNodes;
	cout << "<<<< build" << float( clock () - begin_time ) /  CLOCKS_PER_SEC  << endl;;

	vector < int > Original_Classes = Matrix.GetClasses();
	cout << "<<<< test start" << float( clock () - begin_time ) /  CLOCKS_PER_SEC  << endl;;
	vector < int > Train_Classes = root->TestTree(root,Matrix);
	cout << "<<<< test end" << float( clock () - begin_time ) /  CLOCKS_PER_SEC  << endl;;
	vector < int > Test_Data = Matrix_Test.GetClasses();
	vector < int > Test_Classes = root->TestTree(root,Matrix_Test);


	cout << "\nTrain_Data_Predict:" << endl;
		for(vector<int>::const_iterator i = Train_Classes.begin(); i != Train_Classes.end(); ++i)
		{
			cout << *i << "  ";
		}
	cout << endl << endl;

	cout << "\nTrain_Data_Reference:" << endl;
	for(vector<int>::const_iterator i = Original_Classes.begin(); i != Original_Classes.end(); ++i)
	{
		cout << *i << "  ";
	}
	cout << endl << endl;

	cout << "\nTrain_Accuracy:";
	int count=0;
	for(std::size_t i = 0; i < Original_Classes.size(); i++) {
		if (IntCompare(Original_Classes[i],Train_Classes[i]) == 0 ) count++;
		}
	double accuracy =  double(count)/ Original_Classes.size();
	cout << fixed << accuracy * 100  << '%' ;
	cout << endl << endl;


	cout << "Test_Data_Predict:" << endl;
	for(vector<int>::const_iterator j = Test_Classes.begin(); j != Test_Classes.end(); ++j)
	{
		cout << *j << "  ";
	}
	cout << endl << endl;
	cout << "Test_data_Reference:" << endl;
	for(vector<int>::const_iterator j = Test_Data.begin(); j != Test_Data.end(); ++j)
	{
		cout << *j << "  ";
	}
	cout << endl;

	cout << "Test_Accuracy:";
	count=0;
	for(std::size_t i = 0; i < Test_Data.size(); i++) {
		if (IntCompare(Test_Data[i],Test_Classes[i]) == 0 ) count++;
		}
	accuracy =  double(count)/ Test_Data.size();
	cout << fixed << accuracy * 100  << '%' ;
	cout << endl << endl;


	delete root;
}
