# FHEID3
A decision tree implementation with fully homophobic encryption 

myBinID3.cpp - ID 3 decision tree over plaintext

myFHEID3.cpp - ID 3 decision tree over HElib FHE

compile & link 

g++ -I/home/users/HELibSrc -O0 -g -c -fmessage-length=0 -std=c++11 -MMD -MP -MF"myFHEID3.d" -MT"myFHEID3.o" -o "myFHEID3.o" "../myFHEID3.cpp"

g++ -o "MyFHEBinID3"  ./myFHEID3.o    ../fhe.a -L/usr/local/lib -lntl -lgmp -lm

Prequest for myFHEID3.cpp 

HElib  https://github.com/shaih/HElib
HElib is written in C++ and uses the GMP and NTL (version 10.0.0 or higher) mathematical library .  Refer to HElib installation document for deails.


