#include <algorithm>
#include <array>
#include <cassert>
#include <fstream>
#include <iostream>
#include <sstream>
#include <vector>
using namespace std;
int main(int argc,char**argv){
 int L=argc>1?stoi(argv[1]):120;
 string prefix=argc>2?argv[2]:"independent";
 const int W=L+1;
 vector<unsigned char> p(12*W*W,0);
 auto idx=[&](int m,int a,int b){return (m*W+a)*W+b;};
 auto isp=[&](int a,int b,int c){array<int,3> q={a,b,c};sort(q.begin(),q.end());assert(q[0]<=11);return p[idx(q[0],q[1],q[2])];};
 long long states=0,moves=0;int ps=0;
 for(int m=0;m<=11;m++)for(int a=m;a<=L;a++)for(int b=a;b<=L;b++){
  bool n=false;
  for(int k=1;k<=m&&!n;k++){moves++;n=isp(m-k,a,b);}
  for(int k=1;k<=a&&!n;k++){moves++;n=isp(m,a-k,b);}
  for(int k=1;k<=b&&!n;k++){moves++;n=isp(m,a,b-k);}
  for(int u=0;u<=m&&!n;u++)for(int v=0;v<=a&&!n;v++){
   int w=u^v;if(w>b||!(u|v|w))continue;moves++;n=isp(m-u,a-v,b-w);
  }
  p[idx(m,a,b)]=!n;ps+=!n;states++;
 }
 int expected=0;
 for(int m=0;m<=11;m++){
  ifstream in(prefix+"_slice_"+to_string(m)+".csv");string line;getline(in,line);
  while(getline(in,line)){
   replace(line.begin(),line.end(),',',' ');int i,a,b,d;istringstream(line)>>i>>a>>b>>d;
   if(b<=L){assert(p[idx(m,a,b)]);expected++;p[idx(m,a,b)]=0;}
  }
 }
 for(auto v:p)assert(v==0);
 cout<<"Direct DP verified: states="<<states<<" tested moves="<<moves<<" P-positions="<<ps<<" matching expected="<<expected<<" max heap="<<L<<" min heap<=11\n";
}
