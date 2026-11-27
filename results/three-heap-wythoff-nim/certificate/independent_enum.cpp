#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <functional>
#include <map>
#include <set>
#include <vector>
using namespace std;
struct Pair {int a,b;};
struct Slice {vector<Pair> p; map<int,vector<Pair>> bydiff;};
bool move_to(int m,int x,int y,int r,int a,int b) {
 array<int,3> q={r,a,b};
 do {
  if(q[0]>m||q[1]>x||q[2]>y)continue;
  int u=m-q[0],v=x-q[1],w=y-q[2];
  if(!(u|v|w))continue;
  if((u^v^w)==0 || (u==0&&v==0)||(u==0&&w==0)||(v==0&&w==0))return true;
 }while(next_permutation(q.begin(),q.end()));
 return false;
}
bool hit_lower(int m,int x,int y,const vector<Slice>& all, const vector<vector<Pair>>& exceptional) {
 int d=y-x;
 for(int r=0;r<m;r++){
  int h=m-r;
  // First source heap maps to least target heap. Forward order.
  for(int e=max(0,d-h);e<=d+h;e++){
   auto it=all[r].bydiff.find(e); if(it==all[r].bydiff.end())continue;
   for(auto p:it->second){
    if(p.a>x||p.b>y)continue;
    if((h^(x-p.a)^(y-p.b))==0)return true;
    // single-heap reduction of the first heap
    if(x==p.a&&y==p.b)return true;
   }
  }
  // Opposite order or source first heap maps to a larger target:
  // these require e <= h, or a <= m, respectively.
  for(auto p:exceptional[r]){
   if(p.a>x)break;
   if(move_to(m,x,y,r,p.a,p.b))return true;
  }
 }
 return false;
}
int main(int argc,char**argv){
 int M=argc>1?stoi(argv[1]):10000;
 string prefix=argc>2?argv[2]:"independent";
 vector<Slice> all(12);
 for(int m=0;m<=11;m++){
  set<int> used,diff;
  vector<int> nxt(4*M+1024);iota(nxt.begin(),nxt.end(),0);
  function<int(int)> nextfree = [&](int k)->int { assert(k<(int)nxt.size());return nxt[k]==k?k:nxt[k]=nextfree(nxt[k]); };
  vector<vector<Pair>> exceptional(m);
  for(int r=0;r<m;r++)for(auto p:all[r].p)if(p.a<=m || p.b-p.a<=m-r)exceptional[r].push_back(p);
  for(int r=0;r<m;r++)for(auto p:all[r].p)if(p.a==m)used.insert(p.b);
  for(int x=m;x<=M;x++){
   if(used.count(x))continue;
   int d=nextfree(0);
   while(used.count(x+d)||hit_lower(m,x,x+d,all,exceptional))d=nextfree(d+1);
   int y=x+d;
   all[m].p.push_back({x,y});all[m].bydiff[y-x].push_back({x,y});
   used.insert(x);used.insert(y);diff.insert(y-x);
   nxt[d]=nextfree(d+1);
  }
  ofstream out(prefix+"_slice_"+to_string(m)+".csv");out<<"n,a,b,d\n";
  int n=1;for(auto p:all[m].p)out<<n++<<","<<p.a<<","<<p.b<<","<<p.b-p.a<<"\n";
  cerr<<"m="<<m<<" positions="<<all[m].p.size()<<" last="<<all[m].p.back().a<<","<<all[m].p.back().b<<"\n";
 }
}
