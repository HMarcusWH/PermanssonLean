// Independent checker of Cogentic, equations (4.1)-(4.8).
// GCC/Clang C++17; use signed-overflow/undefined-behavior sanitizer when replaying.
// All acceptance arithmetic is outward-rounded fixed-point integer interval arithmetic.
#include <algorithm>
#include <cstdlib>
#include <array>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <vector>
#include <limits>
#include <chrono>
using namespace std;
using W=__int128_t; using I=int64_t;
constexpr I S=I(1)<<40;
I fl(W a,W b){assert(b>0);W q=a/b,r=a%b;if(r<0)--q; assert(q>=INT64_MIN&&q<=INT64_MAX);return I(q);}
I ce(W a,W b){return -fl(-a,b);}
struct V { I l,h; V():l(0),h(0){} V(I a,I b):l(a),h(b){assert(a<=b);} };
V cn(I a,I b=1){return V(fl(W(a)*S,b),ce(W(a)*S,b));}
V operator+(V a,V b){return V(a.l+b.l,a.h+b.h);} V operator-(V a,V b){return V(a.l-b.h,a.h-b.l);} V operator-(V a){return V(-a.h,-a.l);}
V operator*(V a,V b){W v[]={W(a.l)*b.l,W(a.l)*b.h,W(a.h)*b.l,W(a.h)*b.h};return V(fl(*min_element(v,v+4),S),ce(*max_element(v,v+4),S));}
V operator/(V a,V b){assert(b.l>0);I lo=INT64_MAX,hi=INT64_MIN;for(I x:{a.l,a.h})for(I y:{b.l,b.h}){lo=min(lo,fl(W(x)*S,y));hi=max(hi,ce(W(x)*S,y));}return V(lo,hi);}
V sq(V a){W x=W(a.l)*a.l,y=W(a.h)*a.h;return V(a.l<=0&&a.h>=0?0:fl(min(x,y),S),ce(max(x,y),S));}
V pos(V a){return V(max(I(0),a.l),max(I(0),a.h));} V mn(V a,V b){return V(min(a.l,b.l),min(a.h,b.h));} V hull(V a,V b){return V(min(a.l,b.l),max(a.h,b.h));}
struct D{V v;array<V,3> d;D(){} D(V x):v(x){} };
D c(I a,I b=1){return D(cn(a,b));} D var(V a,int i){D x(a);x.d[i]=cn(1);return x;}
D operator+(D a,D b){D z(a.v+b.v);for(int i=0;i<3;i++)z.d[i]=a.d[i]+b.d[i];return z;}
D operator-(D a,D b){D z(a.v-b.v);for(int i=0;i<3;i++)z.d[i]=a.d[i]-b.d[i];return z;}
D operator*(D a,D b){D z(a.v*b.v);for(int i=0;i<3;i++)z.d[i]=a.d[i]*b.v+a.v*b.d[i];return z;}
D operator/(D a,D b){D z(a.v/b.v);for(int i=0;i<3;i++)z.d[i]=(a.d[i]-z.v*b.d[i])/b.v;return z;}
D sq(D a){D z(sq(a.v));for(int i=0;i<3;i++)z.d[i]=cn(2)*a.v*a.d[i];return z;}
D pos(D a){if(a.v.l>=0)return a;if(a.v.h<=0)return c(0);D z(pos(a.v));for(int i=0;i<3;i++)z.d[i]=hull(cn(0),a.d[i]);return z;}
D mn(D a,D b){if(a.v.h<=b.v.l)return a;if(b.v.h<=a.v.l)return b;D z(mn(a.v,b.v));for(int i=0;i<3;i++)z.d[i]=hull(a.d[i],b.d[i]);return z;}
// Explicit upper approximation: composite trapezoidal upper bound on the positive part of an affine function.
// z branches use their continuous extension on the closed box; variance handled separately.
D calc(array<V,3> x,int branch,int N,bool smallVar){D z=var(x[0],0),a=var(x[1],1),b=var(x[2],2);D f=branch<=2?c(1):branch==3?(c(4)*z+c(1))*c(1,5):c(9,5);D A=(b+f*a-c(2)*f)*c(1,2),B=(b-f*a)*c(1,2);D J;
 if(A.v.l>=0&&B.v.l>=0)J=(A+B)*c(1,16);else if(A.v.h<=0&&B.v.h<=0)J=c(0);else{
  // The convex positive-part integrand has a composite trapezoidal upper bound.
  // The fixed-sign shortcuts above equal that same trapezoidal expression.
  J=(pos(A)+pos(B))*c(1,16*N);
  for(int i=1;i<N;i++)J=J+pos(A*c(N-i,N)+B*c(i,N))*c(1,8*N);
 }
 D F=f*a*c(1,8)-b*c(1,8)+(c(3)*sq(b+f*a)+sq(pos(b+f*a-c(2)*f))-c(4)*sq(pos(b-f*a)))/(c(64)*f)+J+sq(pos(b-a))*c(1,16)-f*sq(a)*c(1,10)-sq(b)*c(1,10);
 D lam=f*c(1,8)+(c(3)*(b+f*z)+pos(b+f*z-c(2)*f)+c(4)*pos(b-f*z))*c(1,32)-pos(b-z)*c(1,8)-f*z*c(1,5);
 if(branch>=2)lam=lam+f*c(1,128)*mn(c(1),c(8)*pos(z-c(7,8)))*(c(1)+mn(c(1),c(4)*pos(b-z)));
 D ev=branch<=1?c(5,1536):f*c(5,6144);
 if(smallVar){D p=pos((a+b)*c(1,2)-c(1,4));ev=mn(ev,c(5,162)*sq(p)*p);}
 return F-lam*(a-z)-(c(1,8)-b*c(1,80))*(z-b)+ev;
}
struct Box{array<V,3> x;int br,dep;};
int main(int argc,char**argv){int N=argc>1?atoi(argv[1]):8;long long cap=argc>2?atoll(argv[2]):3000000; if(N<1||N>256||cap<1){cerr<<"invalid input\n";return 3;} vector<Box> q;vector<array<I,2>> zs={{S/4,3*S/4},{3*S/4,7*S/8},{7*S/8,S},{S,2*S},{2*S,4*S}};for(int b=0;b<5;b++)q.push_back({{V(zs[b][0],zs[b][1]),V(S/4,4*S),V(S/4,4*S)},b,0});I target=fl(-W(S),3000);long long count=0,leaves=0,mon=0;int maxd=0;I worst=INT64_MIN;auto start=chrono::steady_clock::now();
while(!q.empty()&&count<cap){Box box=q.back();q.pop_back();auto x=box.x;int br=box.br;count++;maxd=max(maxd,box.dep);bool sm=br==0 && x[1].h+x[2].h<=2*S;D y=calc(x,br,N,sm);I upper=y.v.h;array<V,3> center;for(int i=0;i<3;i++){I m=x[i].l+(x[i].h-x[i].l)/2;center[i]=V(m,m);}D yc=calc(center,br,N,sm);V t=yc.v;for(int i=0;i<3;i++)t=t+y.d[i]*(x[i]-center[i]);upper=min(upper,t.h);
 if(upper<=target){leaves++;worst=max(worst,upper);continue;}
 // No monotonicity pruning: both closed child boxes are retained.
 // Floating point is used only to choose the split coordinate, not for acceptance.
 int ix=-1;long double best=-1;for(int i=0;i<3;i++){if(x[i].h-x[i].l<2)continue;long double score=(long double)(x[i].h-x[i].l)*max(abs((long double)y.d[i].l),abs((long double)y.d[i].h));if(score>best){best=score;ix=i;}}
 if(ix<0){cerr<<"FAIL point "<<br<<" "<<double(upper)/S<<" "<<double(x[0].l)/S<<" "<<double(x[1].l)/S<<" "<<double(x[2].l)/S<<"\n";return 1;}
 I m=x[ix].l+(x[ix].h-x[ix].l)/2;auto x2=x;x[ix].h=m;x2[ix].l=m;q.push_back({x,br,box.dep+1});q.push_back({x2,br,box.dep+1});
 if(count%100000==0)cerr<<count<<" q="<<q.size()<<" d="<<maxd<<" time="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";
}
 cout<<"N="<<N<<" processed="<<count<<" certified_leaves="<<leaves<<" monotone="<<mon<<" maxdepth="<<maxd<<" remaining="<<q.size()<<" max_certified_bound="<<worst<<"/"<<S<<" target_floor="<<target<<" time="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";
 if(!q.empty())return 2;
 assert(count==2*leaves-5 && worst<=target);
 return 0;
}
