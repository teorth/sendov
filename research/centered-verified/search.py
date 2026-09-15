"""Exploratory full-complex-polar search; no certification from float results."""
import math, cmath, random, json, argparse
from pathlib import Path
R=random.Random(9142026)
OUT=Path(__file__).parent

def gauss(n=80):
    ans=[]
    for i in range(1,n+1):
        z=math.cos(math.pi*(i-.25)/(n+.5))
        for _ in range(20):
            p0,p1=1.,z
            for k in range(2,n+1): p0,p1=p1,((2*k-1)*z*p1-(k-1)*p0)/k
            dp=n*(z*p1-p0)/(z*z-1)
            nz=z-p1/dp
            if abs(nz-z)<2e-16: break
            z=nz
        ans.append(((1-z)/2,1/((1-z*z)*dp*dp)))
    return ans
NODES=gauss()
def polar(a,groups):
    d=1-a*a
    return abs(sum(w*cmath.exp(sum(n*cmath.log(a+d*t*q) for n,q in groups)) for t,w in NODES))
def metrics(a,groups):
    m=sum(n for n,q in groups);mu=sum(n*q for n,q in groups)/m;u=abs(mu)
    v=sum(n*abs(q-mu)**2 for n,q in groups)/m
    z=a*mu;b=1-z
    gamma=v/((m-1)*u*u)
    B2=b**(m+1)+(m+1)*z*b**m+m*(m+1)/2*z*z*b**(m-1)
    # Evaluate small-k H by 1-B, never by a catastrophically cancelling full tail.
    prefixes=[];B=0j
    for j in range(m+1):
        B+=math.comb(m+1,j)*z**j*b**(m+1-j);prefixes.append(1-B)
    H=z**(m+1);tail=0.;terms=[]
    for k in range(m,2,-1):
        if v==0: C=0.
        else:
            ent=0 if k==m else m*math.log(m)-k*math.log(k)-(m-k)*math.log(m-k)
            C=math.exp(.5*(ent+k*math.log(v))-math.lgamma(m+1)+math.lgamma(k+1)+math.lgamma(m-k+1)-k*math.log(u))
        val=C*abs(prefixes[k] if k<=m//2 else H);tail+=val;terms.append((k,val))
        H+=math.comb(m+1,k)*z**k*b**(m+1-k)
    E=abs(b)**(m+1)+gamma*abs(B2)+tail
    return dict(E=E,gamma=gamma,gap=E+gamma-(1-a*u),half_gap=E-(1-a)/2,ratio=E/(1-a),mu=[mu.real,mu.imag],v=v,top_terms=sorted(terms,key=lambda t:-t[1])[:5])
def encode(a,g,label):
    return dict(a=a,m=sum(n for n,q in g),groups=[[n,q.real,q.imag] for n,q in g],family=label,polar=polar(a,g),**metrics(a,g))
def run(count):
    records=[];best={};feasible=0
    for m in [7,8,12,20,50,100,256,512]:
      for a in [.9,.95,.99,.999,1-1e-6]:
       for trial in range(count):
        ng=2+trial%3
        cuts=sorted(R.sample(range(1,m),ng-1));ns=[y-x for x,y in zip([0]+cuts,cuts+[m])]
        angles=[R.uniform(-math.pi,math.pi) for _ in ns]
        radii=[1 if trial%4 else R.uniform(.2,1) for _ in ns]
        # interpolate angles and radii towards q=1 to find a FULLpolar boundary.
        def family(s):return [(n,(1-s*(1-r))*cmath.exp(1j*s*t)) for n,r,t in zip(ns,radii,angles)]
        if polar(a,family(0))<1:continue
        lo,hi=0.,1.
        if polar(a,family(1))>=1:lo=1.
        else:
         for _ in range(38):
          mid=(lo+hi)/2
          if polar(a,family(mid))>=1:lo=mid
          else:hi=mid
        g=family(lo*(1-1e-9));rec=encode(a,g,'boundary_'+str(ng)+'modal');feasible+=1
        for key in ['gap','half_gap','ratio']:
         if key not in best or rec[key]>best[key][key]:best[key]=rec
        records.append(rec)
       print(m,a,'best ratio',best.get('ratio',{}).get('ratio'),flush=True)
       (OUT/'search_results.json').write_text(json.dumps(dict(seed=9142026,feasible=feasible,best=best,records=records),indent=2))
    print(json.dumps(best,indent=2))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--count',type=int,default=30);run(p.parse_args().count)
