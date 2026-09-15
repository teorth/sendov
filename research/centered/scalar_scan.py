"""Larger raw-polar moment disk; not a FULLpolar feasibility claim.
Even m allows an exact two-point realization of each tested moment pair, but
only the weaker RawPolar condition is enforced in this separate scan.
"""
import math,json
from search import NODES,OUT,metrics

def run():
 best=None;rows=[]
 for m in [8,10,12,16,20,24,32,50,100,256,512]:
  for a in [.9,.925,.95,.975,.99,.999,1-1e-6]:
   d=1-a*a
   def raw(x):return sum(w*(a*a+2*a*d*x*t+d*d*t*t)**(m/2) for t,w in NODES)
   lo,hi=a/2,1.
   for _ in range(48):
    mid=(lo+hi)/2
    if raw(mid)>=1:hi=mid
    else:lo=mid
   x=hi
   for i in range(101):
    y=math.sqrt(1-x*x)*i/100;mu=complex(x,y);u=abs(mu)
    perp=1j*mu/u*math.sqrt(max(0,1-u*u))
    g=[(m//2,mu+perp),(m//2,mu-perp)]
    rec=dict(a=a,m=m,x=x,y=y,raw=raw(x),**metrics(a,g))
    if best is None or rec['ratio']>best['ratio']:best=rec
    rows.append(rec)
   print(m,a,'best',best and best['ratio'],flush=True)
 (OUT/'scalar_results.json').write_text(json.dumps(dict(best=best,records=rows),indent=2));print(best)
if __name__=='__main__':run()
