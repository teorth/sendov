"""Deterministic stochastic local maximization under FULLpolar constraints.
Not a global optimum certificate; records rejected feasibility and actual goals.
"""
from search import R,polar,metrics,OUT
import math,cmath,json

def evaluate(m,h,ns,angles,radii):
 a=1-h
 def fam(s):return [(n,(1-s*(1-r))*cmath.exp(1j*s*t)) for n,t,r in zip(ns,angles,radii)]
 if polar(a,fam(0))<1:return None
 lo,hi=0.,1.
 if polar(a,fam(1))>=1:lo=1.
 else:
  for _ in range(40):
   mid=(lo+hi)/2
   if polar(a,fam(mid))>=1:lo=mid
   else:hi=mid
 g=fam(lo*(1-1e-5));K=polar(a,g)
 if K<1:return None
 met=metrics(a,g);budget=1-a*abs(complex(*met['mu']))
 return dict(m=m,a=a,groups=[[n,z.real,z.imag] for n,z in g],polar=K,slack_ratio=(met['E']+met['gamma'])/budget,gap_over_h=met['gap']/h,**met)
def run():
 records=[];evals=0
 for m in [7,8,12,20,24,50,100,256,512]:
  for objective in ['ratio','slack_ratio','gap_over_h']:
   best=None;state=None
   for start in range(4):
    ng=2+start%3;cuts=sorted(R.sample(range(1,m),ng-1));ns=[y-x for x,y in zip([0]+cuts,cuts+[m])]
    angles=[R.uniform(-2,2) for n in ns];radii=[1.]*ng;h=.1
    rec=evaluate(m,h,ns,angles,radii);evals+=1
    for step in range(120):
     sigma=.5*(.015/.5)**(step/120)
     hh=min(.1,max(1e-6,h*math.exp(R.gauss(0,sigma))))
     aa=[max(-math.pi,min(math.pi,t+R.gauss(0,sigma))) for t in angles]
     rr=[min(1,max(.1,r+R.gauss(0,sigma/3))) if step%3==0 else r for r in radii]
     nn=ns[:]
     if step%4==0:
      i,j=R.sample(range(ng),2)
      if nn[i]>1:nn[i]-=1;nn[j]+=1
     cand=evaluate(m,hh,nn,aa,rr);evals+=1
     if cand is not None and (rec is None or cand[objective]>rec[objective]):h,ns,angles,radii,rec=hh,nn,aa,rr,cand
    if rec is not None and (best is None or rec[objective]>best[objective]):best=rec
   records.append(dict(objective=objective,best=best))
   (OUT/'optimization_results.json').write_text(json.dumps(dict(seed=9142026,evaluations=evals,records=records),indent=2))
   print(m,objective,best[objective],flush=True)
if __name__=='__main__':run()
