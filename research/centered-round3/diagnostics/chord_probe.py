"""Search two chord envelopes on the same explicitly labeled relaxations."""
import json,math
from scipy.optimize import differential_evolution
from relaxation import ROOT,T,W,moments,evaluate

def metrics(p):
 r=evaluate(p);m,a,h,l,b,x,y,u,v,s=moments(p)
 d=1-math.sqrt(b);S=9/4-2/(m-1)-1/(2*m*(m-1));D=m*(m-1)*(m-2)
 betaI=float(W@(T**3*(1-2*a*x*T+a*a*s*T*T)**((m-3)/2)))
 P=math.sqrt(S*D)*(m+1)*a**4*u*v**1.5
 base=r['R_ratio']-P*betaI/(1-a*u)
 r['extended_chord_ratio']=base+6*math.sqrt(S)*a**4*u*v**1.5/(d**4*math.sqrt(D)*(1-a*u))
 r['finite_chord_ratio']=base+P*float(W@(T**3*(1-d*T)**(m-3)))/(1-a*u)
 return r

def run():
 records=[]
 for tier in ['rational','chord','norm_integral']:
  for objective in ['extended_chord_ratio','finite_chord_ratio']:
   def fun(p):
    r=metrics(p);c=1 if tier=='rational' else r['chord' if tier=='chord' else 'polar_norm']
    return -r[objective]+10000*max(0,1-c)
   opt=differential_evolution(fun,[(7,44)]+[(0,1)]*4,integrality=[True,False,False,False,False],seed=8711,popsize=10,maxiter=400,tol=1e-9,polish=True)
   rec=dict(tier=tier,objective=objective,parameters=opt.x.tolist(),evaluations=opt.nfev,diagnostic=metrics(opt.x));records.append(rec)
   (ROOT/'chord_results.json').write_text(json.dumps(records,indent=2));print(json.dumps(rec),flush=True)
if __name__=='__main__':run()
