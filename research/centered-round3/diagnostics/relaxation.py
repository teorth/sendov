"""Locate losses in necessary-moment relaxations; never a FULLpolar certificate.

Run .venv/bin/python relaxation.py. Integers m are searched, not tabulated as a proof.
The objective uses the literal C and endpoints or the uniform factorial envelope.
"""
from pathlib import Path
import math,json,argparse
import numpy as np
from scipy.optimize import differential_evolution
from scipy.special import gammaln
ROOT=Path(__file__).resolve().parent
T,W=np.polynomial.legendre.leggauss(64);T=(T+1)/2;W=W/2

def moments(p):
 m=int(round(p[0]));lam=1/3+(m/10-1/3)*p[1];h=lam/m;a=1-h
 b=h*h+(lam/(3+lam)-h*h)*p[2];x=1-(b-h*h)/(2*a)
 u2=1-(1-x*x)*(1-p[3]);y=math.sqrt(max(0,u2-x*x));u=math.sqrt(u2)
 v=min(1-u2,lam*u2/3)*p[4];s=u2+v
 return m,a,h,lam,b,x,y,u,v,s

def evaluate(p,full=False):
 m,a,h,lam,b,x,y,u,v,s=moments(p);mu=complex(x,y);z=a*mu;w=abs(1-z)
 delta=1-a*a;R=math.sqrt(a*a+2*a*delta*x+delta*delta*s)
 chord=sum(a**j*R**(m-j) for j in range(m+1))/(m+1)
 polar_norm=float(W@(a*a+2*a*delta*x*T+delta*delta*s*T*T)**(m/2))
 gamma=v/((m-1)*u*u);B2=sum(math.comb(m+1,j)*z**j*(1-z)**(m+1-j) for j in range(3))
 P=w**(m-1)*(w*w+(m+1)*a*u*w+m*(m+1)/2*a*a*u*u)
 Sm=9/4-2/(m-1)-1/(2*m*(m-1));D=m*(m-1)*(m-2)
 I=float(W@(T**3*(1-2*a*x*T+a*a*s*T*T)**((m-3)/2)))
 tailR=math.sqrt(Sm*D)*(m+1)*a**4*u*v**1.5*I
 E0=w**(m+1);budget=1-a*u
 out=dict(m=m,a=a,h=h,lam=lam,b=b,mu=[x,y],u=u,v=v,s=s,chord=chord,polar_norm=polar_norm,
          R_ratio=(E0+gamma*(1+P)+tailR)/budget,R_exact_B_ratio=(E0+gamma*(1+abs(B2))+tailR)/budget)
 if full:
  terms=[math.comb(m+1,j)*z**j*(1-z)**(m+1-j) for j in range(m+2)]
  Cs=[];tail=0.;integrand=np.zeros_like(T)
  for k in range(3,m+1):
   H=1-sum(terms[:k+1]) if k<=m//2 else sum(terms[k+1:])
   C=0. if v==0 else math.exp(.5*(k*math.log(v)+(0 if k==m else m*math.log(m)-k*math.log(k)-(m-k)*math.log(m-k))))
   tail+=C/math.comb(m,k)/u**k*abs(H)
   integrand+=C*(a*T)**k*np.abs(1-a*mu*T)**(m-k)
  tailC=(m+1)*a*u*float(W@integrand)
  out.update(original_ratio=(E0+gamma*(1+abs(B2))+tail)/budget,pointwise_C_ratio=(E0+gamma*(1+abs(B2))+tailC)/budget,
             E_ratio_h=(E0+gamma*abs(B2)+tail)/h)
 return out

def run(seeds):
 records=[]
 for tier in ['rational','chord','norm_integral']:
  for objective in ['R_ratio','original_ratio']:
   for seed in range(seeds):
    def fun(p):
     r=evaluate(p,objective=='original_ratio');constraint=1 if tier=='rational' else r['chord' if tier=='chord' else 'polar_norm']
     return -r[objective]+10000*max(0,1-constraint)
    opt=differential_evolution(fun,[(7,44)]+[(0,1)]*4,integrality=[True,False,False,False,False],seed=seed+9187,popsize=10,maxiter=400,tol=1e-9,polish=True)
    rec=dict(tier=tier,objective=objective,seed=seed,parameters=opt.x.tolist(),evaluations=opt.nfev,diagnostic=evaluate(opt.x,True))
    records.append(rec);(ROOT/'relaxation_results.json').write_text(json.dumps(records,indent=2))
    print(json.dumps(rec),flush=True)
 print('completed',len(records),'diagnostic optimizations; no certificate or global maximum asserted')
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--seeds',type=int,default=2);run(p.parse_args().seeds)
