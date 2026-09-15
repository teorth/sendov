"""Exploration of a necessary moment relaxation; NOT FULLpolar feasibility."""
import json, math
import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq, differential_evolution
from numpy.polynomial.legendre import leggauss
from pathlib import Path
T,W=leggauss(64);T=(T+1)/2;W=W/2

def normint(m,a,x,s):
    d=1-a*a
    return W@((a*a+2*a*d*x*T+d*d*s*T*T)**(m/2))
def xmin(m,a,s):
    if normint(m,a,1,s)<1:return float('nan')
    return brentq(lambda x:normint(m,a,x,s)-1,0,1)
def bound(m,a,x,u,v):
    z=complex(a*x,a*math.sqrt(max(0,u*u-x*x))); w=abs(1-z)
    B=(1-z)**(m+1)+(m+1)*z*(1-z)**m+m*(m+1)/2*z*z*(1-z)**(m-1)
    P=w**(m-1)*(w*w+(m+1)*a*u*w+m*(m+1)*a*a*u*u/2)
    S=2.25-2/(m-1)-.5/(m*(m-1));D=m*(m-1)*(m-2)
    I=W@(T**3*np.maximum(0,1-2*a*x*T+a*a*(u*u+v)*T*T)**((m-3)/2))
    tail=math.sqrt(S)*(m+1)*a**4*u*v**1.5*math.sqrt(D)*I
    gamma=v/((m-1)*u*u)
    budget=1-a*u
    return {'ratio':(w**(m+1)+gamma*(1+P)+tail)/budget,'exactB_ratio':(w**(m+1)+gamma*(1+abs(B))+tail)/budget,'tail':tail,'gamma':gamma,'P':P,'w':w,'budget':budget}

def optimize(m, seed=42):
    def parse(p):
        a=.9+(1-1/(3*m)-.9)*p[0]
        # x parameter interpolates above actual s=1 norm threshold;
        # s then interpolates [u^2,1], with constraints retained below.
        xm=xmin(m,a,1)
        x=xm+(1-xm)*p[1]
        u=x+(1-x)*p[2]
        v=(1-u*u)*p[3]
        return a,x,u,v
    def obj(p):
        a,x,u,v=parse(p)
        pol=normint(m,a,x,u*u+v)
        if pol<1-1e-12:return 1e3*(1-pol)
        return -bound(m,a,x,u,v)['ratio']
    r=differential_evolution(obj,[(0,1)]*4,tol=1e-8,popsize=15,maxiter=350,seed=seed)
    a,x,u,v=parse(r.x)
    return dict(m=m,a=a,x=x,u=u,v=v,s=u*u+v,polar_norm=normint(m,a,x,u*u+v),**bound(m,a,x,u,v))
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--opt',action='store_true');args=p.parse_args()
    rows=[]
    for m in [7,10,15,20,30,44]:
        a=.9;x=xmin(m,a,1);u=x;v=1-x*x
        row=optimize(m) if args.opt else dict(m=m,a=a,x=x,u=u,v=v,s=1,polar_norm=normint(m,a,x,1),b=1-2*a*x+a*a,**bound(m,a,x,u,v))
        rows.append(row);print(json.dumps(row),flush=True)
    Path(__file__).with_name('probe-results.json').write_text(json.dumps(rows,indent=2))
