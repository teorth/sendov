"""Floating reconnaissance only; no proof role."""
from math import sqrt
import json
from pathlib import Path

def integral(f,n=500):
    return (f(0)+f(1)+sum((4 if j%2 else 2)*f(j/n) for j in range(1,n)))/(3*n)
def xmin(m,a=.9):
    d=1-a*a;lo=0;hi=1
    for _ in range(45):
        x=(lo+hi)/2
        if integral(lambda t:(a*a+2*a*d*x*t+d*d*t*t)**(m/2))<1:lo=x
        else:hi=x
    return lo

def band(L,U,x):
    p=(L-3)/2
    I=integral(lambda t:t**3*(1-2*x*t+t*t)**p)
    D=U*(U-1)*(U-2);S=2.25-2/(U-1)-.5/(U*(U-1))
    uv=x*sqrt(1-x*x) if x>=sqrt(.5) else .5
    T=sqrt(S)*(U+1)*sqrt(D)*I*uv
    G=1/((L-1)*x*x)
    w2=2*(1-x)
    B=U*U*w2**((L-1)/2)
    margin=x-1/15-max(0,T+G*(1+B)-.5)*U/3
    return dict(L=L,U=U,x=x,T=T,G=G,B=B,coeff=T+G*(1+B),margin=margin)
if __name__=='__main__':
    rows=[]
    for L,U in [(7,10),(7,9),(9,13),(10,14),(13,19),(14,20),(19,26),(20,27),(26,34),(27,34)]:
        x=int(xmin(U)*1000)/1000
        r=band(L,U,x);rows.append(r);print(r)
    Path(__file__).with_name('explore.json').write_text(json.dumps(rows,indent=2)+'\n')
