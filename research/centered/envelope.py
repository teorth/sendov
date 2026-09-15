"""Diagnose a finite structural tail envelope (no per-degree constants)."""
import math,json
from search import NODES,OUT

def envelope(m,a,x,u):
 v=max(0.,1-u*u);w=math.sqrt(max(0.,1-2*a*x+a*a*u*u));gamma=v/((m-1)*u*u)
 endpoint=w**(m+1)+gamma*w**(m-1)*(w*w+(m+1)*a*u*w+m*(m+1)/2*a*a*u*u)
 # C_k^2 <= (2k+1) binom(m,k) v^k, via mode/first-moment bound.
 tail=math.sqrt(2.25*m*(m-1)*(m-2))*a**4*u*v**1.5*(m+1)*sum(wt*t**3*(1-2*a*x*t+a*a*t*t)**((m-3)/2) for t,wt in NODES)
 mu=complex(x,math.sqrt(max(0.,u*u-x*x)));z=a*mu;b=1-z
 H3=1-sum(math.comb(m+1,j)*z**j*b**(m+1-j) for j in range(4))
 ent=m*math.log(m)-3*math.log(3)-(m-3)*math.log(m-3)
 term3=math.exp(ent/2)*v**1.5/math.comb(m,3)/u**3*abs(H3)
 tail4=math.sqrt(5/9*m*(m-1)*(m-2)*(m-3))*a**5*u*v*v*(m+1)*sum(wt*t**4*(1-2*a*x*t+a*a*t*t)**((m-4)/2) for t,wt in NODES)
 return dict(endpoint=endpoint,tail=tail,gamma=gamma,budget=1-a*u,ratio=(endpoint+tail+gamma)/(1-a*u),half_ratio=(endpoint+tail)/(1-a),refined_half_ratio=(endpoint+term3+tail4)/(1-a))
def run():
 rows=[]
 for m in [7,8,12,20,24,32,50,100,256,512,1024,4096]:
  for a in [.9,.95,.99,.999,1-1e-6]:
   d=1-a*a;lo,hi=a/2,1.
   for _ in range(52):
    x=(lo+hi)/2
    # Log domain protects large m.
    val=sum(w*math.exp(m/2*math.log(a*a+2*a*d*x*t+d*d*t*t)) for t,w in NODES)
    if val>=1:hi=x
    else:lo=x
   x=hi
   for j in range(101):
    u=x+(1-x)*j/100
    rows.append(dict(m=m,a=a,x=x,u=u,**envelope(m,a,x,u)))
 best=max(rows,key=lambda r:r['ratio'])
 (OUT/'envelope_results.json').write_text(json.dumps(dict(best=best,records=rows),indent=2));print(best,flush=True)
if __name__=='__main__':run()
