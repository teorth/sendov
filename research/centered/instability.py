"""Regression: complex binomial cancellation can fake huge majorant failures."""
from search import metrics
from high_precision import calc,OUT
import math,json

def run():
 rec=dict(a=.95,m=512,groups=[[61,.6532220977967734,.7571663561926022],[451,.5451898775624406,.8383125893146607]])
 g=[(n,complex(x,y)) for n,x,y in rec['groups']];a=rec['a'];m=rec['m'];mu=sum(n*q for n,q in g)/m;v=sum(n*abs(q-mu)**2 for n,q in g)/m;u=abs(mu);z=a*mu;b=1-z
 H=z**(m+1);tail=0.
 for k in range(m,2,-1):
  ent=0 if k==m else m*math.log(m)-k*math.log(k)-(m-k)*math.log(m-k)
  C=math.exp(.5*(ent+k*math.log(v))-math.lgamma(m+1)+math.lgamma(k+1)+math.lgamma(m-k+1)-k*math.log(u))
  tail+=C*abs(H);H+=math.comb(m+1,k)*z**k*b**(m+1-k)
 hp=calc(rec,300)
 out=dict(input=rec,naive_float_tail=tail,stable_float=metrics(a,g),high_precision=hp,verdict='floating evaluation failure; not a C-near counterexample')
 assert tail>1e100
 assert float(hp['E'])<.025
 (OUT/'instability_regression.json').write_text(json.dumps(out,indent=2));print('naive tail',tail,'actual E',hp['E'][:40])
if __name__=='__main__':run()
