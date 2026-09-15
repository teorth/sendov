"""Two-precision replay of moment diagnostics; no interval/global certificate."""
from pathlib import Path
import json
import mpmath as mp
ROOT=Path(__file__).resolve().parent

def calc(p,dps):
 mp.mp.dps=dps;m=int(round(p[0]));p=[mp.mpf(str(x)) for x in p]
 lam=mp.mpf(1)/3+(mp.mpf(m)/10-mp.mpf(1)/3)*p[1];a=1-lam/m
 b=(1-a)**2+(lam/(3+lam)-(1-a)**2)*p[2];x=(1+a*a-b)/(2*a)
 u2=x*x+(1-x*x)*p[3];u=mp.sqrt(u2);y=mp.sqrt(u2-x*x)
 v=min(1-u2,lam*u2/3)*p[4];s=u2+v;mu=mp.mpc(x,y);z=a*mu;w=abs(1-z)
 delta=1-a*a;end=mp.sqrt(a*a+2*a*delta*x+delta*delta*s)
 chord=sum(a**j*end**(m-j) for j in range(m+1))/(m+1)
 norm=mp.quad(lambda t:(a*a+2*a*delta*x*t+delta*delta*s*t*t)**(mp.mpf(m)/2),[0,mp.mpf('.5'),1])
 S=mp.mpf(9)/4-mp.mpf(2)/(m-1)-mp.mpf(1)/(2*m*(m-1));D=m*(m-1)*(m-2)
 I=mp.quad(lambda t:t**3*(1-2*a*x*t+a*a*s*t*t)**(mp.mpf(m-3)/2),[0,mp.mpf('.5'),1])
 P=w**(m-1)*(w*w+(m+1)*a*u*w+mp.mpf(m*(m+1))/2*a*a*u*u)
 gamma=v/((m-1)*u2);E0=w**(m+1);budget=1-a*u
 terms=[mp.binomial(m+1,j)*z**j*(1-z)**(m+1-j) for j in range(m+2)]
 tail=mp.mpf(0)
 for k in range(3,m+1):
  H=1-sum(terms[:k+1]) if k<=m//2 else sum(terms[k+1:])
  C=mp.sqrt(v**k*(1 if k==m else mp.mpf(m)**m/(mp.mpf(k)**k*mp.mpf(m-k)**(m-k))))
  tail+=C/mp.binomial(m,k)/u**k*abs(H)
 tailR=mp.sqrt(S*D)*(m+1)*a**4*u*v**mp.mpf('1.5')*I
 d=1-mp.sqrt(b)
 ext=6*mp.sqrt(S)*a**4*u*v**mp.mpf('1.5')/(d**4*mp.sqrt(D))
 return {k:mp.nstr(v,dps) for k,v in dict(R_ratio=(E0+gamma*(1+P)+tailR)/budget,
    original_ratio=(E0+gamma*(1+abs(sum(terms[:3])))+tail)/budget,
    extended_chord_ratio=(E0+gamma*(1+P)+ext)/budget,chord_margin=chord-1,polar_norm_margin=norm-1,
    mean_imag=y,variance=v,second_moment=s).items()}

def main():
 records=json.loads((ROOT/'relaxation_results.json').read_text());out=[]
 for i,r in enumerate(records):
  checks=[calc(r['parameters'],80),calc(r['parameters'],140)]
  mp.mp.dps=140
  for k in checks[0]:assert abs(mp.mpf(checks[0][k])-mp.mpf(checks[1][k]))<mp.mpf('1e-65'),(i,k)
  out.append(dict(input=r,checks=checks))
  (ROOT/'high_precision.json').write_text(json.dumps(out,indent=2))
  print(i,r['tier'],r['objective'],'R',checks[1]['R_ratio'][:22],'original',checks[1]['original_ratio'][:22],'extended',checks[1]['extended_chord_ratio'][:22],flush=True)
 print('replayed',len(out),'literal optimizer inputs at80/140dps; no q-family FULLpolar certification')
if __name__=='__main__':main()
