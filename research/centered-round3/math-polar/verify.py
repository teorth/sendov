"""Exact endpoint-moment and continuous-band structural checks."""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json

def mul(A,B):
    C={}
    for (i,j),a in A.items():
        for (k,l),b in B.items():
            key=(i+k,j+l);C[key]=C.get(key,0)+a*b
    return {k:v for k,v in C.items() if v}

def moment_poly():
    # 10*[a^2+2a(1-a^2)(7/10)t+(1-a^2)^2t^2], a=1-h.
    q={(0,0):10,(1,0):-20,(1,1):28,(2,0):10,(2,1):-42,(2,2):40,(3,1):14,(3,2):-40,(4,2):10}
    p={(0,0):1}
    for _ in range(22):p=mul(p,q)
    c=[F(0) for _ in range(89)]
    for (i,j),v in p.items():c[i]+=F(v,(j+1)*10**22)
    assert c[0]==1
    return c

def bernstein(c,length=F(1,10)):
    n=len(c)-1
    return [sum((c[j]*length**j*F(comb(k,j),comb(n,j)) for j in range(k+1)),F(0)) for k in range(n+1)]

def poly_power(base,n):
    c=[F(1)]
    for _ in range(n):
        p=[F(0)]*(len(c)+len(base)-1)
        for i,x in enumerate(c):
            for j,y in enumerate(base):p[i+j]+=x*y
        c=p
    return c

def integrate_power(base,n,weight=0):
    return sum((v/F(j+weight+1) for j,v in enumerate(poly_power(base,n))),F(0))

def main():
    checks=[]
    def check(name,condition):
        assert condition,name
        checks.append(name)
    c=moment_poly();b=bernstein(c[1:])
    check('moment polynomial degree',len(c)==89)
    check('Bernstein count',len(b)==88)
    for j,bi in enumerate(b):check('Bernstein upper bound '+str(j),bi<=-F(23,50))
    # Independently reconstruct the endpoint from both bases.
    check('Bernstein endpoint identity',sum((c[j+1]*F(1,10)**j for j in range(88)),F(0))==b[-1])
    check('Bernstein initial value',b[0]==-F(66,5))
    I=integrate_power([F(1),F(-7,5),F(1)],16,3)
    check('tail integral positive',I>0)
    tail2=(F(3,4)*45)**2*(44*43*42)*I**2
    check('tail bound',tail2<F(433,1000)**2)
    G=F(100,49*34)
    K=G*44**2*F(3,5)**17
    check('Gamma bound',G<F(61,1000))
    check('Gamma B2 bound',K<F(20,1000))
    check('tail budget sum',F(433+61+20,1000)==F(257,500))
    check('final h margin',F(7,10)-F(1,15)-(F(257,500)-F(1,2))*F(44,3)==F(107,250))
    # Actual FULLpolar-feasible conjugate-pair family.
    m=44;a=F(9,10);x=u=F(177,250);v=1-u*u;delta=1-a*a
    P=integrate_power([a*a,2*a*delta*x,delta*delta],22)
    B=1-2*a*x+a*a;budget=1-a*u
    check('actual full complex polar integral',P>1)
    check('variance radical',v==F(31171,62500))
    check('pointwise radical norm',x*x+v==1)
    check('residual lambda',F(1,3)<m*(1-a)<=F(m,10))
    check('residual variance strip',v>(1-a)/m**2)
    check('polar norm endpoint',B==F(1339,2500))
    eta2=1-F(8,9*(m-1))-F(2,9*m*(m-1))
    check('eta lower bound',eta2>F(49,50)**2)
    check('variance root lower bound',v>F(7,10)**2)
    check('endpoint root lower bound',B>F(73,100)**2)
    check('factorial root upper bound',m*(m-1)*(m-2)<282**2)
    L=9*F(49,50)*a**4*u*v*F(7,10)/(F(27,100)**4*282)
    check('extended chord tail alone exceeds target',L>budget)
    check('factorial root lower bound',281**2<m*(m-1)*(m-2))
    I_chord=integrate_power([F(1),-F(27,100)],41,3)
    check('finite chord integral positive',I_chord>0)
    Lfinite=F(3,2)*F(49,50)*45*a**4*u*v*F(7,10)*281*I_chord
    check('finite chord tail alone exceeds target',Lfinite>budget)
    record={'checks_passed':len(checks),'checks':checks,'moment_bernstein':{'polynomial':'(Integral Q(h,t)^22 dt - 1)/h','h_interval':['0','1/10'],'degree':87,'power_coefficients':[str(x) for x in c[1:]],'bernstein_coefficients':[str(x) for x in b]},'tail_integral_J16':str(I),'tail_constant_squared':str(tail2),'actual_family':{'m':m,'a':str(a),'x':str(x),'v':str(v),'full_polar_integral':str(P),'budget':str(budget),'extended_chord_tail_lower_bound':str(L),'finite_chord_tail_lower_bound':str(Lfinite)}}
    cache=Path(__file__).with_name('cache');cache.mkdir(exist_ok=True)
    (cache/'exact-verification.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'checks_passed':len(checks),'bernstein_max':float(max(b)),'tail_constant_squared':float(tail2),'Gamma_constant':float(G),'Gamma_B2_constant':float(K),'proved_margin_h':str(F(107,250)),'actual_FULLpolar_integral':float(P),'extended_chord_tail_lower_bound':float(L),'finite_chord_tail_lower_bound':float(Lfinite),'actual_target_budget':float(budget)},indent=2))
if __name__=='__main__':main()
