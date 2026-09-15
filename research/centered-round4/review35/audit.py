"""Independent exact audit. All writes stay beside this script.

Moment construction uses a multinomial sum after integrating t, not the
reviewed script's bivariate repeated multiplication. Bernstein conversion
uses successive finite differences, then a full inverse-basis identity.
"""
from fractions import Fraction as F
from math import comb, isqrt
from pathlib import Path
from typing import Any
from decimal import Decimal, localcontext
import contextlib
import hashlib
import io
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SRC = ROOT / 'centered-round3/math-polar'
checks = []

def check(name, condition):
    if not condition:
        raise AssertionError(name)
    checks.append(name)

def dec(x):
    with localcontext() as c:
        c.prec = 50
        return str(Decimal(x.numerator) / Decimal(x.denominator))

def sqrt_dec(x):
    with localcontext() as c:
        c.prec = 50
        return str((Decimal(x.numerator) / Decimal(x.denominator)).sqrt())

def sqrt_interval(x, digits=80):
    scale=10**digits
    n=isqrt(x.numerator*scale**2//x.denominator)
    low=F(n,scale);high=F(n+1,scale)
    check('rational square-root enclosure',low*low<=x<high*high)
    return low,high

def fingerprint():
    paths = [SRC/'PROOF.md', SRC/'verify.py'] + sorted((SRC/'cache').glob('*'))
    return {str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths if p.is_file()}

def moment_coefficients(n, x):
    # Integrate (a^2 + 2adxt + d^2t^2)^n in t first.
    # With i linear and j quadratic t terms: a^(2n-i-2j)d^(i+2j).
    out = [F(0) for _ in range(4*n+1)]
    for i in range(n+1):
        for j in range(n-i+1):
            k = i+2*j
            r = 2*n-k
            scale = F(comb(n,i)*comb(n-i,j), k+1) * (2*x)**i
            # a^r d^k = (1-h)^r h^k (2-h)^k.
            for b in range(r+1):
                left = (-1)**b * comb(r,b)
                for e in range(k+1):
                    out[k+b+e] += scale*left*(-1)**e*comb(k,e)*2**(k-e)
    return out

def bernstein_by_differences(power, length):
    n = len(power)-1
    # The first element in the j-th forward-difference row is
    # p_j length^j / choose(n,j); reconstruct rows upwards.
    first = [power[j]*length**j/F(comb(n,j)) for j in range(n+1)]
    row = [first[-1]]
    for j in range(n-1,-1,-1):
        lower = [first[j]]
        for value in row:
            lower.append(lower[-1]+value)
        row = lower
    return row

def inverse_bernstein(b):
    n = len(b)-1
    out = [F(0) for _ in range(n+1)]
    for k, bk in enumerate(b):
        for e in range(n-k+1):
            out[k+e] += bk*comb(n,k)*comb(n-k,e)*(-1)**e
    return out

def shifted_quadratic_integral(n):
    # y=r+7/10, q0=r^2+51/100. Integrate on r in [-7/10,3/10].
    result = F(0)
    for j in range(n+1):
        for k in range(4):
            power = 2*j+k+1
            coefficient = comb(n,j)*F(51,100)**(n-j)*comb(3,k)*F(7,10)**(3-k)
            result += coefficient*(F(3,10)**power-(-F(7,10))**power)/power
    return result

def positive_moment(n, a, x, s=F(1)):
    d = 1-a*a
    return sum((F(comb(n,i)*comb(n-i,j),i+2*j+1)*a**(2*n-i-2*j)*(2*x)**i*d**(i+2*j)*s**j
                for i in range(n+1) for j in range(n-i+1)), F(0))

def chord_integral(n, c):
    # Substitute r=1-ct, integrating r^n (1-r)^3 / c^4.
    return sum((F((-1)**j*comb(3,j),n+j+1)*(1-(1-c)**(n+j+1))
                for j in range(4)),F(0))/c**4

def pmul(a,b):
    result=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):result[i+j]+=x*y
    return result

def ppow(a,n):
    result=[F(1)]
    for _ in range(n):result=pmul(result,a)
    return result

def padd(a,b):
    out=[F(0)]*max(len(a),len(b))
    for i,x in enumerate(a):out[i]+=x
    for i,x in enumerate(b):out[i]+=x
    return out

def main():
    before = fingerprint()
    c = moment_coefficients(22,F(7,10))
    check('moment constant',c[0]==1)
    check('moment linear term',c[1]==-F(66,5))
    b = bernstein_by_differences(c[1:],F(1,10))
    check('all 88 Bernstein coefficients',len(b)==88 and all(x<=-F(23,50) for x in b))
    check('full inverse Bernstein polynomial identity',inverse_bernstein(b)==[c[j+1]/10**j for j in range(88)])
    for h in [F(0),F(1,100),F(1,20),F(1,10)]:
        check('moment specialization '+str(h),sum((v*h**j for j,v in enumerate(c)),F(0))==positive_moment(22,1-h,F(7,10)))
    # Exact source replay, with only runtime __file__ redirected to owned output.
    namespace: dict[str, Any]={'__name__':'reviewed_module','__file__':str(HERE/'reviewed_replay.py')}
    exec(compile((SRC/'verify.py').read_text(),str(SRC/'verify.py'),'exec'),namespace)
    check('independent moment agrees with source',c==namespace['moment_poly']())
    check('independent Bernstein agrees with source',b==namespace['bernstein'](c[1:]))
    capture=io.StringIO()
    with contextlib.redirect_stdout(capture):namespace['main']()
    (HERE/'source-replay.json').write_text(capture.getvalue())
    I = shifted_quadratic_integral(16)
    check('independent shifted integral agrees',I==namespace['integrate_power']([F(1),-F(7,5),F(1)],16,3))
    D=44*43*42
    tail2=F(135,4)**2*D*I**2
    G=F(1,34*F(7,10)**2)
    GB=G*44**2*F(3,5)**17
    check('positive-square tail bound',I>0 and tail2<F(433,1000)**2)
    check('Gamma and endpoint constants',G<F(61,1000) and GB<F(20,1000))
    T=F(433+61+20,1000)
    margin=F(7,10)-F(1,15)-(T-F(1,2))*F(44,3)
    check('actual-mean budget margin',margin==F(107,250))
    check('covariance path positive lower bound',F(9,20)-F(19,270)>0)
    # Audit all finite identities used by the coefficient consumer in its band.
    for m in range(7,45):
        Sm=F(9,4)-F(2,m-1)-F(1,2*m*(m-1))
        check('factorial telescoping m='+str(m),sum((F(2*k+1,k*(k-1)*(k-2)) for k in range(3,m+1)),F(0))==Sm)
        for k in range(3,m+1):
            c2=F(m**m,k**k*(m-k)**(m-k)) if k<m else F(1)
            check('original C coefficient '+str((m,k)),c2<=(2*k+1)*comb(m,k))
        check('factorial binomial identity m='+str(m),all(k*(k-1)*(k-2)*comb(m,k)==m*(m-1)*(m-2)*comb(m-3,k-3) for k in range(3,m+1)))
    # Reconstruct normalized H identity as a polynomial in z (before division).
    for m in [7,35,44]:
        for k in range(3,m+1):
            B=[F(0)]*(m+2)
            for j in range(k+1):
                term=[F(0)]*j+[comb(m+1,j)*v for v in ppow([F(1),-F(1)],m+1-j)]
                B=padd(B,term)
            H=[-v for v in B];H[0]+=1
            rhs=[F(0)]*(m+2)
            for r in range(m-k+1):
                rhs[k+1+r]=F((m+1)*comb(m,k)*comb(m-k,r)*(-1)**r,k+r+1)
            check('normalized H polynomial '+str((m,k)),H==rhs)
    a=F(9,10);x=F(177,250);v=1-x*x
    P=positive_moment(22,a,x)
    B=1-2*a*x+a*a
    eta2=F(4,9)*(F(9,4)-F(2,43)-F(1,2*44*43))
    check('exact conjugate family norms and feasibility',v==F(31171,62500) and P>1)
    check('radical enclosure signs',eta2>F(49,50)**2 and v>F(7,10)**2 and F(73,100)**2<B<1 and 281**2<D<282**2)
    lower_ext=9*F(49,50)*a**4*x*v*F(7,10)/(F(27,100)**4*282)
    Ichord=chord_integral(41,F(27,100))
    lower_fin=F(3,2)*F(49,50)*45*a**4*x*v*F(7,10)*281*Ichord
    check('independent finite chord integral',Ichord==namespace['integrate_power']([F(1),-F(27,100)],41,3))
    check('both chord consumers obstructed',lower_fin>1-a*x and lower_ext>1-a*x)
    check('finite chord lower bound exceeds 0.95',lower_fin>F(95,100))
    # Exact interval consumer of the ORIGINAL square-root C on this family.
    z=a*x;w=1-z
    B2=sum((comb(45,j)*z**j*w**(45-j) for j in range(3)),F(0))
    tail_lo=F(0);tail_hi=F(0)
    for k in range(3,45):
        H=sum((comb(45,j)*z**j*w**(45-j) for j in range(k+1,46)),F(0))
        c2=F(44**44,k**k*(44-k)**(44-k))*v**k if k<44 else v**k
        lo,hi=sqrt_interval(c2)
        factor=H/(comb(44,k)*x**k)
        tail_lo+=lo*factor;tail_hi+=hi*factor
    end=w**45+v/(43*x*x)*(1+B2)
    check('original C exact interval closes obstruction family',end+tail_hi<1-z)
    # Feasible zero-variance witness to the local strict-sign typo in (5.3).
    Kzero=((a+1-a*a)**36-a**36)/(36*(1-a*a))
    check('zero-variance all-q=1 FULLpolar witness',Kzero>1)
    check('reviewed source and caches unchanged',fingerprint()==before)
    record={'status':'PASS; paper audit, not kernel verification','checks_passed':len(checks),'checks':checks,'source_sha256':before,
            'moment':{'power_coefficients':[str(x) for x in c], 'bernstein_coefficients':[str(x) for x in b], 'max_index':b.index(max(b)), 'max_exact':str(max(b)), 'max_decimal':dec(max(b)), 'gap_below_minus_23_50':str(-F(23,50)-max(b))},
            'constants':{'J16':str(I),'J16_decimal':dec(I),'tail_squared':str(tail2),'tail_decimal':sqrt_dec(tail2),'Gamma':str(G),'Gamma_decimal':dec(G),'Gamma_B2':str(GB),'Gamma_B2_decimal':dec(GB),'margin_h':str(margin),'path_x_lower':str(F(9,20)-F(19,270))},
            'chord_obstruction':{'FULLpolar':str(P),'FULLpolar_decimal':dec(P),'finite_chord_lower':str(lower_fin),'finite_chord_lower_decimal':dec(lower_fin),'extended_chord_lower':str(lower_ext),'extended_chord_lower_decimal':dec(lower_ext),'budget':str(1-a*x),'original_C_tail_interval':[str(tail_lo),str(tail_hi)],'original_total_ratio_interval':[str((end+tail_lo)/(1-z)),str((end+tail_hi)/(1-z))],'original_C_tail_upper_decimal':dec(tail_hi),'original_total_ratio_upper_decimal':dec((end+tail_hi)/(1-z))},
            'local_strict_sign_issue':{'m':35,'a':'9/10','family':'all q_j=1','v':'0','FULLpolar':str(Kzero),'FULLpolar_decimal':dec(Kzero),'scope':'Only strict Tail < (433/1000)v fails at v=0. Main theorem remains valid.'}}
    (HERE/'evidence.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'status':record['status'],'checks_passed':len(checks),'bernstein_max_index':b.index(max(b)),'bernstein_max':dec(max(b)),'J16':str(I),'tail_constant':sqrt_dec(tail2),'Gamma':dec(G),'Gamma_B2':dec(GB),'margin_h':str(margin),'FULLpolar':dec(P),'finite_chord_lower':dec(lower_fin),'extended_chord_lower':dec(lower_ext),'original_C_tail_upper':dec(tail_hi),'original_total_ratio_upper':dec((end+tail_hi)/(1-z)),'zero_variance_witness_FULLpolar':dec(Kzero),'source_and_caches_unchanged':True},indent=2))

if __name__=='__main__':main()
