"""Independent exact audit; writes exclusively beside this file.
Band moments: exact Newton interpolation with a proved polynomial degree bound.
Tail integrals: centered quadratic antiderivative. No imports of candidate code.
Selected finite structural/witness checks are diagnostics, not degree certificates.
"""
from fractions import Fraction as F
from math import comb, factorial, isqrt
from pathlib import Path
import contextlib
import hashlib
import io
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE = ROOT / 'research/centered-round4/math-residual'
PARAMETERS = [(7,8,'473/500',535708), (9,10,'921/1000',444574),
 (11,12,'449/500',377455), (13,14,'877/1000',327153),
 (15,18,'421/500',506719), (19,22,'203/250',361012),
 (23,28,'31/40',407677), (27,34,'149/200',438549)]
checks=[]
def check(name, truth):
    if not truth: raise AssertionError(name)
    checks.append(name)

def add(a,b):
    c=[F(0)]*max(len(a),len(b))
    for i,v in enumerate(a): c[i]+=v
    for i,v in enumerate(b): c[i]+=v
    return c

def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c

def scale(a,v): return [v*x for x in a]
def power(a,n):
    out=[F(1)]
    for _ in range(n): out=mul(out,a)
    return out

def evaluate(a,x):
    v=F(0)
    for c in reversed(a): v=v*x+c
    return v

def moment_value(n,X,h):
    a=1-h; d=1-a*a
    c=power([a*a,2*a*d*X,d*d],n)
    return sum((v/F(i+1) for i,v in enumerate(c)),F(0))

def moment_newton(n,X):
    # In r=10h, Q^n has degree at most D=4n. D+1 exact values
    # uniquely determine it. Signs are NOT inferred from these node values.
    D=4*n
    values=[moment_value(n,X,F(j,10*D)) for j in range(D+1)]
    differences=[]; row=values
    while row:
        differences.append(row[0]); row=[b-a for a,b in zip(row,row[1:])]
    c=[F(0)]*(D+1); basis=[F(1)]
    for j,delta in enumerate(differences):
        c=add(c,scale(basis,delta/F(factorial(j))))
        basis=mul(basis,[-F(j),F(D)])
    # Polynomial identity checks at additional rational points are redundancy.
    for r in [F(1,7),F(2,9),F(5,11)]:
        check(f'n={n} Newton off-node identity r={r}',evaluate(c,r)==moment_value(n,X,r/10))
    return c

def to_bernstein(c):
    N=len(c)-1
    return [sum((c[j]*F(comb(k,j),comb(N,j)) for j in range(k+1)),F(0)) for k in range(N+1)]

def from_bernstein(b):
    N=len(b)-1; c=[F(0)]*(N+1)
    for k,bk in enumerate(b):
        for j in range(N-k+1):
            c[k+j]+=bk*comb(N,k)*comb(N-k,j)*(-1)**j
    return c

def shifted_tail(p,X):
    # z=y-X: (z+X)^3(z^2+1-X^2)^p, z from -X to 1-X.
    ans=F(0)
    for j in range(p+1):
        for k in range(4):
            exponent=2*j+k+1
            ans+=comb(p,j)*(1-X*X)**(p-j)*comb(3,k)*X**(3-k)*((1-X)**exponent-(-X)**exponent)/exponent
    return ans

def sqrt_bounds(q, digits=60):
    assert q>=0
    den=10**digits; k=isqrt(q.numerator*den*den//q.denominator)
    lo=F(k,den); hi=lo if lo*lo==q else F(k+1,den)
    assert lo*lo<=q<=hi*hi
    return lo,hi

# Gaussian rationals keep all complex polynomial operations exact.
def ga(z,w): return (z[0]+w[0],z[1]+w[1])
def gm(z,w): return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def gs(z,c): return (z[0]*c,z[1]*c)
def gp(z,n):
    a=(F(1),F(0))
    for _ in range(n): a=gm(a,z)
    return a

def norm2(z): return z[0]*z[0]+z[1]*z[1]
def B(m,k,z):
    w=ga((F(1),F(0)),gs(z,-1)); out=(F(0),F(0))
    for j in range(k+1): out=ga(out,gs(gm(gp(z,j),gp(w,m+1-j)),comb(m+1,j)))
    return out

def gaussian_product_integral(q,a):
    d=1-a*a; c=[(F(1),F(0))]
    for z in q:
        out=[(F(0),F(0))]*(len(c)+1)
        for j,cj in enumerate(c):
            out[j]=ga(out[j],gs(cj,a))
            out[j+1]=ga(out[j+1],gs(gm(cj,z),d))
        c=out
    return tuple(sum((z[k]/F(j+1) for j,z in enumerate(c)),F(0)) for k in (0,1))

def structural_diagnostics():
    # Three representative polynomial degrees, including all top branches.
    # The mathematical all-m proof is given in AUDIT.md, not these diagnostics.
    for m in (7,16,34):
        S=F(9,4)-F(2,m-1)-F(1,2*m*(m-1))
        check(f'm={m} telescoping S',S==sum((F(2*k+1,k*(k-1)*(k-2)) for k in range(3,m+1)),F(0)))
        for k in range(3,m+1):
            # H identity as a polynomial in a general complex indeterminate z.
            lhs=[F(1)]+[F(0)]*(m+1)
            for j in range(k+1):
                term=[F(0)]*j+scale(power([F(1),F(-1)],m+1-j),F(comb(m+1,j)))
                lhs=add(lhs,scale(term,-1))
            rhs=[F(0)]*(k+1)+[F((m+1)*comb(m,k)*comb(m-k,j)*(-1)**j,k+j+1) for j in range(m-k+1)]
            check(f'm={m} k={k} general complex H polynomial',lhs==rhs)
            check(f'm={m} k={k} factorial binomial identity',k*(k-1)*(k-2)*comb(m,k)==m*(m-1)*(m-2)*comb(m-3,k-3))
            C2=F(1) if k==m else F(m**m,k**k*(m-k)**(m-k))
            check(f'm={m} k={k} original coefficient incl top',C2 <= (2*k+1)*comb(m,k))
        check(f'm={m} top H is z^(m+1)',B(m,m,(F(2,3),F(1,7)))==ga((F(1),F(0)),gs(gp((F(2,3),F(1,7)),m+1),-1)))
    # Universal polynomial identities, represented by full coefficient arrays.
    n=[F(0),F(1)]; m=add(n,[F(7)])
    lhs=add(add(power(m,3),scale(power(m,2),-6)),add(scale(m,-3),[F(6)]))
    check('L4 shifted cubic identity',lhs==[F(34),F(60),F(15),F(1)])
    check('B2 bracket shifted difference',add(add(power(m,2),scale(m,-3)),[F(-4)])==[F(24),F(11),F(1)])
    # S'(m)=2/(m-1)^2+(2m-1)/(2m^2(m-1)^2)>0; D'=3(m-1)^2-1.
    check('D derivative shift positive',add(scale(power(add(m,[F(-1)]),2),3),[F(-1)])==[F(107),F(36),F(3)])

def witness_checks():
    a=F(9,10); h=1-a
    q=[(F(999,1000),F(0))]*3+[(F(959,1000),F(7,25))]*4
    m=len(q); mu=tuple(sum((z[k] for z in q),F(0))/m for k in (0,1))
    u2=norm2(mu); s=sum((norm2(z) for z in q),F(0))/m; v=s-u2
    full=gaussian_product_integral(q,a)
    check('nonreal actual-family pointwise norms',all(norm2(z)<=1 for z in q))
    check('nonreal actual-family FULLpolar',norm2(full)>1)
    check('nonreal actual-family actual statistics',mu[1]!=0 and 0<v and u2<s<1)
    check('nonreal actual-family lies outside prior kernel regimes',m*h>F(1,3) and v>h/m**2)
    check('nonreal actual variance direct identity',v==sum((norm2(ga(z,gs(mu,-1))) for z in q),F(0))/m)
    z=gs(mu,a); w2=norm2(ga((F(1),F(0)),gs(z,-1)))
    b=1-2*a*mu[0]+a*a
    check('nonreal actual beta identity',w2+a*a*v==1-2*a*mu[0]+a*a*s)
    check('nonreal raw b and variance',b<=m*h/(3+m*h) and v/u2<=m*h/3)
    Gamma=v/((m-1)*u2)
    # Each square-root-C summand is sqrt of one rational, including u powers.
    tail=F(0)
    for k in range(3,m+1):
        C2=v**m if k==m else F(m**m,k**k*(m-k)**(m-k))*v**k
        H=ga((F(1),F(0)),gs(B(m,k,z),-1))
        tail+=sqrt_bounds(C2*norm2(H)/(comb(m,k)**2*u2**k))[1]
    total=sqrt_bounds(w2**(m+1))[1]+Gamma*(1+sqrt_bounds(norm2(B(m,2,z)))[1])+tail
    budget=1-a*sqrt_bounds(u2)[1]
    check('nonreal original-C exact interval margin',total<=budget-h/20)
    check('v=0 FULLpolar witness',gaussian_product_integral([(F(1),F(0))]*7,a)[0]>1)
    check('v=0 original-C margin',h**8<=h-h/20)
    return {'m':m,'a':str(a),'q_types':[[str(x) for x in z] for z in (q[0],q[-1])],
      'multiplicities':[3,4],'mu':[str(x) for x in mu],'s':str(s),'v':str(v),
      'FULLpolar_squared_norm':str(norm2(full)),'original_total_upper':str(total),'budget_lower':str(budget)}

def snapshot():
    paths=[SOURCE/x for x in ('PROOF.md','verify.py','audit.py','cache/exact-verification.json','cache/independent-audit.json')]
    paths += [ROOT/'research'/p for p in (
      'centered-round3/math-polar/PROOF.md','centered-round3/math-polar/verify.py',
      'centered-round2-verified/math-middle/PROOF.md','centered-round2-verified/math-middle/verify.py',
      'centered-round2-verified/math-cutoff45/PROOF.md','centered-round2-verified/math-cutoff45/verify.py',
      'centered-round2-verified/math-bound/PROOF.md','centered-verified/MATH_NOTE.md',
      'centered-round4/review35/AUDIT.md','centered-round4/review35/ISSUES.md')]
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}

def replay_source():
    # Preserve original depth so source root calculation remains correct.
    # __file__ is redirected to this owned directory. All source writes are local.
    logs={}
    for name in ('verify.py','audit.py'):
        out=io.StringIO(); ns={'__name__':'__main__','__file__':str(HERE/name)}
        with contextlib.redirect_stdout(out): exec(compile((SOURCE/name).read_text(),str(SOURCE/name),'exec'),ns)
        logs[name]=out.getvalue()
    # Frozen verifiers were inspected as read-only, no __file__ relative writes.
    for rel in ('centered-round2-verified/math-cutoff45/verify.py','centered-round2-verified/math-middle/verify.py'):
        path=ROOT/'research'/rel; out=io.StringIO()
        with contextlib.redirect_stdout(out): exec(compile(path.read_text(),str(path),'exec'),{'__name__':'__main__','__file__':str(path)})
        logs[rel]=out.getvalue()
    (HERE/'source-replay.json').write_text(json.dumps(logs,indent=2)+'\n')
    return logs

def main():
    before=snapshot(); rows=[]
    for L,U,Xs,tau_n in PARAMETERS:
        X=F(Xs); tau=F(tau_n,10**6); n=U//2; p=(L-3)//2; tag=f'[{L},{U}]'
        c=moment_newton(n,X)  # c is in r=10h.
        check(tag+' c0=1',c[0]==1)
        check(tag+' initial h derivative',10*c[1]==U*(X-1))
        quotient=[10*v for v in c[1:]]
        b=to_bernstein(quotient)
        check(tag+' entire inverse Bernstein identity',from_bernstein(b)==quotient)
        for k,v in enumerate(b): check(tag+f' b{k}<0',v<0)
        check(tag+' closed h endpoint sign',evaluate(c,F(1))<1)
        I=shifted_tail(p,X)
        S=F(9,4)-F(2,U-1)-F(1,2*U*(U-1)); D=U*(U-1)*(U-2)
        T2=S*(U+1)**2*D*I**2*X**2*(1-X**2)
        G=1/((L-1)*X**2); W=2*(1-X); B2=U**2*W**((L-1)//2)
        K=tau+G*(1+B2); delta=X-F(1,15)-F(U,3)*max(F(0),K-F(1,2))
        check(tag+' parameter and signs',L>=7 and L<=U and L%2==1 and U%2==0 and F(0)<X<=F(19,20) and X**2>=F(1,2) and 0<W<1)
        check(tag+' shifted integral positive',I>0)
        check(tag+' positive radical enclosure',0<T2<tau**2)
        check(tag+' convex a endpoint bound',F(181,100)-F(9,5)*X<=W)
        check(tag+' delta>=1/20',delta>=F(1,20))
        rows.append({'L':L,'U':U,'X':str(X),'moment_power_in_r':[str(v) for v in c],
          'moment_bernstein':[str(v) for v in b],'bernstein_max':str(max(b)),
          'tail_integral':str(I),'tail_constant_squared':str(T2),'tau':str(tau),
          'K':str(K),'delta':str(delta)})
        print(json.dumps({'band':[L,U],'bernstein_max':float(max(b)),'delta':float(delta)}),flush=True)
    covered={m for L,U,_,_ in PARAMETERS for m in range(L,U+1)}
    check('eight multi-integer bands',len(rows)==8 and all(U>L for L,U,_,_ in PARAMETERS))
    check('integer coverage exactly 7 through 34',covered==set(range(7,35)))
    check('finite union through cutoff45 start',covered|set(range(35,45))==set(range(7,45)))
    check('cutoff35 margin exceeds global margin',F(107,250)>F(1,20))
    check('cutoff45 margin exceeds global margin',F(14,15)>F(1,20))
    structural_diagnostics(); witness=witness_checks()
    replay_source()
    old=json.loads((HERE/'cache/exact-verification.json').read_text())
    for row,src in zip(rows,old['bands']):
        tag=f"[{row['L']},{row['U']}]"
        check(tag+' source band identity',(row['L'],row['U'],row['X'])==(src['L'],src['U'],src['X']))
        # Independent constructions were completed before reading source records.
        check(tag+' source full moment equality',[F(v)*10**j for j,v in enumerate(row['moment_power_in_r'])]==[F(v) for v in src['moment_power_coefficients']])
        check(tag+' source full Bernstein equality',row['moment_bernstein']==src['moment_bernstein_coefficients'])
        check(tag+' source shifted integral equality',row['tail_integral']==src['tail_integral'])
        check(tag+' source delta equality',row['delta']==src['margin_h'])
    after=snapshot(); check('all inspected source hashes unchanged',before==after)
    result={'status':'PASS','checks_passed':len(checks),'checks':checks,'band_count':len(rows),
      'degree_cover_count':len(covered),'minimum_delta':str(min(F(r['delta']) for r in rows)),
      'global_paper_margin_h':'1/20','bands':rows,'nonreal_actual_witness':witness,
      'source_sha256_before':before,'source_sha256_after':after,
      'scope':'Exact audit plus paper reasoning; not kernel proof or certificate-free formula.'}
    (HERE/'evidence.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','checks_passed','band_count','degree_cover_count','minimum_delta','global_paper_margin_h')}))

if __name__=='__main__': main()
