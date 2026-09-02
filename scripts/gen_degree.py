#!/usr/bin/env python3
"""Certificate generator for the Sendov finite-range claim.

UNTRUSTED.  Nothing this script emits is believed by the Lean development on its
own authority: Lean re-derives the polynomial `P n` from `Sendov.mom` and checks the
Bernstein identity with `ring`, so a wrong coefficient makes the build fail rather
than the theorem weaken.  The checks below exist to catch generator bugs early, not
to license trusting the output.

  python gen_degree.py --check          validate P n against numerical quadrature
  python gen_degree.py <n>              emit Degree<n>.lean

A worked example of why `--check` matters: an early version of `Ppoly` dropped the
factor `2^l` in `(-2c)^l` (the `2^l` cancels against the denominator of `c`, so the
denominator is `M^i`, not `(2M)^l M^(i-l)`).  The resulting `P` was wrong by a sign
and scale, yet still admitted a Bernstein representation -- with every coefficient
negative.  Positivity of the certificate is therefore NOT evidence that `P` is right;
only agreement with an independent evaluation of `1 - R` is.
"""
from fractions import Fraction as F
from math import comb, lcm

def mul(p,q):
    r=[F(0)]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        if x:
            for j,y in enumerate(q): r[i+j]+=x*y
    return r
def add(*ps):
    n=max(len(p) for p in ps); r=[F(0)]*n
    for p in ps:
        for i,x in enumerate(p): r[i]+=x
    return r
def smul(s,p): return [s*x for x in p]
def powp(p,k):
    r=[F(1)]
    for _ in range(k): r=mul(r,p)
    return r
def Ppoly(n):
    # n = 5 is excluded: this uses the odd-degree tangent bound with w = 1, which
    # overshoots in degree five (it gives an upper bound of 1.0625 at alpha = 0 and
    # so proves nothing).  Degree five is done separately in Lean with w = 1/3; see
    # `Sendov.FiniteRange.Degree5`.
    assert n >= 6, "degree 5 needs w = 1/3; see Sendov/FiniteRange/Degree5.lean"
    M=n-1; Nc=[F(6*M),F(M-6),F(-2)]; NA=[F(M),F(-2)]; sh=[F(3),F(1)]
    def mom(k):
        N=[F(0)]
        for i in range(k+1):
            for l in range(i+1):
                coef=F(comb(k,i)*comb(i,l)*(-1)**l, 2*i-l+4)*F(1, M**i)
                N=add(N, smul(coef, mul(powp(Nc,l), mul(powp(NA,i-l), powp(sh,k-l)))))
        return N
    if n%2==0: k=(n-4)//2; N=mom(k); K=k
    else: k=(n-5)//2; N=add(smul(F(1,2),mom(k+1)), smul(F(1,2),mul(mom(k),sh))); K=k+1
    b1=F(1,6)+F(1,2*M); b0=F(1,4)+F(1,4*M)
    num=add(powp(sh,K+1), smul(F(-1), mul(add(smul(b1,sh),[b0]), powp(sh,K))),
            smul(F(-n*M*(n-2),4*M*M), mul(powp(NA,2), N)))
    L=lcm(*[c.denominator for c in num])
    ints=[int(c*L) for c in num]
    while len(ints)>1 and ints[-1]==0: ints.pop()
    return ints, L, K+1


def _check():
    """Validate P n against numerical quadrature of 1 - R n alpha."""
    import numpy as np
    X, W = np.polynomial.legendre.leggauss(600); T = 0.5*(X+1); W = 0.5*W
    def Rnum(n, al):
        M = n-1.0; A = 1-2*al/M; c = 1-al/M-al/(2*(3+al)); Q = 1-2*c*T+A*T*T
        if n % 2 == 0: J = np.sum(W*T**3*np.maximum(Q,0)**((n-4)//2))
        else:
            k = (n-5)//2; J = (np.sum(W*T**3*Q**(k+1))+np.sum(W*T**3*Q**k))/2
        return 1/6+1/(4*(3+al))+1/(2*M)+1/(4*M*(3+al))+A**2*n*M*(n-2)/(4*(3+al))*J
    def ev(cs, x):
        s = F(0)
        for i in range(len(cs)-1, -1, -1): s = s*x+cs[i]
        return s
    bad = 0
    for n in [6,7,8,20,53,97]:
        cf, L, pole = Ppoly(n)
        for al in [0, 5, 17]:
            if al > (n-1)/2: continue
            mine = float(ev(cf, F(al))/L)/(3+al)**pole
            ref = 1-Rnum(n, al)
            ok = abs(mine-ref) < 1e-6
            bad += not ok
            print(f"  n={n:>3} a={al:>2}: P/D={mine:>10.6f}  1-R={ref:>10.6f}  {'ok' if ok else 'MISMATCH'}")
        d = len(cf)-1
        U = F(17) if F(17) <= F(n-1,2) else F(n-1,2); p, q = U.numerator, U.denominator
        G = [sum(cf[i]*q**(j-i)*comb(d-i,j-i)*p**i for i in range(j+1)) for j in range(d+1)]
        print(f"  n={n:>3} deg={d:>3} Bernstein on [0,{U}] all positive: {all(g>0 for g in G)}")
    raise SystemExit(1 if bad else 0)

if __name__ == "__main__":
    import sys
    if "--check" in sys.argv: _check()
    n = int(sys.argv[1]); M = n-1
    cf, L, pole = Ppoly(n); d = len(cf)-1
    U = F(17) if F(17) <= F(M,2) else F(M,2); p,q = U.numerator, U.denominator
    G = [sum(cf[i]*q**(j-i)*comb(d-i,j-i)*p**i for i in range(j+1)) for j in range(d+1)]
    assert all(g>0 for g in G)
    even = (n%2==0); k = (n-4)//2 if even else (n-5)//2
    NAMES={5:"five",6:"six",7:"seven",8:"eight",20:"twenty"}
    nm = NAMES.get(n, "d%d"%n)
    def wrap(body, indent, width=96):
        out=[]; cur=indent
        for w in body.split(" "):
            if len(cur)+1+len(w) > width and cur.strip():
                out.append(cur.rstrip()); cur = indent+"  "+w
            else: cur = (cur+" "+w) if cur.strip() else cur+w
        out.append(cur.rstrip()); return "\n".join(out).lstrip()
    def poly(cs, var="α"):
        ts=[]
        for i,v in enumerate(cs):
            if v==0: continue
            s=("+ " if v>0 else "- ")+str(abs(v))
            if i==1: s+=" * "+var
            elif i>1: s+=f" * {var} ^ {i}"
            ts.append(s)
        r=" ".join(ts); return r[2:] if r.startswith("+ ") else "-"+r[2:]
    P = poly(cf)
    lin = f"({p} - {q} * α)" if q!=1 else f"({p} - α)"
    def bterm(j):
        if j==0: return f"{G[0]} * {lin} ^ {d}"
        if j==d: return f"{G[d]} * α ^ {d}"
        return f"{G[j]} * α ^ {j} * {lin} ^ {d-j}"
    bern = " + ".join(bterm(j) for j in range(d+1))
    haves = "\n".join(f"  have h{j} : (0:ℝ) ≤ {bterm(j)} :=\n"
                      f"    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα {j})) (pow_nonneg hu {d-j})"
                      if 0<j<d else
                      (f"  have h{j} : (0:ℝ) ≤ {bterm(j)} := by positivity")
                      for j in range(d+1))
    Uc = f"{p}/{q}" if q!=1 else f"{p}"
    pref = F(n*M*(n-2),4)
    if even:
        hk = f"(((({n} : ℕ) : ℝ) - 4) / 2) = (({k} : ℕ) : ℝ)"
        getJ = f"(le_of_eq (integral_eq_mom {k} hk))"; Jtxt = f"mom {n} α {k}"
    else:
        hk = f"(((({n} : ℕ) : ℝ) - 4) / 2) = (({k} : ℕ) : ℝ) + 1 / 2"
        getJ = f"(integral_le_mom hfeas {k} hk one_pos)"
        Jtxt = f"(mom {n} α {k+1} / (2 * 1) + 1 / 2 * mom {n} α {k})"
    alphyp = "(hα' : α ≤ 17) " if U==17 else ""
    ubound = "hα'" if U==17 else "h"
    src = f'''/-
    Copyright (c) 2026 Terence Tao. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Terence Tao
    -/
    import Sendov.FiniteRange.Reduce

    /-!
    # The finite-range claim in degree {n}

    Generated from the certificate generator; see `Sendov.FiniteRange.Degree20` for the shape
    of the argument.  Here `k = {k}`, `deg P = {d}`, and the Bernstein certificate on `[0, {Uc}]`
    has {d+1} positive coefficients.
    -/

    set_option maxRecDepth 100000
    set_option maxHeartbeats 2000000

    namespace Sendov

    open MeasureTheory

    variable {{α : ℝ}}

    lemma M_{nm} : M {n} = {M} := by norm_num [M]

    lemma A_{nm} (α : ℝ) : A {n} α = 1 - 2 * α / {M} := by
      rw [A, M]; push_cast; ring

    lemma c_{nm} (α : ℝ) : c {n} α = 1 - α / {M} - α / (2 * (3 + α)) := by
      rw [c, M]; push_cast; ring

    lemma c_{nm}' (hα : 0 ≤ α) :
        c {n} α = ({6*M} + {M-6} * α - 2 * α ^ 2) / ({2*M} * (3 + α)) := by
      have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
      rw [c_{nm}]; field_simp; ring

    /-- Bernstein certificate for the degree-{n} numerator on `[0, {Uc}]`. -/
    lemma P_{nm}_pos (hα : 0 ≤ α) (hle : α ≤ {Uc}) :
        0 < {wrap(P, "    ")} := by
      have hu : (0 : ℝ) ≤ {lin[1:-1]} := by linarith
    {haves}
      have hid : ({p} : ℝ) ^ {d} * ({wrap(P, "      ")})
          = {wrap(bern, "        ")} := by
        ring
      rcases le_total α ({Uc} / 2) with h | h
      · have hpos : (0 : ℝ) < {G[0]} * {lin} ^ {d} :=
          mul_pos (by norm_num) (pow_pos (by linarith) {d})
        linarith
      · have hpos : (0 : ℝ) < {G[d]} * α ^ {d} :=
          mul_pos (by norm_num) (pow_pos (by linarith) {d})
        linarith

    /-- **The finite-range claim in degree {n}.** -/
    theorem finite_range_{nm} (hα : 0 ≤ α) {alphyp}(hfeas : c {n} α ^ 2 ≤ A {n} α) :
        R {n} α < 1 := by
      have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
      have hMle : α ≤ M {n} / 2 := alpha_le_half_M (n := {n}) (by norm_num) hfeas
      rw [M_{nm}] at hMle
      have hle : α ≤ {Uc} := by linarith [{ubound}]
      have hk : {hk} := by norm_num
      have hR := R_le_of_integral_le (n := {n}) (by norm_num) hα {getJ}
      rw [M_{nm}] at hR
      push_cast at hR
      have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * {M}) + 1 / (4 * {M} * (3 + α))
          + A {n} α ^ 2 * {n} * {M} * ({n} - 2) / (4 * (3 + α)) * {Jtxt}
          = 1 - ({wrap(P, "        ")})
              / ({L} * (3 + α) ^ {pole}) := by
        rw [mom, mom, A_{nm}, c_{nm}' hα] <;> try rw [mom]
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.cast_one]
        norm_num
        field_simp
        ring
      rw [hid] at hR
      have hP := P_{nm}_pos hα hle
      have hq : 0 < ({wrap(P, "      ")})
          / ({L} * (3 + α) ^ {pole}) := div_pos hP (by positivity)
      linarith

    end Sendov
    '''
    io.open(f"Degree{n}.lean","w",encoding="utf-8").write(src)
    print(f"n={n} deg={d} bytes={len(src)} maxGammaDigits={max(len(str(g)) for g in G)}")
