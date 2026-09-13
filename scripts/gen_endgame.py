import sympy as sp

a = sp.symbols('a')
g = 300 + 47*a - a**2
T1cf = sp.Rational(1600000, 721)*(100-2*a)**2*(3+a)**3/g**4
terms = [sp.Rational(1, 6), 1/(4*(3+a)), sp.Rational(1, 200), 1/(400*(3+a)),
         sp.Rational(101, 100)*T1cf,
         (100-2*a)**2/100*101*99/(16*(3+a)) * (a/(3+a))**48]
Ut = sum(terms)

# The multiplier D = Lp (3+a)^49 g^4.  Lp is chosen so that *every* term of Ut, multiplied
# by D, is an integer polynomial -- not merely their sum.  (With the smaller multiplier the
# last term alone carries a factor 1/4.)
Dbase = (3+a)**49 * g**4
Fq = sp.Poly(sp.expand(sp.simplify(Dbase * (1 - Ut))), a, domain=sp.QQ)
L = sp.ilcm(*[sp.Rational(x).q for x in Fq.all_coeffs()])
Lp = L
print(f"L = {L}, Lp = {Lp}")

# each term of Ut, times D, in *natural* (unexpanded) form
nat = []
for t in terms:
    q = sp.simplify(sp.cancel(Lp*Dbase*t))
    nat.append(sp.factor(q))
    assert sp.simplify(q - Lp*Dbase*t) == 0

F = sp.Poly(sp.expand(sp.cancel(sp.together(Lp * Dbase * (1 - Ut)))), a)
d = F.degree()
cf = [F.coeff_monomial(a**i) for i in range(d+1)]
assert all(sp.Rational(x).is_Integer for x in cf), "F is not integral"
cf = [sp.Integer(x) for x in cf]
G = [sum(cf[i]*sp.binomial(d-i, m-i)*17**i for i in range(m+1)) for m in range(d+1)]
assert all(x > 0 for x in G), "certificate not all-positive"
assert sp.expand(17**d*F.as_expr() - sum(G[m]*a**m*(17-a)**(d-m) for m in range(d+1))) == 0
for i in range(0, 171):
    v = sp.Rational(i, 10)
    assert Ut.subs(a, v) < 1, f"Ut({v}) >= 1"
    assert F.as_expr().subs(a, v) > 0, f"F({v}) <= 0"

# the constants of the six per-term identities, read off rather than hand-derived
k16 = sp.simplify(nat[0] / (Dbase))
k4 = sp.simplify(nat[1] / ((3+a)**48 * g**4))
k200 = sp.simplify(nat[2] / (Dbase))
k400 = sp.simplify(nat[3] / ((3+a)**48 * g**4))
kT1 = sp.simplify(nat[4] / ((100-2*a)**2 * (3+a)**52))
kT2 = sp.simplify(nat[5] / ((100-2*a)**2 * a**48 * g**4))
def lean_const(k):
    k = sp.Rational(k)
    assert k > 0
    return str(k.p) if k.q == 1 else f"({k.p} / {k.q})"


for nm, k in (("1/6", k16), ("1/(4(3+a))", k4), ("1/200", k200), ("1/(400(3+a))", k400),
              ("T1", kT1), ("T2", kT2)):
    assert sp.Rational(k).is_Rational, f"{nm} constant not rational: {k}"
print("  constants:", k16, k4, k200, k400, kT1, kT2)
k16, k4, k200, k400, kT1, kT2 = map(lean_const, (k16, k4, k200, k400, kT1, kT2))
print(f"degree {d}; |G| up to {max(len(str(x)) for x in G)} digits;  ALL CHECKS PASS")

G4 = "(300 + 47 * α - α ^ 2) ^ 4"
DD = f"{Lp} * (3 + α) ^ 49 * {G4}"
# the factor left over after 721 * γ⁴ is cancelled out of `101/100 * D`
kT1div = sp.Rational(101, 100) * Lp / 721
assert kT1div.is_Integer, kT1div
kT1div = int(kT1div)


def poly(cs, var="α"):
    ts = []
    for i, v in enumerate(cs):
        v = sp.Integer(v)
        if v == 0:
            continue
        s = ("+ " if v > 0 else "- ") + str(abs(v))
        if i == 1:
            s += f" * {var}"
        elif i > 1:
            s += f" * {var} ^ {i}"
        ts.append(s)
    t = " ".join(ts)
    return t[2:] if t.startswith("+ ") else "-" + t[2:]


P = poly(cf)
bern = " + ".join((f"{G[0]} * (17 - α) ^ {d}" if m == 0 else
                   f"{G[d]} * α ^ {d}" if m == d else
                   f"{G[m]} * α ^ {m} * (17 - α) ^ {d-m}") for m in range(d+1))


src = f'''/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.LargeDegree.Monotone
import Sendov.Common.BernsteinCert
import Sendov.Common.BernsteinRing

/-!
# The large-degree claim

`Sendov.U_le_Ut` removed the degree from the bound; what is left is the single inequality
`Ut α < 1` on `0 ≤ α ≤ 17`, and then `R n α < 1` for every `n ≥ 101`.

`Ut` is a rational function of `α` times `(α/(3+α)) ^ 48`, so multiplying by

  `D = {Lp} · (3+α) ^ 49 · γ ^ 4`,   `γ = 300 + 47α - α²`,

which is positive on `[0,17]`, turns the claim into positivity of the single polynomial
`F = D (1 - Ut)` of degree `{d}`.  The two closed forms used are

  `c 101 α = γ / (100 (3+α))`,
  `T1 101 α = 1600000 (100-2α)² (3+α)³ / (721 γ⁴)`.

A Bernstein certificate on `[0,17]` settles it: all {d+1} coefficients of `F` in the basis
`α^m (17-α)^({d}-m)` are positive, so no subdivision of the `α`-range is needed.  (The
informal write-up splits at `α = 16` and estimates the two pieces separately; that is not
necessary once the sharp Beta constant is used, which is what leaves the margin — `Ut` peaks
at `α = 17` with value `0.9229`.)

## Why the multiplication is distributed by hand

`D (1 - Ut)` must not be handed to `field_simp`: it would clear `(3+α) ^ 49` and `γ ⁴` from
both sides at once, leaving `ring` a degree-115 identity that it does not close.  `D` already
*contains* exactly those denominators, so each of the six terms of `Ut` cancels against it
separately.  Doing that first (`Sendov.Ut_lt_one`, steps `t1`–`t6`, and `h48` for the `48`-th
power) keeps every `ring` call at degree at most `{d+4}`, which is the same size as the
certificate identity itself.  `{Lp}` rather than `{L}` is used as the multiplier so that
each term separately, not merely their sum, comes out with integer coefficients.

## Main statements

* `Sendov.Ut_lt_one`: `Ut α < 1` on `0 ≤ α ≤ 17`;
* `Sendov.large_degree`: `R n α < 1` for `n ≥ 101`.
-/

namespace Sendov

variable {{α : ℝ}}

set_option maxHeartbeats 4000000 in
-- a degree-{d} identity in one variable; `ring` needs more than the default budget
/-- The Bernstein certificate: `F` is positive on `[0,17]`. -/
lemma F_pos (hα : 0 ≤ α) (hα' : α ≤ 17) :
    0 < {P} := by
  have hu : (0 : ℝ) ≤ 17 - α := by linarith
  have hid : (17 : ℝ) ^ {d} * ({P}) = {bern} := by
    bernstein_ring α (17 - α)
  bernstein_cert α (17 - α) using hid

set_option maxHeartbeats 4000000 in
/-- **The bound in `α` alone is below `1`.** -/
theorem Ut_lt_one (hα : 0 ≤ α) (hα' : α ≤ 17) : Ut α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hg : (0 : ℝ) < 300 + 47 * α - α ^ 2 := by nlinarith
  have hgne : (300 : ℝ) + 47 * α - α ^ 2 ≠ 0 := hg.ne'
  have hc : c 101 α = (300 + 47 * α - α ^ 2) / (100 * (3 + α)) := by
    simp only [c, M]
    norm_num
    field_simp
    ring
  have hT1 : T1 101 α
      = 1600000 * (100 - 2 * α) ^ 2 * (3 + α) ^ 3 / (721 * (300 + 47 * α - α ^ 2) ^ 4) := by
    simp only [T1, hc]
    norm_num
    field_simp
    ring
  -- `(α/(3+α)) ^ 48` cancels against `(3+α) ^ 49` without expanding either
  have h48 : (α / (3 + α)) ^ 48 * (3 + α) ^ 49 = α ^ 48 * (3 + α) := by
    rw [div_pow, pow_succ (3 + α) 48, ← mul_assoc,
      div_mul_cancel₀ _ (pow_ne_zero 48 h3.ne')]
  -- The six terms of `Ut`, each multiplied by `D`. Composite powers are kept
  -- as scalar factors: cancel denominators first, then normalize only the coefficients.
  have t1 : (1 / 6 : ℝ) * ({DD}) = {k16} * (3 + α) ^ 49 * {G4} := by
    norm_num [← mul_assoc]
  have t2 : 1 / (4 * (3 + α)) * ({DD}) = {k4} * (3 + α) ^ 48 * {G4} := by
    rw [pow_succ (3 + α) 48]
    -- Remove the single factor `3 + α`; the remaining powers stay opaque.
    generalize (3 + α) ^ 48 = p, {G4} = g
    field_simp
    ring
  have t3 : (1 / 200 : ℝ) * ({DD}) = {k200} * (3 + α) ^ 49 * {G4} := by
    norm_num [← mul_assoc]
  have t4 : 1 / (400 * (3 + α)) * ({DD}) = {k400} * (3 + α) ^ 48 * {G4} := by
    rw [pow_succ (3 + α) 48]
    -- Remove the single factor `3 + α`; the remaining powers stay opaque.
    generalize (3 + α) ^ 48 = p, {G4} = g
    field_simp
    ring
  have t5 : 101 / 100 * (1600000 * (100 - 2 * α) ^ 2 * (3 + α) ^ 3
        / (721 * {G4})) * ({DD})
      = {kT1} * (100 - 2 * α) ^ 2 * (3 + α) ^ 52 := by
    -- Combine exponents by `pow_add`, and cancel only the scalar denominator γ⁴.
    rw [show (3 + α) ^ 52 = (3 + α) ^ 3 * (3 + α) ^ 49 from pow_add _ 3 49]
    have hg4 := pow_ne_zero 4 hgne
    generalize (100 - 2 * α) ^ 2 = a, (3 + α) ^ 3 = b, (3 + α) ^ 49 = p
    generalize {G4} = g at hg4 ⊢
    field_simp
    ring
  have t6 : (100 - 2 * α) ^ 2 / 100 * 101 * 99 / (16 * (3 + α)) * (α / (3 + α)) ^ 48
        * ({DD})
      = {kT2} * (100 - 2 * α) ^ 2 * α ^ 48 * {G4} := by
    -- First expose the paired powers so that `h48` cancels 48 denominator factors.
    rw [show (100 - 2 * α) ^ 2 / 100 * 101 * 99 / (16 * (3 + α)) * (α / (3 + α)) ^ 48
          * ({DD})
        = ((100 - 2 * α) ^ 2 / 100 * 101 * 99 / (16 * (3 + α)) * ({Lp} * {G4}))
          * ((α / (3 + α)) ^ 48 * (3 + α) ^ 49) from by
            -- This is only reassociation of scalar factors, not a polynomial identity.
            generalize (100 - 2 * α) ^ 2 / 100 * 101 * 99 / (16 * (3 + α)) = a,
              (α / (3 + α)) ^ 48 = b, (3 + α) ^ 49 = p,
              {G4} = g
            ring, h48]
    -- Only one factor `3 + α` remains to cancel; do not expand α⁴⁸ or γ⁴.
    generalize (100 - 2 * α) ^ 2 = a, α ^ 48 = p, {G4} = g
    field_simp
    ring
  have hD : (0 : ℝ) < {DD} := by
    have h49 := pow_pos h3 49
    have hg4 := pow_pos hg 4
    positivity
  have hmul : (1 - Ut α) * ({DD}) = {P} := by
    rw [Ut, hT1, sub_mul, one_mul, add_mul, add_mul, add_mul, add_mul, add_mul,
      t1, t2, t3, t4, t5, t6]
    ring
  rw [← sub_pos]
  have hF := F_pos hα hα'
  nlinarith [hmul, hF, hD]

/-- **The large-degree claim.**  Every degree `n ≥ 101`. -/
theorem large_degree {{n : ℕ}} (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17)
    (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have hcpos : (0 : ℝ) < c n α := by
    have := c_ge_of_large hn hα hα'
    linarith
  exact lt_of_le_of_lt
    (le_trans (R_le_U (by omega) hα hfeas hcpos) (U_le_Ut hn hα hα'))
    (Ut_lt_one hα hα')

end Sendov
'''
# Resolve relative to this checkout; --output supports isolated regeneration checks.
import argparse
from pathlib import Path
parser = argparse.ArgumentParser()
parser.add_argument("--output", type=Path,
                    default=Path(__file__).resolve().parents[1] / "Sendov/LargeDegree/Endgame.lean",
                    help="Output Lean file; overwrites it if present. Default: this checkout's Endgame.lean.")
output = parser.parse_args().output
output.parent.mkdir(parents=True, exist_ok=True)
with output.open("w", encoding="utf-8", newline="\n") as stream:
    stream.write(src)
print(f"written Endgame.lean, {len(src.encode('utf-8'))} bytes")
