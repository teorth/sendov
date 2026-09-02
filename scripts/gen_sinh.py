import sympy as sp, io
from pathlib import Path

y = sp.symbols('y', real=True)
U = y**3 - 10*y**2 + 36*y - 36
V = y**4 + 16*y**2 - 72
W = y**3 + 10*y**2 + 36*y + 36

rows = []
for j in range(9):
    u = sp.Poly(U, y).all_coeffs()[::-1] + [0]*4
    v = sp.Poly(V, y).all_coeffs()[::-1] + [0]*5
    w = sp.Poly(W, y).all_coeffs()[::-1] + [0]*4 if W != 0 else [0]*4
    u, v, w = u[:4], v[:5], w[:4]
    assert sp.Poly(U, y).degree() <= 3 and sp.Poly(V, y).degree() <= 4
    rows.append((u, v, w))
    U, V, W = sp.expand(2*U + sp.diff(U, y)), sp.expand(V + sp.diff(V, y)), sp.expand(sp.diff(W, y))

# sanity: Phi_j(0) = u0 - v0 - w0 is 0 for j <= 7 and 56 for j = 8
for j, (u, v, w) in enumerate(rows):
    val = u[0] - v[0] - w[0]
    assert val == (0 if j < 8 else 56), (j, val)

# the base case polynomial
A = y**3 + 2*y**2 - 2*y + 10
u8, v8, _w8 = rows[8]
assert sp.expand(sum(u8[i]*y**i for i in range(4)) - 256*A) == 0
V8 = sum(v8[i]*y**i for i in range(5))
base = sp.expand(256*(1 + y + y**2/2)*A - V8)
bc = sp.Poly(base, y).all_coeffs()[::-1]
assert all(c > 0 for c in bc), bc
print("base polynomial coefficients (ascending):", bc)


def num(c):
    c = sp.Rational(c)
    assert c.q == 1
    return f"({c.p})" if c.p < 0 else str(c.p)


def args(j):
    u, v, w = rows[j]
    return " ".join(num(c) for c in (u[3], u[2], u[1], u[0])) + " " \
        + " ".join(num(c) for c in (v[4], v[3], v[2], v[1], v[0])) + " " \
        + " ".join(num(c) for c in (w[3], w[2], w[1], w[0]))


def poly_str(cs, var="y"):
    ts = []
    for i, c in enumerate(cs):
        c = sp.Integer(c)
        if c == 0:
            continue
        s = ("+ " if c > 0 else "- ") + str(abs(c))
        if i == 1:
            s += f" * {var}"
        elif i > 1:
            s += f" * {var} ^ {i}"
        ts.append(s)
    t = " ".join(ts)
    return t[2:] if t.startswith("+ ") else "-" + t[2:]


steps = []
for j in range(7, -1, -1):
    steps.append(f'''
private lemma step{j} (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf {args(j)} y := by
  refine nonneg_of_deriv (g := Sf {args(j+1)})
    (fun z => ?_) ?_ step{j+1} hy
  · have h := hasDerivAt_Sf {args(j)} z
    refine h.congr_deriv ?_
    simp only [Sf]
    ring
  · simp only [Sf]
    norm_num''')

src = f'''/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# `log (sinh h / h) ≤ √(h² + 9) - 3`

This is the sharp estimate behind the simplified polar inequality `β(1) ≤ α/(3+α)` of the blog
post: applied at `u = αβ(1)/2`, `h = α(2-β(1))/2`, it is exactly what turns

  `1 ≤ ∫₀¹ exp(α(-1 + (2-β(1))t)) dt = e^{{-u}} sinh h / h`

into `β(1) ≤ α/(3+α)`.  The constant `3` cannot be improved: at `B = α/(3+α)` the slack in the
integral inequality is `-α⁵/540 + α⁶/648`, so the bound is tight to three orders at `α = 0`.

## The proof

Differentiating, it suffices to prove `coth h - 1/h ≤ h/√(h²+9)`, which after clearing
denominators is

  `G(h) := h⁴ sinh²h - (h²+9) (h cosh h - sinh h)² ≥ 0`.

The informal write-up gets this from the Taylor expansion
`G(h) = Σ_{{k≥4}} 2^{{2k-3}} (2k-1) (2k-6)² / (2k)! · h^{{2k}}`, all of whose coefficients are
nonnegative.  Formalizing an infinite series with nonnegative coefficients is unpleasant, and
unnecessary.  Setting

  `Φ(y) := e^{{2y}} P₁(y) - e^y P₂(y) - P₃(y)`,
  `P₁ = y³-10y²+36y-36`,  `P₂ = y⁴+16y²-72`,  `P₃ = y³+10y²+36y+36`,

one has the algebraic identity `Φ(2h) = 16 e^{{2h}} G(h)`, so `G ≥ 0` iff `Φ ≥ 0` on `[0,∞)`.
And `Φ` is *closed* under differentiation in the family

  `Sf u v w y = e^{{2y}} u(y) - e^y v(y) - w(y)`,  `u` cubic, `v` quartic, `w` cubic,

under `u ↦ 2u + u'`, `v ↦ v + v'`, `w ↦ w'`.  Eight steps of that recurrence reach

  `Φ⁽⁸⁾(y) = 256 e^{{2y}} (y³+2y²-2y+10) - e^y (y⁴+32y³+352y²+1600y+2504)`,

and `Φ⁽ʲ⁾(0) = 0` for `j ≤ 7`.  So it is enough to prove `Φ⁽⁸⁾ ≥ 0` and integrate eight times.
For `Φ⁽⁸⁾`, divide by `e^y` and use just three terms of the exponential series: what is left is

  `{poly_str(bc)}`,

every coefficient of which is positive.  No certificate, no series manipulation — one `ring`
identity and eight applications of "vanishes at `0` and has nonnegative derivative".

## Main statements

* `Sendov.sinh_sq_le`: `(h²+9)(h cosh h - sinh h)² ≤ h⁴ sinh²h`;
* `Sendov.log_sinh_div_le`: the displayed inequality;
* `Sendov.sinh_le_mul_exp`: the form actually used, `sinh h ≤ h exp (√(h²+9) - 3)`.
-/

namespace Sendov

open Real

/-- `f` vanishes at `0` and has nonnegative derivative on `[0,∞)`, hence is nonnegative there. -/
private lemma nonneg_of_deriv {{f g : ℝ → ℝ}} (hd : ∀ z, HasDerivAt f (g z) z)
    (h0 : f 0 = 0) (hg : ∀ z, 0 ≤ z → 0 ≤ g z) {{y : ℝ}} (hy : 0 ≤ y) : 0 ≤ f y := by
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun z _ => (hd z).continuousAt.continuousWithinAt)
      (fun z hz => (hd z).differentiableAt.differentiableWithinAt) (fun z hz => ?_)
    rw [(hd z).deriv]
    rw [interior_Ici] at hz
    exact hg z (le_of_lt hz)
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy
  rwa [h0] at this

/-- `1 + y + y²/2 ≤ exp y` for `y ≥ 0`: three terms of the exponential series. -/
private lemma quad_le_exp {{y : ℝ}} (hy : 0 ≤ y) : 1 + y + y ^ 2 / 2 ≤ exp y := by
  have key : ∀ z : ℝ, 0 ≤ z → 0 ≤ exp z - 1 - z - z ^ 2 / 2 := by
    intro z hz
    refine nonneg_of_deriv (f := fun t => exp t - 1 - t - t ^ 2 / 2)
      (g := fun t => exp t - 1 - t) (fun t => ?_) (by norm_num) (fun t ht => ?_) hz
    · have h := (((Real.hasDerivAt_exp t).sub_const 1).sub (hasDerivAt_id' t)).sub
        ((hasDerivAt_pow 2 t).div_const 2)
      refine h.congr_deriv ?_
      norm_num
    · have := Real.add_one_le_exp t
      linarith
  linarith [key y hy]

/-- The family closed under differentiation: `e^{{2y}} u(y) - e^y v(y) - w(y)` with `u`, `w`
cubic and `v` quartic. -/
private noncomputable def Sf (u₃ u₂ u₁ u₀ v₄ v₃ v₂ v₁ v₀ w₃ w₂ w₁ w₀ y : ℝ) : ℝ :=
  exp (2 * y) * (u₃ * y ^ 3 + u₂ * y ^ 2 + u₁ * y + u₀)
    - exp y * (v₄ * y ^ 4 + v₃ * y ^ 3 + v₂ * y ^ 2 + v₁ * y + v₀)
    - (w₃ * y ^ 3 + w₂ * y ^ 2 + w₁ * y + w₀)

private lemma hasDerivAt_Sf (u₃ u₂ u₁ u₀ v₄ v₃ v₂ v₁ v₀ w₃ w₂ w₁ w₀ y : ℝ) :
    HasDerivAt (fun t : ℝ => Sf u₃ u₂ u₁ u₀ v₄ v₃ v₂ v₁ v₀ w₃ w₂ w₁ w₀ t)
      (Sf (2 * u₃) (2 * u₂ + 3 * u₃) (2 * u₁ + 2 * u₂) (2 * u₀ + u₁)
          v₄ (v₃ + 4 * v₄) (v₂ + 3 * v₃) (v₁ + 2 * v₂) (v₀ + v₁)
          0 (3 * w₃) (2 * w₂) w₁ y) y := by
  simp only [Sf]
  have he2 : HasDerivAt (fun t : ℝ => exp (2 * t)) (exp (2 * y) * 2) y := by
    have h := ((hasDerivAt_id' y).const_mul (2 : ℝ)).exp
    refine h.congr_deriv ?_
    ring
  have he1 : HasDerivAt (fun t : ℝ => exp t) (exp y) y := Real.hasDerivAt_exp y
  have hu : HasDerivAt (fun t : ℝ => u₃ * t ^ 3 + u₂ * t ^ 2 + u₁ * t + u₀)
      (3 * u₃ * y ^ 2 + 2 * u₂ * y + u₁) y := by
    have h := ((((hasDerivAt_pow 3 y).const_mul u₃).add
      ((hasDerivAt_pow 2 y).const_mul u₂)).add ((hasDerivAt_id' y).const_mul u₁)).add_const u₀
    refine h.congr_deriv ?_
    norm_num
    ring
  have hv : HasDerivAt (fun t : ℝ => v₄ * t ^ 4 + v₃ * t ^ 3 + v₂ * t ^ 2 + v₁ * t + v₀)
      (4 * v₄ * y ^ 3 + 3 * v₃ * y ^ 2 + 2 * v₂ * y + v₁) y := by
    have h := (((((hasDerivAt_pow 4 y).const_mul v₄).add
      ((hasDerivAt_pow 3 y).const_mul v₃)).add
      ((hasDerivAt_pow 2 y).const_mul v₂)).add ((hasDerivAt_id' y).const_mul v₁)).add_const v₀
    refine h.congr_deriv ?_
    norm_num
    ring
  have hw : HasDerivAt (fun t : ℝ => w₃ * t ^ 3 + w₂ * t ^ 2 + w₁ * t + w₀)
      (3 * w₃ * y ^ 2 + 2 * w₂ * y + w₁) y := by
    have h := ((((hasDerivAt_pow 3 y).const_mul w₃).add
      ((hasDerivAt_pow 2 y).const_mul w₂)).add ((hasDerivAt_id' y).const_mul w₁)).add_const w₀
    refine h.congr_deriv ?_
    norm_num
    ring
  have h := ((he2.mul hu).sub (he1.mul hv)).sub hw
  refine h.congr_deriv ?_
  ring

/-- The base of the induction, `Φ⁽⁸⁾ ≥ 0`.  Three terms of the exponential series leave a
polynomial with every coefficient positive. -/
private lemma step8 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf {args(8)} y := by
  have hA : (0 : ℝ) ≤ 256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560 := by
    nlinarith [sq_nonneg (y - 1), pow_nonneg hy 3, sq_nonneg y]
  have h1 : (1 + y + y ^ 2 / 2) * (256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560)
      ≤ exp y * (256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560) :=
    mul_le_mul_of_nonneg_right (quad_le_exp hy) hA
  have h2 : (0 : ℝ) ≤ {poly_str(bc)} := by
    nlinarith [pow_nonneg hy 5, pow_nonneg hy 4, pow_nonneg hy 3, sq_nonneg y, hy]
  have h3 : (0 : ℝ) ≤ exp y * (256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560)
      - ({poly_str(rows[8][1])}) := by
    nlinarith [h1, h2]
  have hexp : exp (2 * y) = exp y * exp y := by rw [two_mul, Real.exp_add]
  have h4 := mul_nonneg (Real.exp_pos y).le h3
  calc (0 : ℝ) ≤ exp y * (exp y * (256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560)
        - ({poly_str(rows[8][1])})) := h4
    _ = Sf {args(8)} y := by
        simp only [Sf, hexp]
        ring
{"".join(steps)}

/-- The algebraic bridge: `Φ(2h) = 16 e^{{2h}} G(h)`. -/
private lemma Sf_eq (h : ℝ) :
    Sf {args(0)} (2 * h)
    = 16 * exp h ^ 2 * (h ^ 4 * sinh h ^ 2 - (h ^ 2 + 9) * (h * cosh h - sinh h) ^ 2) := by
  have hE : exp h ≠ 0 := (Real.exp_pos h).ne'
  have e4 : exp (2 * (2 * h)) = exp h ^ 4 := by
    rw [show (2 : ℝ) * (2 * h) = h + h + h + h by ring, Real.exp_add, Real.exp_add, Real.exp_add]
    ring
  have e2 : exp (2 * h) = exp h ^ 2 := by
    rw [show (2 : ℝ) * h = h + h by ring, Real.exp_add]; ring
  simp only [Sf, Real.sinh_eq, Real.cosh_eq, e4, e2, Real.exp_neg]
  field_simp
  ring

/-- **The key inequality.**  Equivalent to `coth h - 1/h ≤ h/√(h²+9)`. -/
theorem sinh_sq_le {{h : ℝ}} (hh : 0 ≤ h) :
    (h ^ 2 + 9) * (h * cosh h - sinh h) ^ 2 ≤ h ^ 4 * sinh h ^ 2 := by
  have h0 := step0 (2 * h) (by linarith)
  rw [Sf_eq] at h0
  have hpos : (0 : ℝ) < 16 * exp h ^ 2 := by positivity
  by_contra hc
  push_neg at hc
  nlinarith [h0, hpos, hc]

end Sendov
'''
# The analytic tail carries no generated data, and contains brace characters that an
# f-string would swallow, so it is kept beside this script rather than inlined.
src = src.replace("\nend Sendov\n", "\n") + io.open(Path(__file__).resolve().with_name("sinh_tail.lean.txt"), encoding="utf-8").read()
io.open(Path(__file__).resolve().parents[1] / "Sendov" / "Common" / "Sinh.lean", "w",
        encoding="utf-8", newline="\n").write(src)
print(f"written Sinh.lean, {len(src)} bytes")
