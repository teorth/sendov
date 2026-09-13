/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao

Adapted from Appendix A of Senjian An (SJanPerth),
Proof Distillation for Sendov's Conjecture, revision
 e8ae601491ec171ab4f7f8456113dd6a047aa85d.
Paper licensed CC BY 4.0: https://creativecommons.org/licenses/by/4.0/ .
Changes: replace the infinite-series certificate with an exact eleven-derivative
exponential closure, and replace Descartes' rule with a Bernstein identity.
Derivative descent / logarithmic endpoint argument adapted from Terence Tao's
Apache-2.0 Sendov/Common/Sinh.lean. No existing weak hyperbolic bound is used.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Strong hyperbolic comparison on `[0,10]`

Write `F(x) = x² A(x) sinh(x) - D(x) (x cosh(x) - sinh(x))`, with `D = 55 B`.
The functions `f0,...,f11` below satisfy `f0(x) = 2 exp(x) F(x)`,
`f(j+1) = f(j)'`, and `f(j)(0) = 0` for `j ≤ 10`.
The final function is exactly `2048 x¹⁰ exp(2x)`, not a Taylor approximation.
Descending nonnegativity therefore proves the full-function Padé comparison.

An explicit degree-eight Bernstein identity proves `P ≤ 0` on `[0,100]`.
This is sufficient for the square comparison (strict negativity is unnecessary).
Positive denominators, differentiation on `(0,10]`, and the right limit at zero
then give `log (sinh(x)/x) ≤ (7/8) (sqrt(9 + (8/7) x²) - 3)`.
The final theorem includes `x = 0` in the equivalent exponential bound.
-/

namespace Sendov.DistillationHyperbolic

open Real Set Filter

private lemma nonneg_of_deriv {f g : ℝ → ℝ} (hd : ∀ z, HasDerivAt f (g z) z)
    (h0 : f 0 = 0) (hg : ∀ z, 0 ≤ z → 0 ≤ g z) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ f y := by
  have hmono : MonotoneOn f (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun z _ => (hd z).continuousAt.continuousWithinAt)
      (fun z _ => (hd z).differentiableAt.differentiableWithinAt) (fun z hz => ?_)
    rw [(hd z).deriv]
    rw [interior_Ici] at hz
    exact hg z (le_of_lt hz)
  simpa [h0] using hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hy) hy

/-- The numerator polynomial in the donor Padé majorant. -/
def A (x : ℝ) : ℝ := x ^ 8 + 1430 * x ^ 6 + 289575 * x ^ 4 + 16081065 * x ^ 2 + 218243025

/-- Exactly 55 times the donor denominator polynomial. -/
def D (x : ℝ) : ℝ := 55 * x ^ 8 + 25740 * x ^ 6 + 2837835 * x ^ 4 + 91891800 * x ^ 2 + 654729075

private noncomputable def f0 (x : ℝ) : ℝ :=
  exp (2 * x) * (x ^ 10 - 55 * x ^ 9 + 1485 * x ^ 8 - 25740 * x ^ 7 + 315315 * x ^ 6 - 2837835 * x
      ^ 5 + 18918900 * x ^ 4 - 91891800 * x ^ 3 + 310134825 * x ^ 2 - 654729075 * x + 654729075) -
      (x ^ 10 + 55 * x ^ 9 + 1485 * x ^ 8 + 25740 * x ^ 7 + 315315 * x ^ 6 + 2837835 * x ^ 5 +
      18918900 * x ^ 4 + 91891800 * x ^ 3 + 310134825 * x ^ 2 + 654729075 * x + 654729075)

private noncomputable def f1 (x : ℝ) : ℝ :=
  exp (2 * x) * (2 * x ^ 10 - 100 * x ^ 9 + 2475 * x ^ 8 - 39600 * x ^ 7 + 450450 * x ^ 6 -
      3783780 * x ^ 5 + 23648625 * x ^ 4 - 108108000 * x ^ 3 + 344594250 * x ^ 2 - 689188500 * x +
      654729075) - (10 * x ^ 9 + 495 * x ^ 8 + 11880 * x ^ 7 + 180180 * x ^ 6 + 1891890 * x ^ 5 +
      14189175 * x ^ 4 + 75675600 * x ^ 3 + 275675400 * x ^ 2 + 620269650 * x + 654729075)

private noncomputable def f2 (x : ℝ) : ℝ :=
  exp (2 * x) * (4 * x ^ 10 - 180 * x ^ 9 + 4050 * x ^ 8 - 59400 * x ^ 7 + 623700 * x ^ 6 -
      4864860 * x ^ 5 + 28378350 * x ^ 4 - 121621500 * x ^ 3 + 364864500 * x ^ 2 - 689188500 * x +
      620269650) - (90 * x ^ 8 + 3960 * x ^ 7 + 83160 * x ^ 6 + 1081080 * x ^ 5 + 9459450 * x ^ 4
      + 56756700 * x ^ 3 + 227026800 * x ^ 2 + 551350800 * x + 620269650)

private noncomputable def f3 (x : ℝ) : ℝ :=
  exp (2 * x) * (8 * x ^ 10 - 320 * x ^ 9 + 6480 * x ^ 8 - 86400 * x ^ 7 + 831600 * x ^ 6 -
      5987520 * x ^ 5 + 32432400 * x ^ 4 - 129729600 * x ^ 3 + 364864500 * x ^ 2 - 648648000 * x +
      551350800) - (720 * x ^ 7 + 27720 * x ^ 6 + 498960 * x ^ 5 + 5405400 * x ^ 4 + 37837800 * x
      ^ 3 + 170270100 * x ^ 2 + 454053600 * x + 551350800)

private noncomputable def f4 (x : ℝ) : ℝ :=
  exp (2 * x) * (16 * x ^ 10 - 560 * x ^ 9 + 10080 * x ^ 8 - 120960 * x ^ 7 + 1058400 * x ^ 6 -
      6985440 * x ^ 5 + 34927200 * x ^ 4 - 129729600 * x ^ 3 + 340540200 * x ^ 2 - 567567000 * x +
      454053600) - (5040 * x ^ 6 + 166320 * x ^ 5 + 2494800 * x ^ 4 + 21621600 * x ^ 3 + 113513400
      * x ^ 2 + 340540200 * x + 454053600)

private noncomputable def f5 (x : ℝ) : ℝ :=
  exp (2 * x) * (32 * x ^ 10 - 960 * x ^ 9 + 15120 * x ^ 8 - 161280 * x ^ 7 + 1270080 * x ^ 6 -
      7620480 * x ^ 5 + 34927200 * x ^ 4 - 119750400 * x ^ 3 + 291891600 * x ^ 2 - 454053600 * x +
      340540200) - (30240 * x ^ 5 + 831600 * x ^ 4 + 9979200 * x ^ 3 + 64864800 * x ^ 2 +
      227026800 * x + 340540200)

private noncomputable def f6 (x : ℝ) : ℝ :=
  exp (2 * x) * (64 * x ^ 10 - 1600 * x ^ 9 + 21600 * x ^ 8 - 201600 * x ^ 7 + 1411200 * x ^ 6 -
      7620480 * x ^ 5 + 31752000 * x ^ 4 - 99792000 * x ^ 3 + 224532000 * x ^ 2 - 324324000 * x +
      227026800) - (151200 * x ^ 4 + 3326400 * x ^ 3 + 29937600 * x ^ 2 + 129729600 * x +
      227026800)

private noncomputable def f7 (x : ℝ) : ℝ :=
  exp (2 * x) * (128 * x ^ 10 - 2560 * x ^ 9 + 28800 * x ^ 8 - 230400 * x ^ 7 + 1411200 * x ^ 6 -
      6773760 * x ^ 5 + 25401600 * x ^ 4 - 72576000 * x ^ 3 + 149688000 * x ^ 2 - 199584000 * x +
      129729600) - (604800 * x ^ 3 + 9979200 * x ^ 2 + 59875200 * x + 129729600)

private noncomputable def f8 (x : ℝ) : ℝ :=
  exp (2 * x) * (256 * x ^ 10 - 3840 * x ^ 9 + 34560 * x ^ 8 - 230400 * x ^ 7 + 1209600 * x ^ 6 -
      5080320 * x ^ 5 + 16934400 * x ^ 4 - 43545600 * x ^ 3 + 81648000 * x ^ 2 - 99792000 * x +
      59875200) - (1814400 * x ^ 2 + 19958400 * x + 59875200)

private noncomputable def f9 (x : ℝ) : ℝ :=
  exp (2 * x) * (512 * x ^ 10 - 5120 * x ^ 9 + 34560 * x ^ 8 - 184320 * x ^ 7 + 806400 * x ^ 6 -
      2903040 * x ^ 5 + 8467200 * x ^ 4 - 19353600 * x ^ 3 + 32659200 * x ^ 2 - 36288000 * x +
      19958400) - (3628800 * x + 19958400)

private noncomputable def f10 (x : ℝ) : ℝ :=
  exp (2 * x) * (1024 * x ^ 10 - 5120 * x ^ 9 + 23040 * x ^ 8 - 92160 * x ^ 7 + 322560 * x ^ 6 -
      967680 * x ^ 5 + 2419200 * x ^ 4 - 4838400 * x ^ 3 + 7257600 * x ^ 2 - 7257600 * x +
      3628800) - (3628800)

private noncomputable def f11 (x : ℝ) : ℝ :=
  exp (2 * x) * (2048 * x ^ 10) - (0)

private lemma deriv0 (x : ℝ) : HasDerivAt f0 (f1 x) x := by
  have he := ((hasDerivAt_id' x).const_mul (2 : ℝ)).exp
  have hu := ((((((((((hasDerivAt_pow 10 x).add ((hasDerivAt_pow 9 x).const_mul (-55 : ℝ))).add
      ((hasDerivAt_pow 8 x).const_mul (1485 : ℝ))).add ((hasDerivAt_pow 7 x).const_mul (-25740 :
      ℝ))).add ((hasDerivAt_pow 6 x).const_mul (315315 : ℝ))).add ((hasDerivAt_pow 5 x).const_mul
      (-2837835 : ℝ))).add ((hasDerivAt_pow 4 x).const_mul (18918900 : ℝ))).add ((hasDerivAt_pow 3
      x).const_mul (-91891800 : ℝ))).add ((hasDerivAt_pow 2 x).const_mul (310134825 : ℝ))).add
      ((hasDerivAt_id' x).const_mul (-654729075 : ℝ))).add (hasDerivAt_const x (654729075 : ℝ))
  have hv := ((((((((((hasDerivAt_pow 10 x).add ((hasDerivAt_pow 9 x).const_mul (55 : ℝ))).add
      ((hasDerivAt_pow 8 x).const_mul (1485 : ℝ))).add ((hasDerivAt_pow 7 x).const_mul (25740 :
      ℝ))).add ((hasDerivAt_pow 6 x).const_mul (315315 : ℝ))).add ((hasDerivAt_pow 5 x).const_mul
      (2837835 : ℝ))).add ((hasDerivAt_pow 4 x).const_mul (18918900 : ℝ))).add ((hasDerivAt_pow 3
      x).const_mul (91891800 : ℝ))).add ((hasDerivAt_pow 2 x).const_mul (310134825 : ℝ))).add
      ((hasDerivAt_id' x).const_mul (654729075 : ℝ))).add (hasDerivAt_const x (654729075 : ℝ))
  convert! (he.mul hu).sub hv using 1 <;> norm_num [f0, f1, Pi.add_apply] <;>
    first | (funext z; dsimp [f0]; ring) | ring

private lemma deriv1 (x : ℝ) : HasDerivAt f1 (f2 x) x := by
  have he := ((hasDerivAt_id' x).const_mul (2 : ℝ)).exp
  have hu := (((((((((((hasDerivAt_pow 10 x).const_mul (2 : ℝ)).add ((hasDerivAt_pow 9
      x).const_mul (-100 : ℝ))).add ((hasDerivAt_pow 8 x).const_mul (2475 : ℝ))).add
      ((hasDerivAt_pow 7 x).const_mul (-39600 : ℝ))).add ((hasDerivAt_pow 6 x).const_mul (450450 :
      ℝ))).add ((hasDerivAt_pow 5 x).const_mul (-3783780 : ℝ))).add ((hasDerivAt_pow 4
      x).const_mul (23648625 : ℝ))).add ((hasDerivAt_pow 3 x).const_mul (-108108000 : ℝ))).add
      ((hasDerivAt_pow 2 x).const_mul (344594250 : ℝ))).add ((hasDerivAt_id' x).const_mul
      (-689188500 : ℝ))).add (hasDerivAt_const x (654729075 : ℝ))
  have hv := ((((((((((hasDerivAt_pow 9 x).const_mul (10 : ℝ)).add ((hasDerivAt_pow 8 x).const_mul
      (495 : ℝ))).add ((hasDerivAt_pow 7 x).const_mul (11880 : ℝ))).add ((hasDerivAt_pow 6
      x).const_mul (180180 : ℝ))).add ((hasDerivAt_pow 5 x).const_mul (1891890 : ℝ))).add
      ((hasDerivAt_pow 4 x).const_mul (14189175 : ℝ))).add ((hasDerivAt_pow 3 x).const_mul
      (75675600 : ℝ))).add ((hasDerivAt_pow 2 x).const_mul (275675400 : ℝ))).add ((hasDerivAt_id'
      x).const_mul (620269650 : ℝ))).add (hasDerivAt_const x (654729075 : ℝ))
  convert! (he.mul hu).sub hv using 1 <;> norm_num [f1, f2, Pi.add_apply] <;>
    first | (funext z; dsimp [f1]; ring) | ring

private lemma deriv2 (x : ℝ) : HasDerivAt f2 (f3 x) x := by
  have he := ((hasDerivAt_id' x).const_mul (2 : ℝ)).exp
  have hu := (((((((((((hasDerivAt_pow 10 x).const_mul (4 : ℝ)).add ((hasDerivAt_pow 9
      x).const_mul (-180 : ℝ))).add ((hasDerivAt_pow 8 x).const_mul (4050 : ℝ))).add
      ((hasDerivAt_pow 7 x).const_mul (-59400 : ℝ))).add ((hasDerivAt_pow 6 x).const_mul (623700 :
      ℝ))).add ((hasDerivAt_pow 5 x).const_mul (-4864860 : ℝ))).add ((hasDerivAt_pow 4
      x).const_mul (28378350 : ℝ))).add ((hasDerivAt_pow 3 x).const_mul (-121621500 : ℝ))).add
      ((hasDerivAt_pow 2 x).const_mul (364864500 : ℝ))).add ((hasDerivAt_id' x).const_mul
      (-689188500 : ℝ))).add (hasDerivAt_const x (620269650 : ℝ))
  have hv := (((((((((hasDerivAt_pow 8 x).const_mul (90 : ℝ)).add ((hasDerivAt_pow 7 x).const_mul
      (3960 : ℝ))).add ((hasDerivAt_pow 6 x).const_mul (83160 : ℝ))).add ((hasDerivAt_pow 5
      x).const_mul (1081080 : ℝ))).add ((hasDerivAt_pow 4 x).const_mul (9459450 : ℝ))).add
      ((hasDerivAt_pow 3 x).const_mul (56756700 : ℝ))).add ((hasDerivAt_pow 2 x).const_mul
      (227026800 : ℝ))).add ((hasDerivAt_id' x).const_mul (551350800 : ℝ))).add (hasDerivAt_const
      x (620269650 : ℝ))
  convert! (he.mul hu).sub hv using 1 <;> norm_num [f2, f3, Pi.add_apply] <;>
    first | (funext z; dsimp [f2]; ring) | ring

private lemma deriv3 (x : ℝ) : HasDerivAt f3 (f4 x) x := by
  have he := ((hasDerivAt_id' x).const_mul (2 : ℝ)).exp
  have hu := (((((((((((hasDerivAt_pow 10 x).const_mul (8 : ℝ)).add ((hasDerivAt_pow 9
      x).const_mul (-320 : ℝ))).add ((hasDerivAt_pow 8 x).const_mul (6480 : ℝ))).add
      ((hasDerivAt_pow 7 x).const_mul (-86400 : ℝ))).add ((hasDerivAt_pow 6 x).const_mul (831600 :
      ℝ))).add ((hasDerivAt_pow 5 x).const_mul (-5987520 : ℝ))).add ((hasDerivAt_pow 4
      x).const_mul (32432400 : ℝ))).add ((hasDerivAt_pow 3 x).const_mul (-129729600 : ℝ))).add
      ((hasDerivAt_pow 2 x).const_mul (364864500 : ℝ))).add ((hasDerivAt_id' x).const_mul
      (-648648000 : ℝ))).add (hasDerivAt_const x (551350800 : ℝ))
  have hv := ((((((((hasDerivAt_pow 7 x).const_mul (720 : ℝ)).add ((hasDerivAt_pow 6 x).const_mul
      (27720 : ℝ))).add ((hasDerivAt_pow 5 x).const_mul (498960 : ℝ))).add ((hasDerivAt_pow 4
      x).const_mul (5405400 : ℝ))).add ((hasDerivAt_pow 3 x).const_mul (37837800 : ℝ))).add
      ((hasDerivAt_pow 2 x).const_mul (170270100 : ℝ))).add ((hasDerivAt_id' x).const_mul
      (454053600 : ℝ))).add (hasDerivAt_const x (551350800 : ℝ))
  convert! (he.mul hu).sub hv using 1 <;> norm_num [f3, f4, Pi.add_apply] <;>
    first | (funext z; dsimp [f3]; ring) | ring

private lemma deriv4 (x : ℝ) : HasDerivAt f4 (f5 x) x := by
  have he := ((hasDerivAt_id' x).const_mul (2 : ℝ)).exp
  have hu := (((((((((((hasDerivAt_pow 10 x).const_mul (16 : ℝ)).add ((hasDerivAt_pow 9
      x).const_mul (-560 : ℝ))).add ((hasDerivAt_pow 8 x).const_mul (10080 : ℝ))).add
      ((hasDerivAt_pow 7 x).const_mul (-120960 : ℝ))).add ((hasDerivAt_pow 6 x).const_mul (1058400
      : ℝ))).add ((hasDerivAt_pow 5 x).const_mul (-6985440 : ℝ))).add ((hasDerivAt_pow 4
      x).const_mul (34927200 : ℝ))).add ((hasDerivAt_pow 3 x).const_mul (-129729600 : ℝ))).add
      ((hasDerivAt_pow 2 x).const_mul (340540200 : ℝ))).add ((hasDerivAt_id' x).const_mul
      (-567567000 : ℝ))).add (hasDerivAt_const x (454053600 : ℝ))
  have hv := (((((((hasDerivAt_pow 6 x).const_mul (5040 : ℝ)).add ((hasDerivAt_pow 5 x).const_mul
      (166320 : ℝ))).add ((hasDerivAt_pow 4 x).const_mul (2494800 : ℝ))).add ((hasDerivAt_pow 3
      x).const_mul (21621600 : ℝ))).add ((hasDerivAt_pow 2 x).const_mul (113513400 : ℝ))).add
      ((hasDerivAt_id' x).const_mul (340540200 : ℝ))).add (hasDerivAt_const x (454053600 : ℝ))
  convert! (he.mul hu).sub hv using 1 <;> norm_num [f4, f5, Pi.add_apply] <;>
    first | (funext z; dsimp [f4]; ring) | ring

private lemma deriv5 (x : ℝ) : HasDerivAt f5 (f6 x) x := by
  have he := ((hasDerivAt_id' x).const_mul (2 : ℝ)).exp
  have hu := (((((((((((hasDerivAt_pow 10 x).const_mul (32 : ℝ)).add ((hasDerivAt_pow 9
      x).const_mul (-960 : ℝ))).add ((hasDerivAt_pow 8 x).const_mul (15120 : ℝ))).add
      ((hasDerivAt_pow 7 x).const_mul (-161280 : ℝ))).add ((hasDerivAt_pow 6 x).const_mul (1270080
      : ℝ))).add ((hasDerivAt_pow 5 x).const_mul (-7620480 : ℝ))).add ((hasDerivAt_pow 4
      x).const_mul (34927200 : ℝ))).add ((hasDerivAt_pow 3 x).const_mul (-119750400 : ℝ))).add
      ((hasDerivAt_pow 2 x).const_mul (291891600 : ℝ))).add ((hasDerivAt_id' x).const_mul
      (-454053600 : ℝ))).add (hasDerivAt_const x (340540200 : ℝ))
  have hv := ((((((hasDerivAt_pow 5 x).const_mul (30240 : ℝ)).add ((hasDerivAt_pow 4 x).const_mul
      (831600 : ℝ))).add ((hasDerivAt_pow 3 x).const_mul (9979200 : ℝ))).add ((hasDerivAt_pow 2
      x).const_mul (64864800 : ℝ))).add ((hasDerivAt_id' x).const_mul (227026800 : ℝ))).add
      (hasDerivAt_const x (340540200 : ℝ))
  convert! (he.mul hu).sub hv using 1 <;> norm_num [f5, f6, Pi.add_apply] <;>
    first | (funext z; dsimp [f5]; ring) | ring

private lemma deriv6 (x : ℝ) : HasDerivAt f6 (f7 x) x := by
  have he := ((hasDerivAt_id' x).const_mul (2 : ℝ)).exp
  have hu := (((((((((((hasDerivAt_pow 10 x).const_mul (64 : ℝ)).add ((hasDerivAt_pow 9
      x).const_mul (-1600 : ℝ))).add ((hasDerivAt_pow 8 x).const_mul (21600 : ℝ))).add
      ((hasDerivAt_pow 7 x).const_mul (-201600 : ℝ))).add ((hasDerivAt_pow 6 x).const_mul (1411200
      : ℝ))).add ((hasDerivAt_pow 5 x).const_mul (-7620480 : ℝ))).add ((hasDerivAt_pow 4
      x).const_mul (31752000 : ℝ))).add ((hasDerivAt_pow 3 x).const_mul (-99792000 : ℝ))).add
      ((hasDerivAt_pow 2 x).const_mul (224532000 : ℝ))).add ((hasDerivAt_id' x).const_mul
      (-324324000 : ℝ))).add (hasDerivAt_const x (227026800 : ℝ))
  have hv := (((((hasDerivAt_pow 4 x).const_mul (151200 : ℝ)).add ((hasDerivAt_pow 3 x).const_mul
      (3326400 : ℝ))).add ((hasDerivAt_pow 2 x).const_mul (29937600 : ℝ))).add ((hasDerivAt_id'
      x).const_mul (129729600 : ℝ))).add (hasDerivAt_const x (227026800 : ℝ))
  convert! (he.mul hu).sub hv using 1 <;> norm_num [f6, f7, Pi.add_apply] <;>
    first | (funext z; dsimp [f6]; ring) | ring

private lemma deriv7 (x : ℝ) : HasDerivAt f7 (f8 x) x := by
  have he := ((hasDerivAt_id' x).const_mul (2 : ℝ)).exp
  have hu := (((((((((((hasDerivAt_pow 10 x).const_mul (128 : ℝ)).add ((hasDerivAt_pow 9
      x).const_mul (-2560 : ℝ))).add ((hasDerivAt_pow 8 x).const_mul (28800 : ℝ))).add
      ((hasDerivAt_pow 7 x).const_mul (-230400 : ℝ))).add ((hasDerivAt_pow 6 x).const_mul (1411200
      : ℝ))).add ((hasDerivAt_pow 5 x).const_mul (-6773760 : ℝ))).add ((hasDerivAt_pow 4
      x).const_mul (25401600 : ℝ))).add ((hasDerivAt_pow 3 x).const_mul (-72576000 : ℝ))).add
      ((hasDerivAt_pow 2 x).const_mul (149688000 : ℝ))).add ((hasDerivAt_id' x).const_mul
      (-199584000 : ℝ))).add (hasDerivAt_const x (129729600 : ℝ))
  have hv := ((((hasDerivAt_pow 3 x).const_mul (604800 : ℝ)).add ((hasDerivAt_pow 2 x).const_mul
      (9979200 : ℝ))).add ((hasDerivAt_id' x).const_mul (59875200 : ℝ))).add (hasDerivAt_const x
      (129729600 : ℝ))
  convert! (he.mul hu).sub hv using 1 <;> norm_num [f7, f8, Pi.add_apply] <;>
    first | (funext z; dsimp [f7]; ring) | ring

private lemma deriv8 (x : ℝ) : HasDerivAt f8 (f9 x) x := by
  have he := ((hasDerivAt_id' x).const_mul (2 : ℝ)).exp
  have hu := (((((((((((hasDerivAt_pow 10 x).const_mul (256 : ℝ)).add ((hasDerivAt_pow 9
      x).const_mul (-3840 : ℝ))).add ((hasDerivAt_pow 8 x).const_mul (34560 : ℝ))).add
      ((hasDerivAt_pow 7 x).const_mul (-230400 : ℝ))).add ((hasDerivAt_pow 6 x).const_mul (1209600
      : ℝ))).add ((hasDerivAt_pow 5 x).const_mul (-5080320 : ℝ))).add ((hasDerivAt_pow 4
      x).const_mul (16934400 : ℝ))).add ((hasDerivAt_pow 3 x).const_mul (-43545600 : ℝ))).add
      ((hasDerivAt_pow 2 x).const_mul (81648000 : ℝ))).add ((hasDerivAt_id' x).const_mul
      (-99792000 : ℝ))).add (hasDerivAt_const x (59875200 : ℝ))
  have hv := (((hasDerivAt_pow 2 x).const_mul (1814400 : ℝ)).add ((hasDerivAt_id' x).const_mul
      (19958400 : ℝ))).add (hasDerivAt_const x (59875200 : ℝ))
  convert! (he.mul hu).sub hv using 1 <;> norm_num [f8, f9, Pi.add_apply] <;>
    first | (funext z; dsimp [f8]; ring) | ring

private lemma deriv9 (x : ℝ) : HasDerivAt f9 (f10 x) x := by
  have he := ((hasDerivAt_id' x).const_mul (2 : ℝ)).exp
  have hu := (((((((((((hasDerivAt_pow 10 x).const_mul (512 : ℝ)).add ((hasDerivAt_pow 9
      x).const_mul (-5120 : ℝ))).add ((hasDerivAt_pow 8 x).const_mul (34560 : ℝ))).add
      ((hasDerivAt_pow 7 x).const_mul (-184320 : ℝ))).add ((hasDerivAt_pow 6 x).const_mul (806400
      : ℝ))).add ((hasDerivAt_pow 5 x).const_mul (-2903040 : ℝ))).add ((hasDerivAt_pow 4
      x).const_mul (8467200 : ℝ))).add ((hasDerivAt_pow 3 x).const_mul (-19353600 : ℝ))).add
      ((hasDerivAt_pow 2 x).const_mul (32659200 : ℝ))).add ((hasDerivAt_id' x).const_mul
      (-36288000 : ℝ))).add (hasDerivAt_const x (19958400 : ℝ))
  have hv := ((hasDerivAt_id' x).const_mul (3628800 : ℝ)).add (hasDerivAt_const x (19958400 : ℝ))
  convert! (he.mul hu).sub hv using 1 <;> norm_num [f9, f10, Pi.add_apply] <;>
    first | (funext z; dsimp [f9]; ring) | ring

private lemma deriv10 (x : ℝ) : HasDerivAt f10 (f11 x) x := by
  have he := ((hasDerivAt_id' x).const_mul (2 : ℝ)).exp
  have hu := (((((((((((hasDerivAt_pow 10 x).const_mul (1024 : ℝ)).add ((hasDerivAt_pow 9
      x).const_mul (-5120 : ℝ))).add ((hasDerivAt_pow 8 x).const_mul (23040 : ℝ))).add
      ((hasDerivAt_pow 7 x).const_mul (-92160 : ℝ))).add ((hasDerivAt_pow 6 x).const_mul (322560 :
      ℝ))).add ((hasDerivAt_pow 5 x).const_mul (-967680 : ℝ))).add ((hasDerivAt_pow 4 x).const_mul
      (2419200 : ℝ))).add ((hasDerivAt_pow 3 x).const_mul (-4838400 : ℝ))).add ((hasDerivAt_pow 2
      x).const_mul (7257600 : ℝ))).add ((hasDerivAt_id' x).const_mul (-7257600 : ℝ))).add
      (hasDerivAt_const x (3628800 : ℝ))
  have hv := hasDerivAt_const x (3628800 : ℝ)
  convert! (he.mul hu).sub hv using 1 <;> norm_num [f10, f11, Pi.add_apply] <;>
    first | (funext z; dsimp [f10]; ring) | ring

private lemma nonneg11 (x : ℝ) (_hx : 0 ≤ x) : 0 ≤ f11 x := by
  simp only [f11, sub_zero]
  positivity

private lemma nonneg10 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f10 x :=
  nonneg_of_deriv deriv10 (by norm_num [f10]) nonneg11 hx

private lemma nonneg9 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f9 x :=
  nonneg_of_deriv deriv9 (by norm_num [f9]) nonneg10 hx

private lemma nonneg8 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f8 x :=
  nonneg_of_deriv deriv8 (by norm_num [f8]) nonneg9 hx

private lemma nonneg7 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f7 x :=
  nonneg_of_deriv deriv7 (by norm_num [f7]) nonneg8 hx

private lemma nonneg6 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f6 x :=
  nonneg_of_deriv deriv6 (by norm_num [f6]) nonneg7 hx

private lemma nonneg5 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f5 x :=
  nonneg_of_deriv deriv5 (by norm_num [f5]) nonneg6 hx

private lemma nonneg4 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f4 x :=
  nonneg_of_deriv deriv4 (by norm_num [f4]) nonneg5 hx

private lemma nonneg3 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f3 x :=
  nonneg_of_deriv deriv3 (by norm_num [f3]) nonneg4 hx

private lemma nonneg2 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f2 x :=
  nonneg_of_deriv deriv2 (by norm_num [f2]) nonneg3 hx

private lemma nonneg1 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f1 x :=
  nonneg_of_deriv deriv1 (by norm_num [f1]) nonneg2 hx

private lemma nonneg0 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f0 x :=
  nonneg_of_deriv deriv0 (by norm_num [f0]) nonneg1 hx

/-- Full-function Padé inequality, proved by exact derivatives, not a Taylor truncation. -/
theorem pade_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x ^ 2 * A x * sinh x - D x * (x * cosh x - sinh x) := by
  have h := nonneg0 x hx
  have he : exp x ≠ 0 := (exp_pos x).ne'
  have hid : f0 x = 2 * exp x *
      (x ^ 2 * A x * sinh x - D x * (x * cosh x - sinh x)) := by
    simp only [f0, A, D, sinh_eq, cosh_eq, exp_neg,
      show exp (2 * x) = exp x ^ 2 by simp [← exp_nat_mul]]
    field_simp
    ring
  rw [hid] at h
  exact nonneg_of_mul_nonneg_right h (by positivity)

private def P (x : ℝ) : ℝ := 8 * x ^ 8 + 1768 * x ^ 7 + 1352780 * x ^ 6 + 225122040 * x ^ 5 +
    3059031690 * x ^ 4 - 2283465284100 * x ^ 3 - 180738098991450 * x ^ 2 - 4712864935103325 * x -
    19052007184460250

private lemma P_nonpos {y : ℝ} (hy : 0 ≤ y) (hy100 : y ≤ 100) : P y ≤ 0 := by
  have hz : 0 ≤ 100 - y := sub_nonneg.mpr hy100
  have h : 0 ≤ 19052007184460250 * y ^ 0 * (100 - y) ^ 8 +
      623702550986014500 * y ^ 1 * (100 - y) ^ 7 +
      5639842645651714500 * y ^ 2 * (100 - y) ^ 6 +
      24091679989633756500 * y ^ 3 * (100 - y) ^ 5 +
      56050805875991355000 * y ^ 4 * (100 - y) ^ 4 +
      73069379238481411500 * y ^ 5 * (100 - y) ^ 3 +
      50433980040599369500 * y ^ 6 * (100 - y) ^ 2 +
      14853399996035009500 * y ^ 7 * (100 - y) ^ 1 +
      414481205709292750 * y ^ 8 * (100 - y) ^ 0 := by positivity
  have hid : 19052007184460250 * y ^ 0 * (100 - y) ^ 8 +
      623702550986014500 * y ^ 1 * (100 - y) ^ 7 +
      5639842645651714500 * y ^ 2 * (100 - y) ^ 6 +
      24091679989633756500 * y ^ 3 * (100 - y) ^ 5 +
      56050805875991355000 * y ^ 4 * (100 - y) ^ 4 +
      73069379238481411500 * y ^ 5 * (100 - y) ^ 3 +
      50433980040599369500 * y ^ 6 * (100 - y) ^ 2 +
      14853399996035009500 * y ^ 7 * (100 - y) ^ 1 +
      414481205709292750 * y ^ 8 * (100 - y) ^ 0 = -(100 ^ 8 : ℝ) * P y := by
    unfold P
    ring
  rw [hid] at h
  nlinarith

/-- Rational square comparison, with the essential factor `8/7`. -/
theorem pade_square_le {x : ℝ} (hx : 0 ≤ x) (hx10 : x ≤ 10) :
    (9 + (8 / 7 : ℝ) * x ^ 2) * A x ^ 2 ≤ D x ^ 2 := by
  have hP := P_nonpos (sq_nonneg x) (show x ^ 2 ≤ 100 by nlinarith)
  have hid : 7 * ((9 + (8 / 7 : ℝ) * x ^ 2) * A x ^ 2 - D x ^ 2) =
      x ^ 2 * P (x ^ 2) := by unfold A D P; ring
  have hh := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) hP
  nlinarith

/-- Cleared derivative comparison for the stronger, interval-restricted bound. -/
theorem sqrt_mul_sub_le {x : ℝ} (hx : 0 ≤ x) (hx10 : x ≤ 10) :
    sqrt (9 + (8 / 7 : ℝ) * x ^ 2) * (x * cosh x - sinh x) ≤ x ^ 2 * sinh x := by
  have hA : 0 ≤ A x := by unfold A; positivity
  have hD : 0 < D x := by unfold D; positivity
  have hs := pade_square_le hx hx10
  have hr : 0 ≤ 9 + (8 / 7 : ℝ) * x ^ 2 := by positivity
  have hroot : sqrt (9 + (8 / 7 : ℝ) * x ^ 2) * A x ≤ D x := by
    have heq : (sqrt (9 + (8 / 7 : ℝ) * x ^ 2) * A x) ^ 2 =
        (9 + (8 / 7 : ℝ) * x ^ 2) * A x ^ 2 := by rw [mul_pow, sq_sqrt hr]
    have hpos := mul_nonneg (sqrt_nonneg (9 + (8 / 7 : ℝ) * x ^ 2)) hA
    nlinarith
  have hp := pade_nonneg hx
  have hsinh : 0 ≤ sinh x := sinh_nonneg_iff.mpr hx
  have hmul := mul_le_mul_of_nonneg_left hroot (mul_nonneg (sq_nonneg x) hsinh)
  have hmul2 := mul_nonneg (sqrt_nonneg (9 + (8 / 7 : ℝ) * x ^ 2)) hp
  have hh : D x * (sqrt (9 + (8 / 7 : ℝ) * x ^ 2) *
      (x * cosh x - sinh x)) ≤ D x * (x ^ 2 * sinh x) := by nlinarith
  exact (mul_le_mul_iff_right₀ hD).mp hh

/-- Strong SJanPerth bound on `(0,10]`; both rational scale factors are retained. -/
theorem log_sinh_div_le {h : ℝ} (hh : 0 < h) (hh10 : h ≤ 10) :
    log (sinh h / h) ≤ (7 / 8 : ℝ) * (sqrt (9 + (8 / 7 : ℝ) * h ^ 2) - 3) := by
  set ψ : ℝ → ℝ := fun z => (7 / 8 : ℝ) * (sqrt (9 + (8 / 7 : ℝ) * z ^ 2) - 3) - (log (sinh z) -
      log z) with hψdef
  -- `ψ` has nonnegative derivative on `(0,10]`.
  have hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt ψ (z / sqrt (9 + (8 / 7 : ℝ) * z ^ 2) - (cosh z / sinh z - 1 / z)) z := by
    intro z hz
    have hsinh : sinh z ≠ 0 := ne_of_gt (sinh_pos_iff.2 hz)
    apply HasDerivAt.sub
    · have h := ((((hasDerivAt_pow 2 z).const_mul (8 / 7 : ℝ)).const_add 9).sqrt (ne_of_gt (by
        positivity))).sub_const 3 |>.const_mul (7 / 8 : ℝ)
      refine h.congr_deriv ?_
      field_simp
      ring
    · exact (((hasDerivAt_sinh z).log hsinh).sub
        ((hasDerivAt_id' z).log (ne_of_gt hz))).congr_deriv (by field_simp)
  have hmono : MonotoneOn ψ (Ioc 0 10) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioc 0 10)
      (fun z hz => (hderiv z hz.1).continuousAt.continuousWithinAt)
      (fun z hz => (hderiv z (by rw [interior_Ioc] at hz; exact
          hz.1)).differentiableAt.differentiableWithinAt)
      (fun z hz => ?_)
    rw [interior_Ioc, mem_Ioo] at hz
    have hzpos : 0 < z := hz.1
    rw [(hderiv z hz.1).deriv, sub_nonneg, div_sub_div _ _ (ne_of_gt (sinh_pos_iff.2 hz.1))
      (ne_of_gt hz.1), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sqrt_mul_sub_le (le_of_lt hz.1) (le_of_lt hz.2)]
  -- `ψ → 0` as `z → 0⁺`
  have hslope : Tendsto (fun z => sinh z / z) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
    simpa [slope_fun_def, div_eq_inv_mul, hasDerivAt_iff_tendsto_slope] using hasDerivAt_sinh 0
  have hlog : Tendsto ψ (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hsub : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhdsWithin 0 {(0 : ℝ)}ᶜ :=
      nhdsWithin_mono _ (fun z hz => ne_of_gt hz)
    have h1 : Tendsto (fun z => log (sinh z / z)) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa [Function.comp_def] using (continuousAt_log one_ne_zero).tendsto.comp
        (hslope.mono_left hsub)
    have h2 : Tendsto (fun z : ℝ => (7 / 8 : ℝ) * (sqrt (9 + (8 / 7 : ℝ) * z ^ 2) - 3))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have h9 : sqrt (9 : ℝ) = 3 := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
      have hc : ContinuousAt (fun z => (7 / 8 : ℝ) * (sqrt (9 + (8 / 7 : ℝ) * z ^ 2) - 3)) 0 := by
          fun_prop
      simpa [ContinuousWithinAt, h9] using hc.continuousWithinAt (s := Ioi (0 : ℝ))
    have heq : ∀ᶠ z : ℝ in nhdsWithin 0 (Ioi 0),
        ψ z = ((7 / 8 : ℝ) * (sqrt (9 + (8 / 7 : ℝ) * z ^ 2) - 3)) - log (sinh z / z) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [hψdef, log_div (ne_of_gt (sinh_pos_iff.2 hz)) (ne_of_gt hz)]
    simpa [tendsto_congr' heq] using h2.sub h1
  -- combine
  have hev : ∀ᶠ z : ℝ in nhdsWithin 0 (Ioi 0), ψ z ≤ ψ h := by
    have hmem : Ioo (0 : ℝ) h ∈ nhdsWithin (0 : ℝ) (Ioi 0) :=
      mem_nhdsGT_iff_exists_Ioo_subset.2 (Exists.intro h (And.intro (mem_Ioi.2 hh) subset_rfl))
    filter_upwards [hmem] with z hz
    exact hmono ⟨hz.1, le_trans hz.2.le hh10⟩ ⟨hh, hh10⟩ (le_of_lt hz.2)
  have h0 : (0 : ℝ) ≤ ψ h := le_of_tendsto hlog hev
  have : (0 : ℝ) < sinh h / h := div_pos (sinh_pos_iff.2 hh) hh
  rw [hψdef] at h0
  rw [log_div (ne_of_gt (sinh_pos_iff.2 hh)) (ne_of_gt hh)]
  linarith

/-- Strong exponential form, including the endpoint `h = 0`. -/
theorem sinh_le_mul_exp {h : ℝ} (hh : 0 ≤ h) (hh10 : h ≤ 10) :
    sinh h ≤ h * exp ((7 / 8 : ℝ) * (sqrt (9 + (8 / 7 : ℝ) * h ^ 2) - 3)) := by
  rcases eq_or_lt_of_le hh with rfl | hpos
  · simp
  · have hd : (0 : ℝ) < sinh h / h := div_pos (sinh_pos_iff.2 hpos) hpos
    grw [← (log_le_iff_le_exp hd).1 (log_sinh_div_le hpos hh10)]
    field_simp
    simp


end Sendov.DistillationHyperbolic
