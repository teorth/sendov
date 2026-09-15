import Sendov.Analytic.PaperPolar
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Full complex-polar diagnostic against the all-degree mean-half claim

Four conjugate unit-circle pairs, not just a relaxed scalar witness.
This refutes only `pointwise + full polar ⇒ mean > (1+a)/2` for all degrees.
No first-origin identity is assumed. This is not a D or Sendov counterexample.
-/
namespace Sendov.PaperPolar.Counterexample
open MeasureTheory
open scoped BigOperators

noncomputable def a : ℝ := 99 / 100
noncomputable def x : ℝ := 497 / 500
noncomputable def y : ℝ := Real.sqrt (1 - x ^ 2)
noncomputable def plus : ℂ := ⟨x, y⟩
noncomputable def minus : ℂ := ⟨x, -y⟩
/-- Alternating signs give exactly four conjugate pairs. -/
noncomputable def q (j : Fin 8) : ℂ := if j.val % 2 = 0 then plus else minus
noncomputable def value : ℝ :=
  9844160902221705118371486810769458499 /
    9843750000000000000000000000000000000

lemma y_sq : y ^ 2 = 1 - x ^ 2 := by
  exact Real.sq_sqrt (by norm_num [x])

lemma norm_plus : ‖plus‖ = 1 := by
  have h : ‖plus‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    change x * x + y * y = 1
    nlinarith [y_sq]
  nlinarith [norm_nonneg plus]

lemma norm_minus : ‖minus‖ = 1 := by
  have h : ‖minus‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    change x * x + (-y) * (-y) = 1
    nlinarith [y_sq]
  nlinarith [norm_nonneg minus]

theorem norm_q (j : Fin 8) : ‖q j‖ = 1 := by
  unfold q
  split <;> first | exact norm_plus | exact norm_minus

theorem mean_q : (∑ j : Fin 8, q j) / 8 = (x : ℂ) := by
  norm_num [q, Fin.sum_univ_succ]
  apply Complex.ext <;> simp [plus, minus]
  ring

lemma pair_product (s r : ℝ) :
    ((s : ℂ) + r * plus) * (s + r * minus) =
      ((s ^ 2 + 2 * s * r * x + r ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp only [plus, minus, pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, mul_zero, sub_zero, add_zero, zero_add]
  · have h := congrArg (fun z : ℝ => r ^ 2 * z) y_sq
    nlinarith only [h]
  · ring

theorem product_eq (t : ℝ) :
    (∏ j : Fin 8, ((a : ℂ) + ((1 - a ^ 2) * t : ℝ) * q j)) =
      (((a ^ 2 + 2 * a * (1 - a ^ 2) * x * t +
        (1 - a ^ 2) ^ 2 * t ^ 2) ^ 4 : ℝ) : ℂ) := by
  have hp := pair_product a ((1 - a ^ 2) * t)
  norm_num [q, Fin.prod_univ_succ]
  calc
    _ = (((a : ℂ) + ((1 - a ^ 2) * t : ℝ) * plus) *
        ((a : ℂ) + ((1 - a ^ 2) * t : ℝ) * minus)) ^ 4 := by push_cast; ring
    _ = _ := by rw [hp]; push_cast; ring

/-- Nine coefficients of a fourth power of a quadratic. -/
noncomputable def fourthCoeffs (A B C : ℝ) : Fin 9 → ℝ :=
  ![A ^ 4, 4 * A ^ 3 * B, 6 * A ^ 2 * B ^ 2 + 4 * A ^ 3 * C,
    4 * A * B ^ 3 + 12 * A ^ 2 * B * C,
    B ^ 4 + 12 * A * B ^ 2 * C + 6 * A ^ 2 * C ^ 2,
    4 * B ^ 3 * C + 12 * A * B * C ^ 2,
    6 * B ^ 2 * C ^ 2 + 4 * A * C ^ 3, 4 * B * C ^ 3, C ^ 4]

lemma fourth_expansion (A B C t : ℝ) :
    (A + B * t + C * t ^ 2) ^ 4 =
      ∑ k : Fin 9, fourthCoeffs A B C k * t ^ k.val := by
  simp [fourthCoeffs, Fin.sum_univ_succ]
  ring

lemma integral_fourth (A B C : ℝ) :
    (∫ t in (0 : ℝ)..1, (A + B * t + C * t ^ 2) ^ 4) =
      ∑ k : Fin 9, fourthCoeffs A B C k / (k.val + 1) := by
  simp_rw [fourth_expansion]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp
    ring
  · intro k hk
    exact ((continuous_const.mul (continuous_pow k.val))).intervalIntegrable _ _

theorem integral_real :
    (∫ t in (0 : ℝ)..1,
      (a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^ 4) =
        value := by
  rw [integral_fourth]
  norm_num [fourthCoeffs, Fin.sum_univ_succ, a, x, value]

/-- Evaluation of the literal complex product integral (not the raw relaxation). -/
theorem integral_complex :
    (∫ t in (0 : ℝ)..1,
      ∏ j : Fin 8, ((a : ℂ) + ((1 - a ^ 2) * t : ℝ) * q j)) = (value : ℂ) := by
  simp_rw [product_eq]
  rw [intervalIntegral.integral_ofReal, integral_real]

theorem value_gt_one : 1 < value := by norm_num [value]

theorem full_polar :
    1 < ‖∫ t in (0 : ℝ)..1,
      ∏ j : Fin 8, ((a : ℂ) + ((1 - a ^ 2) * t : ℝ) * q j)‖ := by
  rw [integral_complex, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (lt_trans (by norm_num) value_gt_one)]
  exact value_gt_one

theorem mean_lt_half : ((∑ j : Fin 8, q j) / 8).re < (1 + a) / 2 := by
  rw [mean_q]
  norm_num [a, x]

/-- The two means are exactly `0.994` and `0.995`. -/
theorem exact_means : ((∑ j : Fin 8, q j) / 8).re = 497 / 500 ∧
    (1 + a) / 2 = 199 / 200 := by
  rw [mean_q]
  norm_num [a, x]

/-- The scalar relaxation also holds, but is not used to prove full polar. -/
theorem raw_polar : RawPolar 8 a x := by
  unfold RawPolar
  norm_num only [Nat.cast_ofNat, show (8 : ℝ) / 2 = (4 : ℝ) by norm_num,
    Real.rpow_ofNat]
  rw [integral_real]
  exact value_gt_one.le

/-- The exact counterexample to the proposed all-degree implication. -/
theorem not_universal_mean_half :
    ¬ (∀ (m : ℕ) (a : ℝ) (q : Fin m → ℂ), 7 ≤ m → 0 < a → a < 1 →
      (∀ j, ‖q j‖ ≤ 1) →
      1 ≤ ‖∫ t in (0 : ℝ)..1,
        ∏ j : Fin m, ((a : ℂ) + ((1 - a ^ 2) * t : ℝ) * q j)‖ →
      (1 + a) / 2 < ((∑ j : Fin m, q j) / (m : ℂ)).re) := by
  intro h
  have hh := h 8 a q (by norm_num) (by norm_num [a]) (by norm_num [a])
    (fun j => (norm_q j).le) full_polar.le
  exact (not_lt_of_ge mean_lt_half.le) hh

#print axioms norm_q
#print axioms mean_q
#print axioms integral_complex
#print axioms full_polar
#print axioms not_universal_mean_half

end Sendov.PaperPolar.Counterexample
