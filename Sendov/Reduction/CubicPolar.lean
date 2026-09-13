import Sendov.Common.DistillationHyperbolic
import Sendov.Reduction.DistillationBridge

/-!
# The strict cubic polar envelope from the original weak polar constraint

Adaptation of Senjian An (SJanPerth), *Proof Distillation for Sendov's
Conjecture*, revision e8ae601491ec171ab4f7f8456113dd6a047aa85d,
paper lines 260–291 (CC BY 4.0, https://creativecommons.org/licenses/by/4.0/).
The integral evaluation is the existing Apache-2.0 BetaBound interface.

Unlike the paper, the input is only `1 ≤ integral`. This gives `F(p) ≤ 0`,
which still contradicts the STRICT positivity of F at the cubic envelope.
The resulting strict envelope feeds the scalar obstruction comparison.
-/

namespace Sendov

open MeasureTheory Real

/-- A positive-coefficient certificate replaces the paper's Descartes argument. -/
lemma cubicPolarEnvelope_center_lt_ten {α : ℝ} (hα : 0 ≤ α) (h17 : α ≤ 17) :
    α * (1 - cubicPolarEnvelope α / 2) < 10 := by
  have hd : α + 3 ≠ 0 := by positivity
  have hid : 10 - α * (1 - cubicPolarEnvelope α / 2) =
      ((17 - α) * (31 * α ^ 3 + 287 * α ^ 2 + 829 * α) + 487 * α + 16200) /
        (60 * (α + 3) ^ 3) := by
    unfold cubicPolarEnvelope
    field_simp
    ring
  have hn : 0 < (17 - α) * (31 * α ^ 3 + 287 * α ^ 2 + 829 * α) +
      487 * α + 16200 := by
    have := mul_nonneg (sub_nonneg.mpr h17)
      (show 0 ≤ 31 * α ^ 3 + 287 * α ^ 2 + 829 * α by positivity)
    positivity
  have hp : 0 < 10 - α * (1 - cubicPolarEnvelope α / 2) := by
    rw [hid]
    exact div_pos hn (by positivity)
  linarith

/-- Strict positivity at the envelope. Clearing the paper's u-expression gives
an all-positive numerator, so no strict integral premise is necessary. -/
lemma cubicPolarEnvelope_quadratic_pos {α : ℝ} (hα : 0 < α) :
    0 < (α * cubicPolarEnvelope α / 2) ^ 2 / 7 +
      2 * (α + 3) * (α * cubicPolarEnvelope α / 2) - α ^ 2 := by
  have hd : α + 3 ≠ 0 := by positivity
  have hid : (α * cubicPolarEnvelope α / 2) ^ 2 / 7 +
      2 * (α + 3) * (α * cubicPolarEnvelope α / 2) - α ^ 2 =
      α ^ 4 * (α ^ 4 + 360 * α ^ 3 + 2700 * α ^ 2 + 6480 * α + 4860) /
        (25200 * (α + 3) ^ 6) := by
    unfold cubicPolarEnvelope
    field_simp
    ring
  rw [hid]
  positivity

/-- Full integral-to-log bridge, with the original weak inequality. -/
lemma polar_le_log_sinh {α η : ℝ} (hα : 0 < α) (hη : η < 2)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - η) * t))) :
    α * η / 2 ≤ log (sinh (α - α * η / 2) / (α - α * η / 2)) := by
  rw [integral_exp_eq hα hη] at hpolar
  have hc : α * (2 - η) / 2 = α - α * η / 2 := by ring
  rw [hc, Real.exp_neg, inv_mul_eq_div,
    le_div_iff₀ (Real.exp_pos (α * η / 2)), one_mul] at hpolar
  calc
    α * η / 2 = log (exp (α * η / 2)) := (Real.log_exp _).symm
    _ ≤ log (sinh (α - α * η / 2) / (α - α * η / 2)) :=
      Real.log_le_log (Real.exp_pos _) hpolar

/-- The original weak polar constraint implies the STRICT cubic envelope.
Both `7/8` and `8/7` in the strong hyperbolic estimate are used unchanged. -/
theorem eta_lt_cubicPolarEnvelope {α η : ℝ} (hα : 0 < α) (h17 : α ≤ 17)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - η) * t))) :
    η < cubicPolarEnvelope α := by
  by_contra hnot
  have hηc : cubicPolarEnvelope α ≤ η := le_of_not_gt hnot
  set p := α * η / 2 with hpdef
  set x := α - p with hxdef
  set pc := α * cubicPolarEnvelope α / 2 with hpcdef
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hpc0 : 0 ≤ pc := by
    dsimp [pc]
    exact div_nonneg (mul_nonneg hα.le (cubicPolarEnvelope_nonneg hα.le)) (by norm_num)
  have hpcp : pc ≤ p := by dsimp [pc, p]; gcongr
  have hx0 : 0 < x := by
    dsimp [x, p]
    nlinarith [mul_pos hα (sub_pos.mpr hη1)]
  have hx10 : x < 10 := by
    have hc := cubicPolarEnvelope_center_lt_ten hα.le h17
    have hxp : x ≤ α * (1 - cubicPolarEnvelope α / 2) := by
      dsimp [x, p, pc] at *
      nlinarith
    exact hxp.trans_lt hc
  have hlog : p ≤ log (sinh x / x) := polar_le_log_sinh hα (by linarith) hpolar
  have hstrong : p ≤ (7 / 8 : ℝ) * (sqrt (9 + (8 / 7 : ℝ) * x ^ 2) - 3) :=
    hlog.trans (DistillationHyperbolic.log_sinh_div_le hx0 hx10.le)
  have hroot : (8 / 7 : ℝ) * p + 3 ≤ sqrt (9 + (8 / 7 : ℝ) * x ^ 2) := by
    linarith
  have hsq : sqrt (9 + (8 / 7 : ℝ) * x ^ 2) ^ 2 =
      9 + (8 / 7 : ℝ) * x ^ 2 := Real.sq_sqrt (by positivity)
  have hsquare : ((8 / 7 : ℝ) * p + 3) ^ 2 ≤ 9 + (8 / 7 : ℝ) * x ^ 2 := by
    nlinarith [sq_nonneg (sqrt (9 + (8 / 7 : ℝ) * x ^ 2) - ((8 / 7 : ℝ) * p + 3)),
      mul_nonneg (show 0 ≤ (8 / 7 : ℝ) * p + 3 by positivity)
        (sub_nonneg.mpr hroot)]
  have hF : p ^ 2 / 7 + 2 * (α + 3) * p - α ^ 2 ≤ 0 := by
    rw [hxdef] at hsquare
    nlinarith
  have hFc : 0 < pc ^ 2 / 7 + 2 * (α + 3) * pc - α ^ 2 :=
    cubicPolarEnvelope_quadratic_pos hα
  have hmono : pc ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ hpc0 hpcp 2
  nlinarith [mul_nonneg (show 0 ≤ 2 * (α + 3) by positivity)
    (sub_nonneg.mpr hpcp)]

/-- Old `a,x,n` coordinates: eta's domain follows from the original weak
polar hypothesis via the already proved Bridge, rather than an extra premise.
The separate original alpha bound may supply `h17`. -/
theorem actualEta_lt_cubicPolarEnvelope_of_polar {n : ℕ} (hn : 2 ≤ n)
    {a x α : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2) (h17 : α ≤ 17)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2)) :
    QQ (a * x) (a ^ 2) 1 < cubicPolarEnvelope α := by
  have hη := actualEta_mem_Ico_of_polar hn ha ha1 hx hα hpolar
  exact eta_lt_cubicPolarEnvelope (alpha_pos hn ha1 ha hα) h17 hη.1 hη.2
    (polar_exp hn hx hα hpolar)

end Sendov
