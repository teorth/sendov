import Sendov.Common.DistillationMajorant
import Sendov.LargeDegree.DistillationTail
import Sendov.DistillationFinite.Rows53_55
import Sendov.DistillationFinite.Rows61_61

/-!
# The proved bounded interval and infinite tail

The existing critical-point row at `m = 61` supplies the earlier `<199/200`
tail, starting at polynomial degree 62. No finite base or monotonicity is assumed.
The original row 55 separately closes the real interval `55 <= m <= 61`.
The underlying mathematical route is Senjian An's *Proof Distillation for Sendov's
Conjecture*, revision e8ae601491ec171ab4f7f8456113dd6a047aa85d, Sections 7--8
(CC BY 4.0, https://creativecommons.org/licenses/by/4.0/).
-/

namespace Sendov

/-- A real-degree interval, not a finite case split. The original row 55 supplies
the three base budgets internally; bounded growth is allowed for both powers. -/
theorem distillComponents_interval_55_61 {m α : ℝ} (hm : m ∈ Set.Icc 55 61)
    (hα : 0 ≤ α) (h17 : α ≤ 17) :
    distillEBudget m + distillT0 m α + distillT1 m α + distillT2 m α < 199 / 200 := by
  have hm5 : 5 ≤ m := by have := hm.1; linarith
  have hE := distillEBudget_antitone_on (K := 55) (by norm_num)
    (by simp) hm.1 hm.1
  have h0 := (distillT0_antitone_55 hα h17 (by simp) hm.1 hm.1).trans
    (CriticalRow55.component0 α hα h17)
  have hnode : distillNode 55 α ≤ (979 / 1000) ^ 10 :=
    (distillNode_mono (by norm_num) hα h17).trans
      (by norm_num [distillNode, cubicPolarEnvelope])
  have h1 := distillKappa_rpow_interval (K := 55) (U := 61)
    (ε := 331 / 37800) 10 (by norm_num) hm (by norm_num) (by norm_num)
    (by norm_num) hα h17 (distillNode_pos (by norm_num) hα).le
    (by norm_num : (0 : ℝ) < 979 / 1000) hnode
  have hpow := Real.rpow_le_rpow (distillNode_pos (by linarith) hα).le
    (distillNode_antitone_degree_on (K := 55) (by norm_num) hα
      (by simp) hm.1 hm.1) (by linarith : 0 ≤ (m - 3) / 2)
  have h1' := (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (distillKappa_nonneg hm5 hα))
    (by norm_num : (0 : ℝ) ≤ 1 - 331 / 37800 * (61 - 55))).trans h1
  have h1'' : distillT1 m α * (1 - 331 / 37800 * (61 - 55)) ≤ 91 / 1000 := by
    apply le_trans _ (CriticalRow55.component1 α hα h17)
    simpa only [distillT1, mul_assoc] using
      mul_le_mul_of_nonneg_left h1' (by norm_num : (0 : ℝ) ≤ 259 / 3125)
  have h2 := distillKappa_rpow_interval (K := 55) (U := 61)
    (ε := 95 / 4158) 4 (by norm_num) hm (by norm_num) (by norm_num)
    (by norm_num) hα h17 (cubicPolarEnvelope_nonneg hα)
    (by norm_num : (0 : ℝ) < 21 / 22) (cubicPolarEnvelope_le_decay_base hα h17)
  have h2' : distillT2 m α * (1 - 95 / 4158 * (61 - 55)) ≤ 33 / 100 := by
    apply le_trans _ (CriticalRow55.component2 α hα h17)
    simpa only [distillT2, mul_assoc] using
      mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 421 / 3125)
  norm_num [distillEBudget] at hE ⊢
  linarith

/-- The existing finite row closes the earlier tail on the full closed alpha
domain, including zero. No stronger row certificate at m=61 is required. -/
theorem distillComponents_lt_199_200 {m α : ℝ} (hm : 61 ≤ m)
    (hα : 0 ≤ α) (h17 : α ≤ 17) :
    distillEBudget m + distillT0 m α + distillT1 m α + distillT2 m α < 199 / 200 :=
  (distillComponents_le_61 hm hα h17).trans_lt
    ((distillFinite_61 α hα h17).trans_lt distillFiniteBound_61)

/-- Earlier raw scalar tail. Positive alpha is intentional; all of `α ≤ 17`
is covered, and `2 * α ≤ m` follows from the degree threshold. -/
theorem distillScalar_lt_199_200 {m α : ℝ} (hm : 61 ≤ m)
    (hα : 0 < α) (h17 : α ≤ 17) :
    scalarObstruction m α (cubicPolarEnvelope α) < 199 / 200 := by
  exact (distillScalar_le_majorant (by linarith) hα (by linarith)).trans_lt
    (distillComponents_lt_199_200 hm hα.le h17)

end Sendov
