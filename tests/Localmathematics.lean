import Sendov.LargeDegree.DistillationTail

namespace MathematicsFeasibility
open Sendov

theorem decay_base : cubicPolarEnvelope 17 ≤ (21 / 22 : ℝ) ^ 4 := by
  norm_num [cubicPolarEnvelope]

theorem log_decay {z : ℝ} (hz : 0 < z) (hcap : z ≤ (21 / 22 : ℝ) ^ 4) :
    Real.log z / 2 ≤ -(1 / 11) := by
  have hlog := Real.log_le_log hz hcap
  rw [Real.log_pow] at hlog
  have hlinear := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 21 / 22)
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

theorem start61 : (1 / (61 - 1) + 2 / (61 - 34) : ℝ) ≤ 1 / 11 := by
  norm_num

theorem start60_not_this_certificate :
    ¬ (1 / (60 - 1) + 2 / (60 - 34) : ℝ) ≤ 1 / 11 := by norm_num

example {α : ℝ} (hα : 0 ≤ α) (h17 : α ≤ 17) :
    AntitoneOn (fun m : ℝ => distillKappa m α * (5 / 6 : ℝ) ^ ((m - 3) / 2))
      (Set.Ici 64) :=
  distillKappa_rpow_antitone_on (by norm_num) (by norm_num)
    hα h17 (by norm_num) le_rfl

example {α : ℝ} (hα : 0 ≤ α) (h17 : α ≤ 17) :
    AntitoneOn (fun m : ℝ => distillKappa m α * (0 : ℝ) ^ ((m - 3) / 2))
      (Set.Ici 61) :=
  distillKappa_rpow_antitone_of_pow 4 (by norm_num) (by norm_num)
    hα h17 le_rfl (by norm_num : (0 : ℝ) < 21 / 22) (by norm_num)

theorem zero34 : distillT2 34 17 = 0 := by
  norm_num [distillT2, distillKappa]

theorem positive35 : 0 < distillT2 35 17 := by
  have hk : 0 < distillKappa 35 17 := by norm_num [distillKappa, distillRatio]
  have he : 0 < cubicPolarEnvelope 17 := by norm_num [cubicPolarEnvelope]
  exact mul_pos (mul_pos (by norm_num) hk) (Real.rpow_pos_of_pos he _)

theorem increase59_61 : distillT2 59 17 < distillT2 61 17 := by
  norm_num [distillT2, distillKappa, distillRatio, cubicPolarEnvelope,
    show ((59 : ℝ) - 3) / 2 = (28 : ℕ) by norm_num,
    show ((61 : ℝ) - 3) / 2 = (29 : ℕ) by norm_num, Real.rpow_natCast]

theorem no_antitone_start_le_59 {K : ℝ} (hK : K ≤ 59) :
    ¬ AntitoneOn (fun m : ℝ => distillT2 m 17) (Set.Ici K) := by
  intro h
  exact (not_le_of_gt increase59_61)
    (h hK (hK.trans (by norm_num)) (by norm_num))

example : 2 * (17 : ℝ) ≤ 34 ∧ 2 * (17 : ℝ) ≤ 35 ∧
    2 * (17 : ℝ) ≤ 59 ∧ 2 * (17 : ℝ) ≤ 61 := by norm_num

#print axioms no_antitone_start_le_59
#print axioms log_decay
end MathematicsFeasibility
