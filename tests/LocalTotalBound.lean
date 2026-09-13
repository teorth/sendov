import Sendov.Common.DistillationTotalBound

namespace LocalTotalBound
open Sendov MeasureTheory

theorem small_alpha_real_ray {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hα1 : α ≤ 7 / 5) :
    scalarObstruction m α (cubicPolarEnvelope α) < 1 :=
  distillScalar_lt_one_small_alpha hm hα hα1

theorem whole_chord_real_frontier :
    distillChordTotal (25 / 2) (17 / 12) = 1 + 141383 / 711868500 := by
  norm_num [distillChordTotal, distillEBudget]

theorem whole_chord_integer_frontier :
    distillChordTotal 13 (10 / 7) = 1 + 426061 / 212373252 := by
  norm_num [distillChordTotal, distillEBudget]

private lemma integral_quadratic (A b : ℝ) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * (1 - b * t + A * t ^ 2)) =
      1 / 4 - b / 5 + A / 6 := by
  have hid : (fun t : ℝ => t ^ 3 * (1 - b * t + A * t ^ 2)) =
      fun t => t ^ 3 - b * t ^ 4 + A * t ^ 5 := by funext t; ring
  rw [hid]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private lemma integral_quadratic_sq (A b : ℝ) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * (1 - b * t + A * t ^ 2) ^ 2) =
      1 / 4 - 2 * b / 5 + (b ^ 2 + 2 * A) / 6 - 2 * A * b / 7 + A ^ 2 / 8 := by
  have hid : (fun t : ℝ => t ^ 3 * (1 - b * t + A * t ^ 2) ^ 2) =
      fun t => t ^ 3 - (2 * b) * t ^ 4 + (b ^ 2 + 2 * A) * t ^ 5 -
        (2 * A * b) * t ^ 6 + A ^ 2 * t ^ 7 := by funext t; ring
  rw [hid]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

theorem raw_five_at_one :
    scalarObstruction 5 1 (cubicPolarEnvelope 1) = 4104463139 / 7377920000 := by
  have hQ (t : ℝ) : polarKernel 5 1 (cubicPolarEnvelope 1) t =
      1 - (2593 / 1920) * t + (3 / 5) * t ^ 2 := by
    norm_num [polarKernel, cubicPolarEnvelope]
    ring
  simp only [scalarObstruction, show ((5 : ℝ) - 3) / 2 = 1 by norm_num,
    Real.rpow_one, hQ, integral_quadratic]
  norm_num [cubicPolarEnvelope]

theorem raw_seven_at_one :
    scalarObstruction 7 1 (cubicPolarEnvelope 1) = 280207725981353 / 489767341916160 := by
  have hQ (t : ℝ) : polarKernel 7 1 (cubicPolarEnvelope 1) t =
      1 - (19687 / 13440) * t + (5 / 7) * t ^ 2 := by
    norm_num [polarKernel, cubicPolarEnvelope]
    ring
  simp only [scalarObstruction, show ((7 : ℝ) - 3) / 2 = (2 : ℕ) by norm_num,
    Real.rpow_natCast, hQ, integral_quadratic_sq]
  norm_num [cubicPolarEnvelope]

theorem raw_increases_5_7 :
    scalarObstruction 5 1 (cubicPolarEnvelope 1) <
      scalarObstruction 7 1 (cubicPolarEnvelope 1) := by
  rw [raw_five_at_one, raw_seven_at_one]
  norm_num

theorem no_raw_antitone_start_le_5 {K : ℝ} (hK : K ≤ 5) :
    ¬ AntitoneOn (fun m : ℝ => scalarObstruction m 1 (cubicPolarEnvelope 1))
      (Set.Ici K) := by
  intro h
  exact (not_le_of_gt raw_increases_5_7)
    (h hK (hK.trans (by norm_num)) (by norm_num))

theorem raw_zero_not_regularized :
    scalarObstruction 5 0 (cubicPolarEnvelope 0) = 1 / 10 ∧
      distillEBudget 5 - distillElementaryLoss 5 0 = 11 / 30 := by
  rw [scalarObstruction_zero]
  norm_num [distillEBudget, distillElementaryLoss, cubicPolarEnvelope]

end LocalTotalBound
