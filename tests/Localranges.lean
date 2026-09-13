import Sendov.Common.DistillationBounds

open Sendov

example {m : ℝ} (hm : m ∈ Set.Icc 55 61) :
    distillEBudget m + distillT0 m 0 + distillT1 m 0 + distillT2 m 0 < 199 / 200 :=
  distillComponents_interval_55_61 hm le_rfl (by norm_num)

example {α : ℝ} (hα : 0 ≤ α) (h17 : α ≤ 17) :
    distillEBudget 55 + distillT0 55 α + distillT1 55 α + distillT2 55 α < 199 / 200 :=
  distillComponents_interval_55_61 (by norm_num) hα h17

example :
    distillEBudget (111 / 2) + distillT0 (111 / 2) 17 +
      distillT1 (111 / 2) 17 + distillT2 (111 / 2) 17 < 199 / 200 :=
  distillComponents_interval_55_61 (by norm_num) (by norm_num) le_rfl

example {α : ℝ} (hα : 0 ≤ α) (h17 : α ≤ 17) :
    distillEBudget 61 + distillT0 61 α + distillT1 61 α + distillT2 61 α < 199 / 200 :=
  distillComponents_interval_55_61 (by norm_num) hα h17

example {m : ℕ} (hm : 56 ≤ m) (h60 : m ≤ 60) {α : ℝ}
    (hα : 0 ≤ α) (h17 : α ≤ 17) :
    distillEBudget m + distillT0 m α + distillT1 m α + distillT2 m α < 199 / 200 := by
  exact distillFinite_components (by omega) h60 hα
    (by
      have hmR : (56 : ℝ) ≤ m := by exact_mod_cast hm
      linarith) h17

example {n : ℕ} (hn : 6 ≤ n) {α : ℝ} (hα : 0 < α) (h17 : α ≤ 17)
    (hhalf : 2 * α ≤ M n) :
    scalarObstruction (M n) α (cubicPolarEnvelope α) < 1 :=
  distillScalar_lt_one hn hα h17 hhalf

example : scalarObstruction 5 (5 / 2) (cubicPolarEnvelope (5 / 2)) < 199 / 200 := by
  exact distillFinite_scalar (m := 5) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

example {m : ℝ} (hm : m ∈ Set.Icc 55 61) :
    (distillKappa m 0 * (0 : ℝ) ^ ((m - 3) / 2)) *
      (1 - 95 / 4158 * (61 - 55)) ≤
        distillKappa 55 0 * (0 : ℝ) ^ (((55 : ℝ) - 3) / 2) :=
  distillKappa_rpow_interval (ε := 95 / 4158) 4 (by norm_num) hm (by norm_num) (by norm_num)
    (by norm_num) le_rfl (by norm_num) le_rfl
    (by norm_num : (0 : ℝ) < 21 / 22) (by norm_num)

example : ¬ (54 : ℝ) ∈ Set.Icc 55 61 := by norm_num
example : ¬ (123 / 2 : ℝ) ∈ Set.Icc 55 61 := by norm_num
example : ¬ (18 : ℝ) ≤ 17 := by norm_num

example : (1 / 54 + 2 / 21 : ℝ) > 1 / 11 := by norm_num
example : (43 / 165 + 31 / 125 +
    (91 / 1000) / (1 - 331 / 37800 * 7) +
    (33 / 100) / (1 - 95 / 4158 * 7) : ℝ) > 199 / 200 := by norm_num
