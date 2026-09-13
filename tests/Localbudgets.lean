import Sendov.Common.DistillationFinite
import Sendov.LargeDegree.DistillationTailBound

namespace Localbudgets

open Sendov

-- The m=60 formulas below are regression examples, not retained row consumers.
-- Raw central obligations cover the zero flank, internal brackets and the
-- point bracket at 17, with both integer and half-integer real exponents.
example :
    distillKappa 5 (1 / 2) * (96 * (3 / 5) ^ 4 /
      ((5 - 1) * (5 + 1) * (5 + 3) * (5 + 5) * (1 - distillNode 5 (3 / 4)) ^ 4)) ≤
      101 / 500 := by
  norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]

example :
    ((259 / 3125) * distillKappa 5 0) ^ 2 * (distillNode 5 (1 / 4)) ^ 2 ≤
      (191 / 1000 : ℝ) ^ 2 := by
  norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]

example :
    ((421 / 3125) * distillKappa 5 (1 / 2)) ^ 2 * (cubicPolarEnvelope (3 / 4)) ^ 2 ≤
      (37 / 250 : ℝ) ^ 2 := by
  norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]

example :
    ((259 / 3125) * distillKappa 6 (1 / 2)) ^ 2 * (distillNode 6 (3 / 4)) ^ 3 ≤
      (171 / 1000 : ℝ) ^ 2 := by
  norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]

example :
    ((421 / 3125) * distillKappa 6 (3 / 4)) ^ 2 * (cubicPolarEnvelope 1) ^ 3 ≤
      (133 / 1000 : ℝ) ^ 2 := by
  norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]

example :
    distillKappa 61 17 * (96 * (3 / 5) ^ 4 /
      ((61 - 1) * (61 + 1) * (61 + 3) * (61 + 5) * (1 - distillNode 61 17) ^ 4)) ≤
      57 / 250 := by
  norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]

example :
    ((259 / 3125) * distillKappa 60 17) ^ 2 * (distillNode 60 17) ^ 57 ≤
      (57 / 1000 : ℝ) ^ 2 := by
  norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]

example :
    ((421 / 3125) * distillKappa 60 17) ^ 2 * (cubicPolarEnvelope 17) ^ 57 ≤
      (81 / 250 : ℝ) ^ 2 := by
  norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]

example :
    ((259 / 3125) * distillKappa 61 17) ^ 2 * (distillNode 61 17) ^ 58 ≤
      (13 / 250 : ℝ) ^ 2 := by
  norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]

example :
    ((421 / 3125) * distillKappa 61 17) ^ 2 * (cubicPolarEnvelope 17) ^ 58 ≤
      (81 / 250 : ℝ) ^ 2 := by
  norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]

-- These closed numerical negations require no assumed sign identity or bound.
-- Each also checks that the emitted arithmetic tactic rejects the false goal.
theorem wrong_unsquared_budget : ¬ (
    distillKappa 5 (1 / 2) * (96 * (3 / 5) ^ 4 /
      ((5 - 1) * (5 + 1) * (5 + 3) * (5 + 5) * (1 - distillNode 5 (3 / 4)) ^ 4)) ≤
      201 / 1000) := by
  fail_if_success
    have h :
        distillKappa 5 (1 / 2) * (96 * (3 / 5) ^ 4 /
          ((5 - 1) * (5 + 1) * (5 + 3) * (5 + 5) *
            (1 - distillNode 5 (3 / 4)) ^ 4)) ≤ 201 / 1000 := by
      norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]
  norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]

theorem wrong_zero_flank_budget : ¬ (
    ((259 / 3125) * distillKappa 5 0) ^ 2 * (distillNode 5 (1 / 4)) ^ 2 ≤
      (19 / 100 : ℝ) ^ 2) := by
  fail_if_success
    have h :
        ((259 / 3125) * distillKappa 5 0) ^ 2 * (distillNode 5 (1 / 4)) ^ 2 ≤
          (19 / 100 : ℝ) ^ 2 := by
      norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]
  norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]

theorem wrong_scale : ¬ (
    ((518 / 3125) * distillKappa 6 (1 / 2)) ^ 2 * (distillNode 6 (3 / 4)) ^ 3 ≤
      (171 / 1000 : ℝ) ^ 2) := by
  fail_if_success
    have h :
        ((518 / 3125) * distillKappa 6 (1 / 2)) ^ 2 * (distillNode 6 (3 / 4)) ^ 3 ≤
          (171 / 1000 : ℝ) ^ 2 := by
      norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]
  norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]

theorem wrong_internal_exponent : ¬ (
    ((259 / 3125) * distillKappa 6 (1 / 2)) ^ 2 * (distillNode 6 (3 / 4)) ^ 2 ≤
      (171 / 1000 : ℝ) ^ 2) := by
  fail_if_success
    have h :
        ((259 / 3125) * distillKappa 6 (1 / 2)) ^ 2 * (distillNode 6 (3 / 4)) ^ 2 ≤
          (171 / 1000 : ℝ) ^ 2 := by
      norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]
  norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]

theorem wrong_endpoint_exponent : ¬ (
    ((421 / 3125) * distillKappa 60 17) ^ 2 * (cubicPolarEnvelope 17) ^ 56 ≤
      (81 / 250 : ℝ) ^ 2) := by
  fail_if_success
    have h :
        ((421 / 3125) * distillKappa 60 17) ^ 2 * (cubicPolarEnvelope 17) ^ 56 ≤
          (81 / 250 : ℝ) ^ 2 := by
      norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]
  norm_num only [distillKappa, distillRatio, distillNode, cubicPolarEnvelope]

theorem wrong_row_total :
    ¬ (distillEBudget 5 + 101 / 500 + 191 / 1000 + 37 / 250 ≤ 272 / 300) := by
  norm_num only [distillEBudget]

theorem wrong_rpow_exponent : ¬ (((6 : ℝ) - 3) / 2 = (2 : ℝ) / 2) := by norm_num

example (n : ℕ) : ((0 : ℝ) ^ ((n : ℝ) / 2)) ^ 2 = (0 : ℝ) ^ n :=
  distillRpow_half_sq le_rfl n

example : (2 : ℝ) * (1 / 4 : ℝ) ^ (((6 : ℝ) - 3) / 2) ≤ 1 / 4 := by
  exact distillMulRpow_le_of_sq 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : (2 : ℝ) * (0 : ℝ) ^ (((6 : ℝ) - 3) / 2) ≤ 0 := by
  exact distillMulRpow_le_of_sq 3 le_rfl le_rfl (by norm_num) (by norm_num)

example : distillT1 5 0 ≤ 191 / 1000 :=
  CriticalRow5.component1 0 le_rfl (by norm_num)

example (α : ℝ) (hα : 0 ≤ α) (hd : α ≤ 17) :
    distillT0 61 α ≤ 57 / 250 ∧ distillT1 61 α ≤ 13 / 250 ∧
      distillT2 61 α ≤ 81 / 250 :=
  ⟨CriticalRow61.component0 α hα hd, CriticalRow61.component1 α hα hd,
    CriticalRow61.component2 α hα hd⟩

example : distillEBudget 61 + distillT0 61 17 + distillT1 61 17 + distillT2 61 17 <
    199 / 200 :=
  (distillFinite_61 17 (by norm_num) le_rfl).trans_lt distillFiniteBound_61

example {m : ℕ} (hm : 5 ≤ m) (hm60 : m ≤ 60) {α : ℝ} (hα : 0 ≤ α)
    (hαm : α ≤ (m : ℝ) / 2) (h17 : α ≤ 17) :
    distillEBudget m + distillT0 m α + distillT1 m α + distillT2 m α < 199 / 200 :=
  distillFinite_components hm hm60 hα hαm h17

example {m α : ℝ} (hm : 61 ≤ m) (hα : 0 ≤ α) (h17 : α ≤ 17) :
    distillEBudget m + distillT0 m α + distillT1 m α + distillT2 m α < 199 / 200 :=
  distillComponents_lt_199_200 hm hα h17

end Localbudgets
