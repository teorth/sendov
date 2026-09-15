import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

/-! Uniform finite-ray comparisons from round5 §5.4. These compare the
analytic upper and lower bounds; the analytic bounds themselves are separate.
A single monotonic comparison carries each base inequality to every real m≥256. -/
namespace Sendov.PaperRay

/-- A generic base-to-ray comparison, preserving every parameter. -/
theorem compare_from_base {M m C E K z : ℝ} (hM : 0 < M) (hm : M ≤ m)
    (hE : 0 ≤ E) (hK : 0 ≤ K) (hC : 0 ≤ C - E / M)
    (hbase : 1 + K / M + z < M / (M + 1) * (C - E / M)) :
    1 + K / m + z < m / (m + 1) * (C - E / m) := by
  have hm0 : 0 < m := lt_of_lt_of_le hM hm
  have hM1 : 0 < M + 1 := by linarith
  have hm1 : 0 < m + 1 := by linarith
  have hfrac : M / (M + 1) ≤ m / (m + 1) := by
    apply (div_le_div_iff₀ hM1 hm1).2
    nlinarith
  have hEdiv : E / m ≤ E / M := by
    apply (div_le_div_iff₀ hm0 hM).2
    nlinarith
  have hKdiv : K / m ≤ K / M := by
    apply (div_le_div_iff₀ hm0 hM).2
    nlinarith
  have hleft : 0 ≤ M / (M + 1) := by positivity
  have hright : 0 ≤ m / (m + 1) := by positivity
  have hprod : M / (M + 1) * (C - E / M) ≤ m / (m + 1) * (C - E / m) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hfrac) hC,
      mul_nonneg hright (sub_nonneg.mpr hEdiv)]
  linarith

/-- The ray 1/5 ≤ lambda ≤ 1. -/
theorem ray_one {m : ℝ} (hm : 256 ≤ m) :
    1 + 18 / m < m / (m + 1) * (1 + (24 / 49 - 8 / m) / 5) := by
  have h := compare_from_base (M := 256) (C := 1 + 24 / 245)
    (E := 8 / 5) (K := 18) (z := 0) (by norm_num) hm
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> ring

/-- The ray 1 ≤ lambda ≤ 5. -/
theorem ray_two {m : ℝ} (hm : 256 ≤ m) :
    1 + 33 / m < m / (m + 1) * (1 + 6 / 25 - 24 / m) := by
  simpa using compare_from_base (M := 256) (C := 1 + 6 / 25)
    (E := 24) (K := 33) (z := 0) (by norm_num) hm
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The ray 5 ≤ lambda ≤ 10. -/
theorem ray_three {m : ℝ} (hm : 256 ≤ m) :
    1 + 33 / m < m / (m + 1) * (6 * (7 / 12) ^ 2) := by
  simpa using compare_from_base (M := 256) (C := 6 * (7 / 12) ^ 2)
    (E := 0) (K := 33) (z := 0) (by norm_num) hm
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The ray 10 ≤ lambda ≤ 25. -/
theorem ray_four {m : ℝ} (hm : 256 ≤ m) :
    1 + 51 / m + 1 / 4 < m / (m + 1) * (11 * (231 / 512) ^ 2) := by
  simpa using compare_from_base (M := 256) (C := 11 * (231 / 512) ^ 2)
    (E := 0) (K := 51) (z := 1 / 4) (by norm_num) hm
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The ray 25 ≤ lambda ≤ 49. -/
theorem ray_five {m : ℝ} (hm : 256 ≤ m) :
    1 + 62 / m + 2 < m / (m + 1) * (26 * (207 / 512) ^ 2) := by
  simpa using compare_from_base (M := 256) (C := 26 * (207 / 512) ^ 2)
    (E := 0) (K := 62) (z := 2) (by norm_num) hm
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Sendov.PaperRay
