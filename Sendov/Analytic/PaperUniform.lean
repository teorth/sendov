import Sendov.Analytic.PaperGlobalPolar
import Sendov.Analytic.PaperTwoEnd
import Sendov.Analytic.PaperTail
import Sendov.Analytic.PaperRayGeometry
import Sendov.Analytic.PaperNear
import Sendov.Analytic.PaperBulkAlgebra

/-! # Uniform D for all natural degrees at least 256

The two-endpoint integral bounds give both a global two-thirds bound and a
retained-radius bound. The remaining continuous rays use sharp Laplace and
raw-polar geometry. No analytic estimate is assumed by the public theorem.
-/
namespace Sendov.PaperUniform

open PaperPolar

lemma beta_one (a x : ℝ) : PaperTaylor.beta a x 1 = b a x := by
  simp only [PaperTaylor.beta, b, mul_one, one_pow]

lemma chord_eq (a x : ℝ) : PaperTaylor.chord a x = c a x := by
  unfold PaperTaylor.chord c b
  ring

/-- A single rational Taylor certificate, independent of the degree. -/
lemma exp_seventeen_fifths : (29 : ℝ) < Real.exp (17 / 5 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 17 / 5) 16
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h
  linarith

lemma middle_relax {m x : ℝ} (hm : 256 ≤ m) :
    (1 + 5 * m * x ^ 2 / 8) * Real.exp (-3 * (m - 1) * x ^ 2 / 8) ≤
      (1 + 5 * (m * x ^ 2) / 8) * Real.exp (-(11 / 30 : ℝ) * (m * x ^ 2)) := by
  have hm0 : 0 ≤ m := by linarith
  rw [mul_assoc 5 m (x ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_nonneg (show 0 ≤ m - 45 by linarith) (sq_nonneg x)]

variable {m : ℕ} {a x : ℝ}

/-- The actual integral budget is globally less than two thirds. -/
theorem budget_lt_two_thirds (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) : PaperTaylor.budget (m : ℝ) a x < 2 / 3 := by
  have hm' : (256 : ℝ) ≤ m := by exact_mod_cast hm
  have hm7 : (7 : ℝ) ≤ m := by linarith
  obtain ⟨hax, hc⟩ := geometry (by omega : 7 ≤ m) ha ha1 hx0 hx1 hr
  have hx : 0 < x := by linarith
  have hk := PaperGlobalPolar.degree_mul_sq_gt hm ha ha1 hx0 hx1 hr
  have he := PaperGlobalPolar.endpoint_le (by omega) ha ha1 hx0 hx1 hr
  rw [← beta_one] at he
  have hleft : 4 / ((m : ℝ) * x ^ 2) < 8 / 19 := by
    apply (div_lt_iff₀ (by positivity : 0 < (m : ℝ) * x ^ 2)).mpr
    linarith
  by_cases hs : a ≤ x ∨ 3 * x / 2 ≤ a
  · have ht := PaperTwoEnd.budget_lt_separated hm7 ha ha1 hx hx1
      (by rw [chord_eq]; exact hc) hs
    have he' : 4 / ((m : ℝ) + 2) ≤ 4 / 258 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
      linarith
    linarith
  · push Not at hs
    have ht := (PaperTwoEnd.budget_lt_middle hm7 ha ha1 hx hx1 hs.1 hs.2).trans_le
      (add_le_add le_rfl (middle_relax (x := x) hm'))
    have hf := PaperTail.middle_antitone
      (show (19 / 2 : ℝ) ∈ Set.Ici (19 / 2) by simp) hk.le hk.le
    have hexp : Real.exp (-(11 / 30 : ℝ) * (19 / 2)) ≤ Real.exp (-(17 / 5 : ℝ)) :=
      Real.exp_le_exp.mpr (by norm_num)
    have hinv : Real.exp (-(17 / 5 : ℝ)) < 1 / 29 := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_lt_one_div_of_lt (by norm_num) exp_seventeen_fifths
    have hf' := mul_le_mul_of_nonneg_left (hexp.trans hinv.le)
      (by norm_num : (0 : ℝ) ≤ 1 + 5 * (19 / 2) / 8)
    dsimp at hf
    linarith

/-- Retaining a in the left endpoint term is essential at degree 256. -/
theorem budget_lt_retained (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (ha3 : 1 / 3 ≤ a)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hr : RawPolar m a x) :
    PaperTaylor.budget (m : ℝ) a x < 16 / ((m : ℝ) * a ^ 2) + 24 / (m : ℝ) := by
  have hm' : (256 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hm7 : (7 : ℝ) ≤ m := by linarith
  obtain ⟨hax, hc⟩ := geometry (by omega : 7 ≤ m) ha ha1 hx0 hx1 hr
  have hx : 0 < x := by linarith
  have hleft : 4 / ((m : ℝ) * x ^ 2) < 16 / ((m : ℝ) * a ^ 2) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    have hs : a ^ 2 < 4 * x ^ 2 := by nlinarith
    nlinarith only [mul_pos hm0 (sub_pos.mpr hs)]
  by_cases hs : a ≤ x ∨ 3 * x / 2 ≤ a
  · have ht := PaperTwoEnd.budget_lt_separated hm7 ha ha1 hx hx1
      (by rw [chord_eq]; exact hc) hs
    have he := PaperGlobalPolar.endpoint_le (by omega) ha ha1 hx0 hx1 hr
    rw [← beta_one] at he
    have he' : 4 / ((m : ℝ) + 2) ≤ 4 / (m : ℝ) := by
      apply (div_le_div_iff₀ (by positivity) hm0).mpr
      linarith
    simp only [div_eq_mul_inv] at he he' ht hleft ⊢
    linarith
  · push Not at hs
    have ht := (PaperTwoEnd.budget_lt_middle hm7 ha ha1 hx hx1 hs.1 hs.2).trans_le
      (add_le_add le_rfl (middle_relax (x := x) hm'))
    have hx2 : (4 / 81 : ℝ) ≤ x ^ 2 := by nlinarith
    have hk : (4 : ℝ) * m / 81 ≤ (m : ℝ) * x ^ 2 := by
      nlinarith only [mul_le_mul_of_nonneg_left hx2 hm0.le]
    have hbase : (19 / 2 : ℝ) ≤ 4 * m / 81 := by linarith
    have hf := PaperTail.middle_antitone hbase (hbase.trans hk) hk
    have htail := PaperTail.middle_tail hm'
    have heq : (1 + 5 * ((4 : ℝ) * m / 81) / 8) *
        Real.exp (-(11 / 30 : ℝ) * (4 * m / 81)) =
        (1 + 5 * (m : ℝ) / 162) * Real.exp (-22 * m / 1215) := by
      rw [show -(11 / 30 : ℝ) * (4 * m / 81) = -22 * m / 1215 by ring]
      congr 1
      ring
    dsimp at hf
    rw [heq] at hf
    have hf' : (1 + 5 * ((m : ℝ) * x ^ 2) / 8) *
        Real.exp (-(11 / 30 : ℝ) * ((m : ℝ) * x ^ 2)) < 24 / (m : ℝ) := by
      apply (lt_div_iff₀ hm0).mpr
      have hh := mul_le_mul_of_nonneg_left hf hm0.le
      nlinarith only [hh, htail]
    linarith

/-- Closure of the four finite continuous rays, including all seams. -/
theorem finite_rays_D (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (hl0 : 2 / 5 ≤ lambda m a) (hl1 : lambda m a ≤ 49) :
    PaperTaylor.budget (m : ℝ) a x < 1 - (m : ℝ) * a / ((m : ℝ) + 1) := by
  have hm' : (256 : ℝ) ≤ m := by exact_mod_cast hm
  have hx : 0 < x := by
    have := (geometry (by omega : 7 ≤ m) ha ha1 hx0 hx1 hr).1
    linarith
  have hxa : x < 2 * a :=
    (div_lt_one (by positivity : 0 < 2 * a)).mp
      (PaperRayGeometry.halfpoint_mem hm ha ha1 hx0 hx1 hr hl1).2
  apply PaperRayGeometry.lt_B_of_scaled_lt (by omega : 0 < m) hx
  by_cases hl : lambda m a ≤ 1
  · have hg := PaperRayGeometry.geometry_one hm ha ha1 hx0 hx1 hr hl
    have hb := (PaperRayGeometry.geometry_ten hm ha ha1 hx0 hx1 hr (by linarith)).1
    rw [← beta_one] at hb
    exact (PaperTail.budget_region_one hm' ha ha1 hg hx1 hxa hb.le).trans
      (PaperRayGeometry.budget_lower_one hm ha ha1 hx0 hx1 hr hl0 hl)
  by_cases hl10 : lambda m a ≤ 10
  · obtain ⟨hb, hg⟩ := PaperRayGeometry.geometry_ten hm ha ha1 hx0 hx1 hr hl10
    rw [← beta_one] at hb
    exact (PaperTail.budget_region_two hm' ha ha1 hg hx1 hxa hb.le).trans
      (PaperRayGeometry.budget_lower_ten hm ha ha1 hx0 hx1 hr (by linarith) hl10)
  by_cases hl25 : lambda m a ≤ 25
  · obtain ⟨hb, hg⟩ := PaperRayGeometry.geometry_twentyfive hm ha ha1 hx0 hx1 hr hl25
    rw [← beta_one] at hb
    exact (PaperTail.budget_region_three hm' ha ha1 hg hx1 hxa hb.le).trans
      (PaperRayGeometry.budget_lower_twentyfive hm ha ha1 hx0 hx1 hr (by linarith) hl25)
  · obtain ⟨hb, hg⟩ := PaperRayGeometry.geometry_fortynine hm ha ha1 hx0 hx1 hr hl1
    rw [← beta_one] at hb
    exact (PaperTail.budget_region_four hm' ha ha1 hg hx1 hxa hb.le).trans
      (PaperRayGeometry.budget_lower_fortynine hm ha ha1 hx0 hx1 hr (by linarith) hl1)

/-- All a, with only the raw polar integral and the stated domain assumptions. -/
theorem uniform_D (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) :
    PaperTaylor.budget (m : ℝ) a x < 1 - (m : ℝ) * a / ((m : ℝ) + 1) := by
  have hm' : (256 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  by_cases ha3 : a ≤ 1 / 3
  · exact PaperBulk.direct_budget_small hm0.le ha ha3
      (budget_lt_two_thirds hm ha ha1 hx0 hx1 hr)
  have ht := budget_lt_retained hm ha ha1 (by linarith) hx0 hx1 hr
  by_cases ha4 : a ≤ 4 / 5
  · exact PaperBulk.direct_budget_middle hm' (by linarith) ha4 ht
  by_cases hl49 : 49 ≤ lambda m a
  · have hbulk := PaperBulk.large_ray_budget hm0 (by linarith : 4 / 5 ≤ a) hl49
    have hgap : 1 - a < 1 - (m : ℝ) * a / ((m : ℝ) + 1) := by
      have heq : 1 - (m : ℝ) * a / ((m : ℝ) + 1) =
          1 - a + a / ((m : ℝ) + 1) := by field_simp; ring
      rw [heq]
      have := div_pos ha (show (0 : ℝ) < m + 1 by positivity)
      linarith
    exact (ht.trans_le hbulk).trans hgap
  by_cases hlnear : lambda m a ≤ 2 / 5
  · have hn := PaperNearClosure.near_endpoint_D (by omega) ha ha1 hx0 hx1 hr hlnear
    have hp : 0 < (1 - a) / 1000 := by positivity
    linarith
  · exact finite_rays_D hm ha ha1 hx0 hx1 hr (by linarith) (by linarith)

end Sendov.PaperUniform
