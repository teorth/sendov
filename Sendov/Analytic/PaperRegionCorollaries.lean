import Sendov.Analytic.PaperConsequences
import Sendov.Analytic.PaperRateDetails

/-!
# Literal region corollaries of the paper

The eleven acceptance families are exported with the actual integral expression T.
All ray intervals are closed, so adjacent bands both apply at each seam. The
first ray starts at 1/5, including the full interval [1/5,2/5).
Only the paper's conditional bulk estimates retain a bulk hypothesis.
-/
namespace Sendov.PaperRegionCorollaries

open PaperPolar

private lemma literal_budget (m : ℕ) (a x : ℝ) :
    ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) =
      PaperTaylor.budget (m : ℝ) a x := by
  simp only [PaperTaylor.budget, PaperTaylor.beta, mul_one, one_pow]

/-- IN02: both finite two-end estimates, with exact denominators and endpoint rates. -/
theorem in02_two_end {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) :
    (((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) ≤ 100 * (m : ℝ) /
      (9 * ((m : ℝ) + 1) * ((m : ℝ) + 3) * x ^ 2) +
      29 * (1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2)) ∧
    (((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) ≤ 16 * (m : ℝ) /
      (((m : ℝ) + 1) * ((m : ℝ) + 3) * x ^ 2) +
      13 * (1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2)) := by
  simp only [literal_budget]
  obtain ⟨hax, hc⟩ := geometry hm ha ha1 hx0 hx1 hr
  have hx : 0 < x := by linarith
  have hc' : 0 < PaperTaylor.chord a x := by
    rw [PaperUniform.chord_eq]
    exact hc
  have h₁ := PaperHistoricalBounds.total_le_A5 (m := (m : ℝ))
    (by exact_mod_cast hm) ha ha1 hx hx1 hc'
  have h₂ := PaperHistoricalBounds.total_le_A5b (m := (m : ℝ))
    (by exact_mod_cast hm) ha ha1 hx hx1 hc'
  rw [PaperTwoEnd.total_eq_budget ha] at h₁ h₂
  constructor
  · simpa only [PaperTaylor.budget, PaperTaylor.beta, PaperTwoEnd.endpoint,
      PaperTwoEnd.Q, mul_one, one_pow, mul_right_comm] using h₁
  · simpa only [PaperTaylor.budget, PaperTaylor.beta, PaperTwoEnd.endpoint,
      PaperTwoEnd.Q, mul_one, one_pow, mul_right_comm] using h₂

/-- IN04: retain the original exponent at m=7,8; relax only from m=9. -/
theorem in04_middle {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx : 0 < x) (hx1 : x ≤ 1)
    (hxa : x < a) (hax : a < 3 * x / 2) :
    (((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 4 / ((m : ℝ) * x ^ 2) +
      (1 + 5 * ((m : ℝ) * x ^ 2) / 8) *
        Real.exp (-3 * ((m : ℝ) - 1) * ((m : ℝ) * x ^ 2) / (8 * (m : ℝ)))) ∧
    (9 ≤ m → ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 4 / ((m : ℝ) * x ^ 2) +
      (1 + 5 * ((m : ℝ) * x ^ 2) / 8) * Real.exp (-((m : ℝ) * x ^ 2) / 3)) := by
  simp only [literal_budget]
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have ht := PaperTwoEnd.budget_lt_middle hm' ha ha1 hx hx1 hxa hax
  change PaperTaylor.budget (m : ℝ) a x < _ ∧
    (9 ≤ m → PaperTaylor.budget (m : ℝ) a x < _)
  constructor
  · convert ht using 1; field_simp
  · intro hm9
    have hm9' : (9 : ℝ) ≤ m := by exact_mod_cast hm9
    apply ht.trans_le
    apply add_le_add le_rfl
    rw [mul_assoc 5 (m : ℝ) (x ^ 2)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg (show 0 ≤ (m : ℝ) - 9 by linarith) (sq_nonneg x)]

/-- NE05: the original lambda ≤ 3/10 margin. -/
theorem ne05_near {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x)
    (hl : lambda m a ≤ 3 / 10) :
    (1 - (m : ℝ) * a / ((m : ℝ) + 1)) - ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) > (1 - a) / 1000 := by
  simp only [literal_budget]
  exact PaperNearClosure.near_endpoint_D hm ha ha1 hx0 hx1 hr (by
    change (m : ℝ) * (1 - a) ≤ 3 / 10 at hl
    linarith)

private lemma h_lt_B {m : ℕ} {a : ℝ} (ha : 0 < a) :
    1 - a < (1 - (m : ℝ) * a / ((m : ℝ) + 1)) := by
  have hd : 0 < (m : ℝ) + 1 := by positivity
  have he : (1 - (m : ℝ) * a / ((m : ℝ) + 1)) - (1 - a) = a / ((m : ℝ) + 1) := by field_simp; ring
  have hp := div_pos ha hd
  linarith

/-- UN04: retained-radius rate, and the original conditional strict chain. -/
theorem un04_bulk40 {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x)
    (ha2 : 2 / 5 ≤ a) :
    (((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 40 / ((m : ℝ) * a ^ 2)) ∧
    (40 ≤ (m : ℝ) * a ^ 2 * (1 - a) →
      ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) <
      1 - a ∧ 1 - a < (1 - (m : ℝ) * a / ((m : ℝ) + 1))) := by
  simp only [literal_budget]
  refine ⟨PaperHistoricalBounds.budget_lt_forty hm ha ha1 ha2 hx0 hx1 hr, ?_⟩
  intro hbulk
  exact ⟨PaperHistoricalBounds.budget_lt_one_sub_of_bulk40 hm ha ha1 ha2 hx0 hx1 hr hbulk,
    h_lt_B ha⟩

/-- UN05: the original degree-seven bulk theorem, including T < h < B. -/
theorem un05_bulk116 {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x)
    (hbulk : 116 ≤ (m : ℝ) * a ^ 2 * (1 - a)) :
    ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) <
      1 - a ∧ 1 - a < (1 - (m : ℝ) * a / ((m : ℝ) + 1)) := by
  simp only [literal_budget]
  exact ⟨PaperHistoricalBounds.budget_lt_one_sub_of_bulk116 hm ha ha1 hx0 hx1 hr hbulk,
    h_lt_B ha⟩

/-- UN08: explicit all-a cutoff 512; no radius or ray restriction. -/
theorem un08_all_a_512 {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) :
    ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) <
      (1 - (m : ℝ) * a / ((m : ℝ) + 1)) := by
  simp only [literal_budget]
  exact PaperConsequences.old_all_a_cutoff (M := 512) (by norm_num)
    hm ha ha1 hx0 hx1 hr

/-- UN09: explicit all-a cutoff 10000; no radius or ray restriction. -/
theorem un09_all_a_10000 {m : ℕ} {a x : ℝ} (hm : 10000 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) :
    ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) <
      (1 - (m : ℝ) * a / ((m : ℝ) + 1)) := by
  simp only [literal_budget]
  exact PaperConsequences.old_all_a_cutoff (M := 10000) (by norm_num)
    hm ha ha1 hx0 hx1 hr

/-- UN10: explicit all-a cutoff 100000; no radius or ray restriction. -/
theorem un10_all_a_100000 {m : ℕ} {a x : ℝ} (hm : 100000 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) :
    ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) <
      (1 - (m : ℝ) * a / ((m : ℝ) + 1)) := by
  simp only [literal_budget]
  exact PaperConsequences.old_all_a_cutoff (M := 100000) (by norm_num)
    hm ha ha1 hx0 hx1 hr

/-- UN11: explicit all-a cutoff 1000000; no radius or ray restriction. -/
theorem un11_all_a_1000000 {m : ℕ} {a x : ℝ} (hm : 1000000 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) :
    ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) <
      (1 - (m : ℝ) * a / ((m : ℝ) + 1)) := by
  simp only [literal_budget]
  exact PaperConsequences.old_all_a_cutoff (M := 1000000) (by norm_num)
    hm ha ha1 hx0 hx1 hr

/-- RA03: all four round5 upper bands, with the actual integral on the left. -/
theorem ra03_scaled_upper {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) :
    (lambda m a ∈ Set.Icc (1 / 5) (1) →
      (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 18 / (m : ℝ)) ∧
    (lambda m a ∈ Set.Icc (1) (10) →
      (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 33 / (m : ℝ)) ∧
    (lambda m a ∈ Set.Icc (10) (25) →
      (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 51 / (m : ℝ) + 1 / 4) ∧
    (lambda m a ∈ Set.Icc (25) (49) →
      (m : ℝ) * x ^ 2 * ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) +
      (m : ℝ) * a ^ 2 * ∫ t in (0 : ℝ)..1,
        t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) < 1 + 62 / (m : ℝ) + 2) := by
  simp only [literal_budget]
  have hm' : (256 : ℝ) ≤ m := by exact_mod_cast hm
  have half (hl : lambda m a ≤ 49) : x < 2 * a := by
    exact (div_lt_one (by positivity : 0 < 2 * a)).mp
      (PaperRayGeometry.halfpoint_mem hm ha ha1 hx0 hx1 hr hl).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hl
    have hx := PaperRayGeometry.geometry_one hm ha ha1 hx0 hx1 hr hl.2
    have hb := (PaperRayGeometry.geometry_ten hm ha ha1 hx0 hx1 hr
      (by linarith [hl.2])).1
    exact PaperTail.budget_region_one hm' ha ha1 hx hx1 (half (by linarith [hl.2]))
      (by rw [PaperUniform.beta_one]; exact hb.le)
  · intro hl
    obtain ⟨hb, hx⟩ := PaperRayGeometry.geometry_ten hm ha ha1 hx0 hx1 hr hl.2
    exact PaperTail.budget_region_two hm' ha ha1 hx hx1 (half (by linarith [hl.2]))
      (by rw [PaperUniform.beta_one]; exact hb.le)
  · intro hl
    obtain ⟨hb, hx⟩ := PaperRayGeometry.geometry_twentyfive hm ha ha1 hx0 hx1 hr hl.2
    exact PaperTail.budget_region_three hm' ha ha1 hx hx1 (half (by linarith [hl.2]))
      (by rw [PaperUniform.beta_one]; exact hb.le)
  · intro hl
    obtain ⟨hb, hx⟩ := PaperRayGeometry.geometry_fortynine hm ha ha1 hx0 hx1 hr hl.2
    exact PaperTail.budget_region_four hm' ha ha1 hx hx1 (half hl.2)
      (by rw [PaperUniform.beta_one]; exact hb.le)

/-- The original second lower expression needs 31/25, not merely 6/5. -/
private lemma product_five_original {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (hl0 : 1 ≤ lambda m a) (hl1 : lambda m a ≤ 5) :
    31 / 25 ≤ (lambda m a + 1) * x ^ 2 := by
  have hlpos : 0 ≤ lambda m a := by linarith
  have hb := PaperRayGeometry.b_le_lambda (by omega) ha ha1 hx0 hx1 hr
  have ha' := PaperRayGeometry.a_lower hm ha1 hl1
  norm_num at ha'
  by_cases hl2 : lambda m a ≤ 2
  · have hb2 := hb.trans (rational_mono hlpos hl2)
    norm_num at hb2
    have hx := PaperRayGeometry.x_lower_constant (by norm_num : (0 : ℝ) < 251 / 256) ha'
      (by norm_num : (0 : ℝ) ≤ 2 / 5) hb2
    have hxs : 79 / 100 ≤ x := by norm_num at hx; linarith
    have hx2 : (79 / 100 : ℝ) ^ 2 ≤ x ^ 2 := by nlinarith
    have hmul := mul_nonneg (sq_nonneg x) (show 0 ≤ lambda m a - 1 by linarith)
    nlinarith
  · have hb5 := hb.trans (rational_mono hlpos hl1)
    norm_num at hb5
    have hx := PaperRayGeometry.x_lower_constant (by norm_num : (0 : ℝ) < 251 / 256) ha'
      (by norm_num : (0 : ℝ) ≤ 5 / 8) hb5
    have hxs : 17 / 25 ≤ x := by norm_num at hx; linarith
    have hx2 : (17 / 25 : ℝ) ^ 2 ≤ x ^ 2 := by nlinarith
    have hmul := mul_nonneg (sq_nonneg x) (show 0 ≤ lambda m a - 2 by linarith)
    nlinarith

/-- RA04: all five original rational lower bounds and their strict comparisons.
The first band uses RateDetails on the full [1/5,1], not the shortened [2/5,1]. -/
theorem ra04_scaled_lower {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) :
    (lambda m a ∈ Set.Icc (1 / 5) (1) →
      1 + 18 / (m : ℝ) < (m : ℝ) / ((m : ℝ) + 1) * (1 + (24 / 49 - 8 / (m : ℝ)) / 5) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (1 + (24 / 49 - 8 / (m : ℝ)) / 5) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) ∧
    (lambda m a ∈ Set.Icc (1) (5) →
      1 + 33 / (m : ℝ) < (m : ℝ) / ((m : ℝ) + 1) * (1 + 6 / 25 - 24 / (m : ℝ)) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (1 + 6 / 25 - 24 / (m : ℝ)) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) ∧
    (lambda m a ∈ Set.Icc (5) (10) →
      1 + 33 / (m : ℝ) < (m : ℝ) / ((m : ℝ) + 1) * (6 * (7 / 12) ^ 2) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (6 * (7 / 12) ^ 2) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) ∧
    (lambda m a ∈ Set.Icc (10) (25) →
      1 + 51 / (m : ℝ) + 1 / 4 < (m : ℝ) / ((m : ℝ) + 1) * (11 * (231 / 512) ^ 2) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (11 * (231 / 512) ^ 2) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) ∧
    (lambda m a ∈ Set.Icc (25) (49) →
      1 + 62 / (m : ℝ) + 2 < (m : ℝ) / ((m : ℝ) + 1) * (26 * (207 / 512) ^ 2) ∧
      (m : ℝ) / ((m : ℝ) + 1) * (26 * (207 / 512) ^ 2) ≤
      (m : ℝ) * x ^ 2 * (1 - (m : ℝ) * a / ((m : ℝ) + 1))) := by
  have hm' : (256 : ℝ) ≤ m := by exact_mod_cast hm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hl
    exact ⟨PaperRay.ray_one hm',
      PaperRateDetails.scaled_budget_paper_lower_one hm ha ha1 hx0 hx1 hr hl.1 hl.2⟩
  · intro hl
    refine ⟨PaperRay.ray_two hm', PaperRayGeometry.scaled_budget_lower ?_⟩
    have hp := product_five_original hm ha ha1 hx0 hx1 hr hl.1 hl.2
    have hd : 0 ≤ 24 / (m : ℝ) := by positivity
    linarith
  · intro hl
    refine ⟨PaperRay.ray_three hm', ?_⟩
    have hx := (PaperRayGeometry.geometry_ten hm ha ha1 hx0 hx1 hr hl.2).2
    simpa only [PaperRayGeometry.B, show (5 : ℝ) + 1 = 6 by norm_num] using
      PaperRayGeometry.scaled_budget_lower_of_x hl.1 (by norm_num)
        (by norm_num : (0 : ℝ) ≤ 7 / 12) hx.le
  · intro hl
    refine ⟨PaperRay.ray_four hm', ?_⟩
    have hx := (PaperRayGeometry.geometry_twentyfive hm ha ha1 hx0 hx1 hr hl.2).2
    simpa only [PaperRayGeometry.B, show (10 : ℝ) + 1 = 11 by norm_num] using
      PaperRayGeometry.scaled_budget_lower_of_x hl.1 (by norm_num)
        (by norm_num : (0 : ℝ) ≤ 231 / 512) hx.le
  · intro hl
    refine ⟨PaperRay.ray_five hm', ?_⟩
    have hx := (PaperRayGeometry.geometry_fortynine hm ha ha1 hx0 hx1 hr hl.2).2
    simpa only [PaperRayGeometry.B, show (25 : ℝ) + 1 = 26 by norm_num] using
      PaperRayGeometry.scaled_budget_lower_of_x hl.1 (by norm_num)
        (by norm_num : (0 : ℝ) ≤ 207 / 512) hx.le

end Sendov.PaperRegionCorollaries
