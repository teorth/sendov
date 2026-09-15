import Sendov.Analytic.PaperHistoricalBounds
import Sendov.Analytic.PaperRayGeometry

/-!
# Preserved paper rates (PO06, HI04, RA04)

These statements retain quantitative outputs, not merely `T < B`.
The endpoint keeps its delta-dependent exponent. The two historical small-radius
ratios follow from the stronger accepted `T < 3/5` and bulk-116 bounds. The
missing low ray uses the existing rational polar bound and continuous polynomial
comparison; neither a degree table nor an assumed geometric estimate is used.
-/
namespace Sendov.PaperRateDetails

open PaperPolar

/-- PO06: the original delta-sensitive rate, not just `4/(m+2)`.
In fact the logarithmic proof works for every positive `N*delta`. -/
theorem endpoint_delta_rate {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x)
    (hlarge : 2 ≤ (((m : ℝ) + 2) / 2) * (1 - a ^ 2)) :
    b a x ^ ((m : ℝ) / 2) ≤
      ((((m : ℝ) + 2) / 2) * (1 - a ^ 2)) ^
        (-(m : ℝ) / (((m : ℝ) + 2) * (1 - a ^ 2))) := by
  have hD : 0 < (((m : ℝ) + 2) / 2) * (1 - a ^ 2) := by linarith
  have hb := b_pos ha.le ha1 hx1
  have hlog := PaperGlobalPolar.log_mul_delta_le hm ha ha1 hx0 hx1 hr
  have hlogb : Real.log (b a x) ≤ -c a x := by
    have h := Real.log_le_sub_one_of_pos hb
    unfold c
    linarith
  have hscale := mul_le_mul_of_nonneg_left hlogb hD.le
  have hcombined : Real.log (b a x) ≤
      -Real.log ((((m : ℝ) + 2) / 2) * (1 - a ^ 2)) /
        ((((m : ℝ) + 2) / 2) * (1 - a ^ 2)) := by
    apply (le_div_iff₀ hD).mpr
    nlinarith only [hscale, hlog]
  have hmul := mul_le_mul_of_nonneg_left hcombined
    (show 0 ≤ (m : ℝ) / 2 by positivity)
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hb _)
    (Real.rpow_pos_of_pos hD _)).mp
  rw [Real.log_rpow hb, Real.log_rpow hD]
  calc
    _ ≤ (m : ℝ) / 2 *
        (-Real.log ((((m : ℝ) + 2) / 2) * (1 - a ^ 2)) /
          ((((m : ℝ) + 2) / 2) * (1 - a ^ 2))) := hmul
    _ = _ := by field_simp

/-- The small-radius branch of both historical ratios uses a stronger modern bound. -/
lemma small_radius_ratio {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (ha5 : a ≤ 1 / 5)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hr : RawPolar m a x) :
    PaperTaylor.budget m a x / (1 - a) < 3 / 4 := by
  apply (div_lt_iff₀ (show 0 < 1 - a by linarith)).mpr
  have ht := PaperHistoricalBounds.budget_lt_three_fifths hm ha ha1 hx0 hx1 hr
  linarith

/-- HI04, original uniform small-a ratio at degree 100000. -/
theorem small_a_ratio_100000 {m : ℕ} {a x : ℝ} (hm : 100000 ≤ m)
    (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) :
    PaperTaylor.budget m a x / (1 - a) < 83567 / 100000 := by
  have ha1 : a < 1 := by linarith
  by_cases ha5 : a ≤ 1 / 5
  · exact (small_radius_ratio (by omega) ha ha1 ha5 hx0 hx1 hr).trans (by norm_num)
  have hm' : (100000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by linarith
  have haSq : 1 / 25 ≤ a ^ 2 := by nlinarith
  have hma : (4000 : ℝ) ≤ (m : ℝ) * a ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hm') (sq_nonneg a), haSq]
  have hbound : 116 / ((m : ℝ) * a ^ 2) ≤ (83567 / 100000 : ℝ) * (1 - a) := by
    apply (div_le_iff₀ (by positivity : 0 < (m : ℝ) * a ^ 2)).mpr
    have hprod := mul_nonneg (show 0 ≤ 1 - a - 1 / 2 by linarith)
      (show 0 ≤ (m : ℝ) * a ^ 2 by positivity)
    nlinarith only [hprod, hma]
  apply (div_lt_iff₀ (show 0 < 1 - a by linarith)).mpr
  exact (PaperHistoricalBounds.budget_lt_bulk116 (by omega) ha ha1 hx0 hx1 hr).trans_le hbound

/-- HI04, round3's small-a ratio, retaining its bulk-complement hypothesis. -/
theorem small_a_ratio_10000 {m : ℕ} {a x : ℝ} (hm : 10000 ≤ m)
    (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (hbulk : (m : ℝ) * a ^ 2 * (1 - a) < 116) :
    PaperTaylor.budget m a x / (1 - a) < 106 / 125 := by
  have hm' : (10000 : ℝ) ≤ m := by exact_mod_cast hm
  have ha1 : a < 1 := by linarith
  have hma : (m : ℝ) * a ^ 2 < 232 := by
    have h := mul_nonneg (show 0 ≤ 1 - a - 1 / 2 by linarith)
      (show 0 ≤ (m : ℝ) * a ^ 2 by positivity)
    nlinarith only [h, hbulk]
  have haSq : a ^ 2 < 1 / 25 := by
    have h := mul_nonneg (sub_nonneg.mpr hm') (sq_nonneg a)
    nlinarith only [h, hma]
  have ha5 : a ≤ 1 / 5 := by nlinarith
  exact (small_radius_ratio (by omega) ha ha1 ha5 hx0 hx1 hr).trans (by norm_num)

/-- The missing continuous strip of RA04 has the same stronger product bound
already used above lambda=2/5. No numerical sampling is involved. -/
lemma product_lower_low_ray {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (hl0 : 1 / 5 ≤ lambda m a) (hl1 : lambda m a ≤ 2 / 5) :
    11 / 10 ≤ (lambda m a + 1) * x ^ 2 := by
  have hlpos : 0 ≤ lambda m a := by linarith
  have hb := PaperRayGeometry.b_le_lambda (by omega) ha ha1 hx0 hx1 hr
  have hrat : lambda m a / (3 + lambda m a) ≤ lambda m a / 3 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith [sq_nonneg (lambda m a)]
  have ha' := PaperRayGeometry.a_lower hm ha1 (show lambda m a ≤ 1 by linarith)
  norm_num at ha'
  have hx := PaperRayGeometry.x_lower_constant (by norm_num : (0 : ℝ) < 255 / 256)
    ha' (show 0 ≤ lambda m a / 3 by positivity) (hb.trans hrat)
  have hxlin : 1 - 128 / 765 * lambda m a ≤ x := by
    convert hx using 1
    ring
  have hx2 : 1 - 256 / 765 * lambda m a ≤ x ^ 2 := by
    nlinarith [sq_nonneg (x - 1)]
  have hmul := mul_nonneg (show 0 ≤ lambda m a + 1 by positivity)
    (sub_nonneg.mpr hx2)
  have hquad := mul_nonneg hlpos (sub_nonneg.mpr hl1)
  nlinarith

/-- RA04's exact round5 lower formula, on the full original first ray. -/
theorem scaled_budget_paper_lower_one {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (hl0 : 1 / 5 ≤ lambda m a) (hl1 : lambda m a ≤ 1) :
    (m : ℝ) / ((m : ℝ) + 1) * (1 + (24 / 49 - 8 / (m : ℝ)) / 5) ≤
      (m : ℝ) * x ^ 2 * PaperRayGeometry.B m a := by
  have hp : 11 / 10 ≤ (lambda m a + 1) * x ^ 2 := by
    by_cases hl : 2 / 5 ≤ lambda m a
    · exact PaperRayGeometry.product_lower_one hm ha ha1 hx0 hx1 hr hl hl1
    · exact product_lower_low_ray hm ha ha1 hx0 hx1 hr hl0 (by linarith)
  apply PaperRayGeometry.scaled_budget_lower
  have hdiv : 0 ≤ 8 / (m : ℝ) := by positivity
  linarith

/-- RA04 on the entire original first ray, including the formerly missing
`[1/5,2/5)` strip: a lower bound on the actual available budget from raw polar. -/
theorem scaled_budget_lower_one {m : ℕ} {a x : ℝ} (hm : 256 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (hl0 : 1 / 5 ≤ lambda m a) (hl1 : lambda m a ≤ 1) :
    1 + 18 / (m : ℝ) < (m : ℝ) * x ^ 2 * PaperRayGeometry.B m a :=
  (PaperRay.ray_one (by exact_mod_cast hm)).trans_le
    (scaled_budget_paper_lower_one hm ha ha1 hx0 hx1 hr hl0 hl1)

end Sendov.PaperRateDetails
