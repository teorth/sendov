import Sendov.Common.DistillationCorrelatedPeak

/-! # Rational closure of the same-alpha exponential peaks -/

namespace Sendov

noncomputable def distillTaylor6 (x : ℝ) : ℝ :=
  1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720

lemma distillTaylor6_pos {x : ℝ} (hx : 0 ≤ x) : 0 < distillTaylor6 x := by
  unfold distillTaylor6
  positivity

lemma exp_neg_le_taylor6 {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 / distillTaylor6 x := by
  have h := Real.sum_le_exp_of_nonneg hx 7
  norm_num [Finset.sum_range_succ] at h
  have hp := distillTaylor6_pos hx
  rw [Real.exp_neg, inv_eq_one_div]
  apply div_le_div_of_nonneg_left (by norm_num) hp
  simpa only [distillTaylor6] using h

private lemma exp_neg_two_bound : Real.exp (-2) ≤ 677 / 5000 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 13
  norm_num [Finset.sum_range_succ] at h
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_iff₀ (Real.exp_pos 2)).mpr
  linarith

private lemma exp_neg_three_bound : Real.exp (-3) ≤ 249 / 5000 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 17
  norm_num [Finset.sum_range_succ] at h
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_iff₀ (Real.exp_pos 3)).mpr
  linarith

noncomputable def distillPeakShift1 (α : ℝ) : ℝ :=
  distillPeakRate1 α * (2 * α - 3) - distillPeakBoost1 α

lemma distillPeakShift1_pos {α : ℝ} (hα : 2 ≤ α) : 0 < distillPeakShift1 α := by
  let P := 5 * α ^ 3 + 36 * α ^ 2 + 78 * α + 48
  let W := 95 * α ^ 3 + 774 * α ^ 2 + 2052 * α + 1782
  have hα0 : 0 < α := by linarith
  have hP : 0 < P := by dsimp [P]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  have hB : distillPeakNode α = 9 * P / (50 * (α + 3) ^ 3) := by
    unfold distillPeakNode cubicPolarEnvelope
    dsimp [P]
    field_simp
    ring
  have hid : distillPeakShift1 α * (9 * P * W) =
      70 * (α - 2) ^ 7 + 8749 * (α - 2) ^ 6 + 184410 * (α - 2) ^ 5 +
        1673506 * (α - 2) ^ 4 + 7765678 * (α - 2) ^ 3 +
        18513756 * (α - 2) ^ 2 + 19556380 * (α - 2) + 4759936 := by
    unfold distillPeakShift1 distillPeakRate1 distillPeakBoost1
    rw [hB]
    dsimp [P, W]
    field_simp
    ring
  have hpos : 0 < 70 * (α - 2) ^ 7 + 8749 * (α - 2) ^ 6 +
      184410 * (α - 2) ^ 5 + 1673506 * (α - 2) ^ 4 +
      7765678 * (α - 2) ^ 3 + 18513756 * (α - 2) ^ 2 +
      19556380 * (α - 2) + 4759936 := by
    have : 0 ≤ α - 2 := by linarith
    positivity
  rw [← hid] at hpos
  exact pos_of_mul_pos_left hpos (by positivity)

noncomputable def distillRationalExpPeak (α c x : ℝ) : ℝ :=
  (27 * (249 / 5000) / c ^ 3 + 8 * α * (677 / 5000) / c ^ 2) /
    distillTaylor6 x

lemma exp_peak_le_rational {α c x : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hx : 0 ≤ x) :
    Real.exp (-x) *
      (27 * Real.exp (-3) / c ^ 3 + 8 * α * Real.exp (-2) / c ^ 2) ≤
      distillRationalExpPeak α c x := by
  have h2 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left exp_neg_two_bound (by positivity : 0 ≤ 8 * α))
    (sq_nonneg c)
  have h3 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left exp_neg_three_bound (by norm_num : (0 : ℝ) ≤ 27))
    (pow_nonneg hc.le 3)
  have h := mul_le_mul (exp_neg_le_taylor6 hx) (add_le_add h3 h2)
    (by positivity) (by have := distillTaylor6_pos hx; positivity)
  unfold distillRationalExpPeak
  exact h.trans_eq (by ring)

private lemma expPeak_antitone_rate {α c d : ℝ} (hα : 3 / 2 ≤ α)
    (hc : 0 < c) (hcd : c ≤ d) : distillExpPeak α d ≤ distillExpPeak α c := by
  have hd : 0 < d := hc.trans_le hcd
  have he : Real.exp (-d * (2 * α - 3)) ≤ Real.exp (-c * (2 * α - 3)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h2 := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ 8 * α * Real.exp (-2)) (pow_pos hc 2)
    (pow_le_pow_left₀ hc.le hcd 2)
  have h3 := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ 27 * Real.exp (-3)) (pow_pos hc 3)
    (pow_le_pow_left₀ hc.le hcd 3)
  exact mul_le_mul he (add_le_add h3 h2) (by positivity) (Real.exp_nonneg _)

noncomputable def distillRationalPeak (α : ℝ) : ℝ :=
  distillElementary (max 5 (2 * α)) α + distillPeak0 α +
    (259 / 12500) * distillRatio α *
      distillRationalExpPeak α (distillPeakRate1 α) (distillPeakShift1 α) +
    (421 / 12500) * distillRatio α *
      distillRationalExpPeak α (distillPeakRate2 α) (distillPeakRate2 α * (2 * α - 3))

/-- Only alpha remains; the real degree ray has already been bounded analytically. -/
theorem distillScalar_le_rationalPeak {m α : ℝ} (hm : 5 ≤ m) (hα : 2 ≤ α)
    (hαm : 2 * α ≤ m) :
    scalarObstruction m α (cubicPolarEnvelope α) ≤ distillRationalPeak α := by
  have hα0 : 0 < α := by linarith
  have h := distillScalar_le_correlated_peak hm (by linarith : 1 ≤ α) hαm
  have h1 := mul_le_mul_of_nonneg_left
    (exp_peak_le_rational hα0.le (distillPeakRate1_pos (α := α) (by linarith))
      (distillPeakShift1_pos hα).le)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 259 / 12500) (distillRatio_nonneg hα0.le))
  have hid1 : distillPeak1 α = (259 / 12500) * distillRatio α *
      (Real.exp (-distillPeakShift1 α) *
        (27 * Real.exp (-3) / distillPeakRate1 α ^ 3 +
          8 * α * Real.exp (-2) / distillPeakRate1 α ^ 2)) := by
    have hexp : Real.exp (-distillPeakShift1 α) =
        Real.exp (distillPeakBoost1 α) * Real.exp (-distillPeakRate1 α * (2 * α - 3)) := by
      rw [← Real.exp_add]
      congr 1
      unfold distillPeakShift1
      ring
    rw [hexp]
    unfold distillPeak1 distillExpPeak
    ring
  rw [← hid1] at h1
  have he := cubicPolarEnvelope_pos hα0
  have hlog := log_le_pade he (cubicPolarEnvelope_lt_one hα0.le).le
  have hrate : distillPeakRate2 α ≤ -Real.log (cubicPolarEnvelope α) / 2 := by
    unfold distillPeakRate2
    linarith
  have h2a := mul_le_mul_of_nonneg_left
    (expPeak_antitone_rate (by linarith : 3 / 2 ≤ α)
      (distillPeakRate2_pos hα0.le) hrate)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 421 / 12500) (distillRatio_nonneg hα0.le))
  have hx2 : 0 ≤ distillPeakRate2 α * (2 * α - 3) :=
    mul_nonneg (distillPeakRate2_pos hα0.le).le (by linarith)
  have h2b := mul_le_mul_of_nonneg_left
    (exp_peak_le_rational hα0.le (distillPeakRate2_pos hα0.le) hx2)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 421 / 12500) (distillRatio_nonneg hα0.le))
  have hid2 : Real.exp (-(distillPeakRate2 α * (2 * α - 3))) =
      Real.exp (-distillPeakRate2 α * (2 * α - 3)) := by congr 1; ring
  rw [hid2] at h2b
  unfold distillExpPeak at h2a
  have h2 : distillPeak2 α ≤ (421 / 12500) * distillRatio α *
      distillRationalExpPeak α (distillPeakRate2 α) (distillPeakRate2 α * (2 * α - 3)) :=
    h2a.trans h2b
  unfold distillCorrelatedPeak at h
  unfold distillRationalPeak
  linarith only [h, h1, h2]

end Sendov
