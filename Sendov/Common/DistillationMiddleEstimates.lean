import Sendov.Common.DistillationPeakRational

/-!
# Mixed-alpha estimates on entire real-degree rays

The rational T0 bound retains `(m+3)(m+5)`. The exponential estimates use
the original node at the upper alpha endpoint and the prefactor at the lower
endpoint, but never use a finite degree row or a degree-tail base value.
-/

namespace Sendov

lemma distillT0_le_mixed_rational {m α l r R d : ℝ} (hm : 5 ≤ m)
    (hl : 0 ≤ l) (hlα : l ≤ α) (hαr : α ≤ r) (hrm : 2 * r ≤ m)
    (hR : distillRatio l ≤ R) (hd : d ≤ distillPeakD r)
    (hden : 0 < d * m - 12 * r / 25) :
    distillT0 m α ≤
      24 * (3 / 5) ^ 4 * R * m ^ 3 * (m - 2 * l) ^ 2 /
        ((m + 3) * (m + 5) * (d * m - 12 * r / 25) ^ 4) := by
  have hm0 : 0 < m := by linarith
  have hm1 : m - 1 ≠ 0 := by linarith
  have hR0 : 0 ≤ R := (distillRatio_nonneg hl).trans hR
  have hdr : 0 < distillPeakD r * m - 12 * r / 25 := by nlinarith
  have hn : 1 - distillNode m r = (distillPeakD r * m - 12 * r / 25) / m := by
    unfold distillNode distillPeakD
    field_simp
    ring
  have h := distillT0_mixed hm hl hlα hαr (by linarith)
  have hid :
      distillKappa m l * (96 * (3 / 5) ^ 4 /
        ((m - 1) * (m + 1) * (m + 3) * (m + 5) * (1 - distillNode m r) ^ 4)) =
      24 * (3 / 5) ^ 4 * distillRatio l * m ^ 3 * (m - 2 * l) ^ 2 /
        ((m + 3) * (m + 5) * (distillPeakD r * m - 12 * r / 25) ^ 4) := by
    rw [hn]
    unfold distillKappa
    field_simp
    ring
  rw [hid] at h
  refine h.trans ?_
  apply div_le_div₀ (by positivity)
    (by gcongr)
    (by positivity)
  gcongr

lemma distillT1_le_mixed_peak {m α l r : ℝ} (hm : 5 ≤ m)
    (hl : 0 ≤ l) (hr : 1 ≤ r) (hlα : l ≤ α) (hαr : α ≤ r)
    (hrm : 2 * r ≤ m) :
    distillT1 m α ≤ (259 / 12500) * distillRatio l *
      Real.exp (distillPeakBoost1 r) * distillExpPeak l (distillPeakRate1 r) := by
  have hm0 : 0 < m := by linarith
  have h := distillT1_mixed hm hl hlα hαr (by linarith)
  have hK := distillKappa_le_shifted_cubic hm0 hl
  have hp := distillNode_rpow_le_exp hm hr
  have hmul := mul_le_mul hK hp
    (Real.rpow_nonneg (distillNode_pos hm0 (by linarith : 0 ≤ r)).le _)
    (by have := distillRatio_nonneg hl; positivity)
  have hs := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 259 / 3125)
  have hpeak := distill_degree_exp_le_peak hl (by linarith : 2 * l ≤ m)
    (distillPeakRate1_pos hr)
  have hscaled := mul_le_mul_of_nonneg_left hpeak
    (by have := distillRatio_nonneg hl
        positivity : 0 ≤ (259 / 12500) * distillRatio l * Real.exp (distillPeakBoost1 r))
  rw [Real.exp_add] at hs
  nlinarith only [h, hs, hscaled]

lemma distillT2_le_mixed_peak {m α l r : ℝ} (hm : 5 ≤ m)
    (hl : 0 ≤ l) (hr : 0 < r) (hlα : l ≤ α) (hαr : α ≤ r)
    (hrm : 2 * r ≤ m) :
    distillT2 m α ≤
      (421 / 12500) * distillRatio l * distillExpPeak l (distillPeakRate2 r) := by
  have hm0 : 0 < m := by linarith
  have he := cubicPolarEnvelope_pos hr
  have hlog := log_le_pade he (cubicPolarEnvelope_lt_one hr.le).le
  have hp : cubicPolarEnvelope r ^ ((m - 3) / 2) ≤
      Real.exp (-distillPeakRate2 r * (m - 3)) := by
    rw [Real.rpow_def_of_pos he]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hlog (by linarith : 0 ≤ (m - 3) / 2)
    unfold distillPeakRate2
    nlinarith only [h]
  have h := distillT2_mixed hm hl hlα hαr (by linarith)
  have hK := distillKappa_le_shifted_cubic hm0 hl
  have hmul := mul_le_mul hK hp (Real.rpow_nonneg he.le _)
    (by have := distillRatio_nonneg hl; positivity)
  have hs := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 421 / 3125)
  have hpeak := distill_degree_exp_le_peak hl (by linarith : 2 * l ≤ m)
    (distillPeakRate2_pos hr.le)
  have hscaled := mul_le_mul_of_nonneg_left hpeak
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 421 / 12500) (distillRatio_nonneg hl))
  nlinarith only [h, hs, hscaled]

noncomputable def distillLinearExpPeak (l c x : ℝ) : ℝ :=
  (27 * (249 / 5000) / c ^ 3 + 8 * l * (677 / 5000) / c ^ 2) / (1 + x)

/-- Unlike the Taylor-six bound, this also covers the small negative shifts. -/
lemma distill_exp_peak_le_linear {l c x : ℝ} (hl : 0 ≤ l) (hc : 0 < c)
    (hx : 0 < 1 + x) :
    Real.exp (-x) * (27 * Real.exp (-3) / c ^ 3 + 8 * l * Real.exp (-2) / c ^ 2) ≤
      distillLinearExpPeak l c x := by
  have hexp : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply div_le_div_of_nonneg_left (by norm_num) hx
    linarith only [Real.add_one_le_exp x]
  have h := exp_peak_le_rational hl hc (x := 0) (by norm_num)
  norm_num [distillRationalExpPeak, distillTaylor6] at h
  have hmul := mul_le_mul hexp h (by positivity) (by positivity)
  exact hmul.trans_eq (by unfold distillLinearExpPeak; ring)

lemma distill_mixed_peak1_le_linear {l r : ℝ} (hl : 0 ≤ l) (hr : 1 ≤ r)
    (hx : 0 < 1 + (distillPeakRate1 r * (2 * l - 3) - distillPeakBoost1 r)) :
    (259 / 12500) * distillRatio l * Real.exp (distillPeakBoost1 r) *
        distillExpPeak l (distillPeakRate1 r) ≤
      (259 / 12500) * distillRatio l *
        distillLinearExpPeak l (distillPeakRate1 r)
          (distillPeakRate1 r * (2 * l - 3) - distillPeakBoost1 r) := by
  have h := mul_le_mul_of_nonneg_left
    (distill_exp_peak_le_linear hl (distillPeakRate1_pos hr) hx)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 259 / 12500) (distillRatio_nonneg hl))
  have hid : Real.exp (-(distillPeakRate1 r * (2 * l - 3) - distillPeakBoost1 r)) =
      Real.exp (distillPeakBoost1 r) * Real.exp (-distillPeakRate1 r * (2 * l - 3)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hid] at h
  unfold distillExpPeak
  nlinarith only [h]

lemma distill_mixed_peak2_le_linear {l r : ℝ} (hl : 0 ≤ l) (hr : 0 ≤ r)
    (hx : 0 < 1 + distillPeakRate2 r * (2 * l - 3)) :
    (421 / 12500) * distillRatio l * distillExpPeak l (distillPeakRate2 r) ≤
      (421 / 12500) * distillRatio l *
        distillLinearExpPeak l (distillPeakRate2 r) (distillPeakRate2 r * (2 * l - 3)) := by
  have h := mul_le_mul_of_nonneg_left
    (distill_exp_peak_le_linear hl (distillPeakRate2_pos hr) hx)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 421 / 12500) (distillRatio_nonneg hl))
  have hid : -(distillPeakRate2 r * (2 * l - 3)) =
      -distillPeakRate2 r * (2 * l - 3) := by ring
  rw [hid] at h
  exact h

end Sendov
