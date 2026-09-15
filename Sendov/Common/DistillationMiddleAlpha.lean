import Sendov.Common.DistillationMiddleEstimates

/-!
# The closed middle-alpha strip, without finite degree bases

The only split is in alpha, at `17/10`. On each side a positive sextic in
`m-5` bounds T0 on the entire real-degree ray, retaining its actual denominator.
T1 and T2 use mixed-alpha exponential peaks, also on the entire ray.
-/

namespace Sendov

lemma distillElementary_le_middle {m α : ℝ} (hm : 5 ≤ m) (hα : 7 / 5 ≤ α) :
    distillElementary m α ≤ 221 / 660 := by
  have hα0 : 0 < α := by linarith
  have hr : distillRatio α ≤ 5 / 22 := by
    have h := distillRatio_antitone (by norm_num : (0 : ℝ) ≤ 7 / 5) hα
    have hcap : distillRatio (7 / 5) ≤ 5 / 22 := by norm_num [distillRatio]
    exact h.trans hcap
  have he := cubicPolarEnvelope_lt_one hα0.le
  have hlinear := (le_div_iff₀ (by linarith : 0 < α + 3)).mp
    (cubicPolarEnvelope_le_linear hα0.le)
  have hid : distillRatio α * α = cubicPolarEnvelope α :=
    (eq_div_iff hα0.ne').mp (distillRatio_eq hα0)
  have hfirst : distillRatio α / (2 * (1 - cubicPolarEnvelope α)) ≤ 1 / 6 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (1 - cubicPolarEnvelope α))).mpr
    nlinarith
  have h := distillElementary_antitone_degree (by norm_num : (0 : ℝ) < 5) hm hα0.le
  unfold distillElementary at h ⊢
  nlinarith only [h, hfirst, hr]

private lemma middle_T0_lower_polynomial {m : ℝ} (hm : 5 ≤ m) :
    24 * (3 / 5 : ℝ) ^ 4 * (5 / 22) * m ^ 3 * (m - 2 * (7 / 5)) ^ 2 <
      (13 / 50) * ((m + 3) * (m + 5) * ((31 / 50) * m - 12 * (17 / 10) / 25) ^ 4) := by
  have hx : 0 ≤ m - 5 := by linarith
  have hid :
      2148437500000 *
        ((13 / 50) * ((m + 3) * (m + 5) * ((31 / 50) * m - 12 * (17 / 10) / 25) ^ 4) -
          24 * (3 / 5) ^ 4 * (5 / 22) * m ^ 3 * (m - 2 * (7 / 5)) ^ 2) =
      82539689375 * (m - 5) ^ 6 + 1183226670250 * (m - 5) ^ 5 +
        5752975708450 * (m - 5) ^ 4 + 13287198225360 * (m - 5) ^ 3 +
        48679218659063 * (m - 5) ^ 2 + 207466884835694 * (m - 5) +
        297259523310640 := by ring
  apply sub_pos.mp
  apply pos_of_mul_pos_right (a := (2148437500000 : ℝ)) _ (by norm_num)
  rw [hid]
  positivity

private lemma middle_T0_upper_polynomial {m : ℝ} (hm : 5 ≤ m) :
    24 * (3 / 5 : ℝ) ^ 4 * (10 / 47) * m ^ 3 * (m - 2 * (17 / 10)) ^ 2 <
      (13 / 50) * ((m + 3) * (m + 5) * ((3 / 5) * m - 12 * 2 / 25) ^ 4) := by
  have hx : 0 ≤ m - 5 := by linarith
  have hid :
      917968750 *
        ((13 / 50) * ((m + 3) * (m + 5) * ((3 / 5) * m - 12 * 2 / 25) ^ 4) -
          24 * (3 / 5) ^ 4 * (10 / 47) * m ^ 3 * (m - 2 * (17 / 10)) ^ 2) =
      30931875 * (m - 5) ^ 6 + 369947250 * (m - 5) ^ 5 +
        1135607850 * (m - 5) ^ 4 + 856992960 * (m - 5) ^ 3 +
        18236567691 * (m - 5) ^ 2 + 103802533398 * (m - 5) + 136283024880 := by ring
  apply sub_pos.mp
  apply pos_of_mul_pos_right (a := (917968750 : ℝ)) _ (by norm_num)
  rw [hid]
  positivity

lemma distillT0_le_middle {m α : ℝ} (hm : 5 ≤ m)
    (hα : 7 / 5 ≤ α) (hα2 : α ≤ 2) : distillT0 m α ≤ 13 / 50 := by
  have hm0 : 0 < m := by linarith
  by_cases hsplit : α ≤ 17 / 10
  · have hd : 0 < (31 / 50 : ℝ) * m - 12 * (17 / 10) / 25 := by linarith
    have h := distillT0_le_mixed_rational hm (by norm_num : (0 : ℝ) ≤ 7 / 5)
      hα hsplit (by linarith : 2 * (17 / 10 : ℝ) ≤ m)
      (by norm_num [distillRatio] : distillRatio (7 / 5) ≤ 5 / 22)
      (by norm_num [distillPeakD, cubicPolarEnvelope] : (31 / 50 : ℝ) ≤ distillPeakD (17 / 10))
      hd
    apply h.trans (le_of_lt _)
    apply (div_lt_iff₀ (by positivity :
      0 < (m + 3) * (m + 5) * ((31 / 50) * m - 12 * (17 / 10) / 25) ^ 4)).mpr
    exact middle_T0_lower_polynomial hm
  · have hd : 0 < (3 / 5 : ℝ) * m - 12 * 2 / 25 := by linarith
    have h := distillT0_le_mixed_rational hm (by norm_num : (0 : ℝ) ≤ 17 / 10)
      (by linarith : (17 / 10 : ℝ) ≤ α) hα2 (by linarith : 2 * (2 : ℝ) ≤ m)
      (by norm_num [distillRatio] : distillRatio (17 / 10) ≤ 10 / 47)
      (by norm_num [distillPeakD, cubicPolarEnvelope] : (3 / 5 : ℝ) ≤ distillPeakD 2)
      hd
    apply h.trans (le_of_lt _)
    apply (div_lt_iff₀ (by positivity :
      0 < (m + 3) * (m + 5) * ((3 / 5) * m - 12 * 2 / 25) ^ 4)).mpr
    exact middle_T0_upper_polynomial hm

lemma distillT1_le_middle {m α : ℝ} (hm : 5 ≤ m)
    (hα : 7 / 5 ≤ α) (hα2 : α ≤ 2) : distillT1 m α ≤ 7 / 30 := by
  by_cases hsplit : α ≤ 17 / 10
  · have h := distillT1_le_mixed_peak hm (by norm_num : (0 : ℝ) ≤ 7 / 5)
      (by norm_num : (1 : ℝ) ≤ 17 / 10) hα hsplit (by linarith)
    have hlin := distill_mixed_peak1_le_linear (by norm_num : (0 : ℝ) ≤ 7 / 5)
      (by norm_num : (1 : ℝ) ≤ 17 / 10)
      (by norm_num [distillPeakRate1, distillPeakBoost1, distillPeakNode, cubicPolarEnvelope])
    refine (h.trans hlin).trans ?_
    norm_num [distillLinearExpPeak, distillRatio, distillPeakRate1,
      distillPeakBoost1, distillPeakNode, cubicPolarEnvelope]
  · have h := distillT1_le_mixed_peak hm (by norm_num : (0 : ℝ) ≤ 17 / 10)
      (by norm_num : (1 : ℝ) ≤ 2) (by linarith : (17 / 10 : ℝ) ≤ α) hα2 (by linarith)
    have hlin := distill_mixed_peak1_le_linear (by norm_num : (0 : ℝ) ≤ 17 / 10)
      (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num [distillPeakRate1, distillPeakBoost1, distillPeakNode, cubicPolarEnvelope])
    refine (h.trans hlin).trans ?_
    norm_num [distillLinearExpPeak, distillRatio, distillPeakRate1,
      distillPeakBoost1, distillPeakNode, cubicPolarEnvelope]

lemma distillT2_le_middle {m α : ℝ} (hm : 5 ≤ m)
    (hα : 7 / 5 ≤ α) (hα2 : α ≤ 2) : distillT2 m α ≤ 1 / 6 := by
  by_cases hsplit : α ≤ 17 / 10
  · have h := distillT2_le_mixed_peak hm (by norm_num : (0 : ℝ) ≤ 7 / 5)
      (by norm_num : (0 : ℝ) < 17 / 10) hα hsplit (by linarith)
    have hlin := distill_mixed_peak2_le_linear (by norm_num : (0 : ℝ) ≤ 7 / 5)
      (by norm_num : (0 : ℝ) ≤ 17 / 10)
      (by norm_num [distillPeakRate2, cubicPolarEnvelope])
    refine (h.trans hlin).trans ?_
    norm_num [distillLinearExpPeak, distillRatio, distillPeakRate2, cubicPolarEnvelope]
  · have h := distillT2_le_mixed_peak hm (by norm_num : (0 : ℝ) ≤ 17 / 10)
      (by norm_num : (0 : ℝ) < 2) (by linarith : (17 / 10 : ℝ) ≤ α) hα2 (by linarith)
    have hlin := distill_mixed_peak2_le_linear (by norm_num : (0 : ℝ) ≤ 17 / 10)
      (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num [distillPeakRate2, cubicPolarEnvelope])
    refine (h.trans hlin).trans ?_
    norm_num [distillLinearExpPeak, distillRatio, distillPeakRate2, cubicPolarEnvelope]

/-- Both alpha endpoints and all real degrees are included; there is no finite base. -/
theorem distillScalar_lt_one_middle_alpha {m α : ℝ} (hm : 5 ≤ m)
    (hα : 7 / 5 ≤ α) (hα2 : α ≤ 2) (hαm : 2 * α ≤ m) :
    scalarObstruction m α (cubicPolarEnvelope α) < 1 := by
  have h := distillScalar_le_elementary_components hm (by linarith : 0 < α) hαm
  have hE := distillElementary_le_middle hm hα
  have h0 := distillT0_le_middle hm hα hα2
  have h1 := distillT1_le_middle hm hα hα2
  have h2 := distillT2_le_middle hm hα hα2
  linarith only [h, hE, h0, h1, h2]

/-- The inherited small-alpha argument and the new strip cover all `0<alpha<=2`. -/
theorem distillScalar_lt_one_alpha_le_two {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hα2 : α ≤ 2) (hαm : 2 * α ≤ m) :
    scalarObstruction m α (cubicPolarEnvelope α) < 1 := by
  by_cases hsmall : α ≤ 7 / 5
  · exact distillScalar_lt_one_small_alpha hm hα hsmall
  · exact distillScalar_lt_one_middle_alpha hm (by linarith) hα2 hαm

end Sendov
