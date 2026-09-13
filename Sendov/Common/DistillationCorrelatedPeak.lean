import Sendov.Common.DistillationTotalBound

/-!
# Same-alpha degree peaks

The shift is `m - 2 * alpha`, not `m - 34`. All bounds below cover the
entire legal real-degree ray. No finite row or old tail theorem is imported.
-/

namespace Sendov

lemma log_le_pade {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.log x ≤ -2 * ((1 - x) / (1 + x)) := by
  let f := fun y : ℝ => Real.log y - 2 * (y - 1) / (y + 1)
  have hd (y : ℝ) (hy : 0 < y) :
      HasDerivAt f ((y - 1) ^ 2 / (y * (y + 1) ^ 2)) y := by
    have h := (Real.hasDerivAt_log hy.ne').sub
      ((((hasDerivAt_id' y).sub_const 1).const_mul 2).div
        ((hasDerivAt_id' y).add_const 1) (by linarith))
    apply h.congr_deriv
    field_simp
    ring
  have hmono : MonotoneOn f (Set.Ioi 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    have hy0 : 0 < y := interior_subset hy
    exact div_nonneg (sq_nonneg _) (by positivity)
  have h := hmono hx (by norm_num : (1 : ℝ) ∈ Set.Ioi 0) hx1
  dsimp [f] at h
  norm_num at h
  have hid : 2 * (x - 1) / (x + 1) = -2 * ((1 - x) / (1 + x)) := by ring
  linarith

private lemma pow_mul_exp_peak {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c)
    (n : ℕ) (hn : 0 < n) :
    t ^ n * Real.exp (-c * t) ≤
      ((n : ℝ) / c) ^ n * Real.exp (-(n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h := pow_le_pow_left₀
    (mul_nonneg (div_nonneg (mul_nonneg hc.le ht) hn0.le) (Real.exp_nonneg _))
    (Real.mul_exp_neg_le_exp_neg_one (c * t / n)) n
  rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul] at h
  have he : (n : ℝ) * -(c * t / n) = -c * t := by field_simp
  rw [he] at h
  have hmul := mul_le_mul_of_nonneg_left h (pow_nonneg (div_nonneg hn0.le hc.le) n)
  have hid : ((n : ℝ) / c) ^ n * ((c * t / n) ^ n * Real.exp (-c * t)) =
      t ^ n * Real.exp (-c * t) := by
    rw [← mul_assoc, ← mul_pow]
    congr 2
    field_simp
  simpa only [hid, mul_neg, mul_one] using hmul

noncomputable def distillExpPeak (α c : ℝ) : ℝ :=
  Real.exp (-c * (2 * α - 3)) *
    (27 * Real.exp (-3) / c ^ 3 + 8 * α * Real.exp (-2) / c ^ 2)

/-- The two polynomial terms peak separately, but at the same alpha. -/
lemma distill_degree_exp_le_peak {m α c : ℝ} (hα : 0 ≤ α)
    (hαm : 2 * α ≤ m) (hc : 0 < c) :
    m * (m - 2 * α) ^ 2 * Real.exp (-c * (m - 3)) ≤
      distillExpPeak α c := by
  let t := m - 2 * α
  have ht : 0 ≤ t := sub_nonneg.mpr hαm
  have h2 := pow_mul_exp_peak ht hc 2 (by norm_num)
  have h3 := pow_mul_exp_peak ht hc 3 (by norm_num)
  have hsum := add_le_add h3 (mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * α))
  have hexp : Real.exp (-c * (m - 3)) =
      Real.exp (-c * (2 * α - 3)) * Real.exp (-c * t) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [t]
    ring
  rw [hexp]
  unfold distillExpPeak
  have hid : m * (m - 2 * α) ^ 2 *
      (Real.exp (-c * (2 * α - 3)) * Real.exp (-c * t)) =
      Real.exp (-c * (2 * α - 3)) *
        (t ^ 3 * Real.exp (-c * t) + 2 * α * (t ^ 2 * Real.exp (-c * t))) := by
    dsimp [t]
    ring
  rw [hid]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  convert hsum using 1
  norm_num
  ring

noncomputable def distillPeak2 (α : ℝ) : ℝ :=
  (421 / 12500) * distillRatio α *
    distillExpPeak α (-Real.log (cubicPolarEnvelope α) / 2)

lemma distillKappa_le_shifted_cubic {m α : ℝ} (hm : 0 < m) (hα : 0 ≤ α) :
    distillKappa m α ≤ distillRatio α / 4 * (m * (m - 2 * α) ^ 2) := by
  have hbase : (m ^ 2 - 1) / (4 * m) ≤ m / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * m)).mpr
    nlinarith
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbase (distillRatio_nonneg hα)) (sq_nonneg (m - 2 * α))
  exact h.trans_eq (by ring)

/-- An explicit uniform degree bound; no optimizer or assumed maximum occurs. -/
theorem distillT2_le_peak {m α : ℝ} (hm : 5 ≤ m) (hα : 0 < α)
    (hαm : 2 * α ≤ m) : distillT2 m α ≤ distillPeak2 α := by
  have hm0 : 0 < m := by linarith
  have he := cubicPolarEnvelope_pos hα
  have hc : 0 < -Real.log (cubicPolarEnvelope α) / 2 :=
    div_pos (neg_pos.mpr (Real.log_neg he (cubicPolarEnvelope_lt_one hα.le))) (by norm_num)
  have hK := distillKappa_le_shifted_cubic hm0 hα.le
  have hpow : cubicPolarEnvelope α ^ ((m - 3) / 2) =
      Real.exp (-(-Real.log (cubicPolarEnvelope α) / 2) * (m - 3)) := by
    rw [Real.rpow_def_of_pos he]
    congr 1
    ring
  have hpeak := distill_degree_exp_le_peak hα.le hαm hc
  rw [distillT2, hpow]
  calc
    _ ≤ (421 / 3125) * (distillRatio α / 4 * (m * (m - 2 * α) ^ 2)) *
        Real.exp (-(-Real.log (cubicPolarEnvelope α) / 2) * (m - 3)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hK (by norm_num)) (Real.exp_nonneg _)
    _ = (421 / 12500) * distillRatio α *
        (m * (m - 2 * α) ^ 2 *
          Real.exp (-(-Real.log (cubicPolarEnvelope α) / 2) * (m - 3))) := by ring
    _ ≤ distillPeak2 α := mul_le_mul_of_nonneg_left hpeak
      (mul_nonneg (by norm_num) (distillRatio_nonneg hα.le))

noncomputable def distillPeakNode (α : ℝ) : ℝ :=
  8 / 25 + 3 / 5 * cubicPolarEnvelope α

noncomputable def distillPeakRate1 (α : ℝ) : ℝ :=
  (1 - distillPeakNode α) / (1 + distillPeakNode α) +
    (2 / 25) * (α - 1) / (α * distillPeakNode α)

noncomputable def distillPeakBoost1 (α : ℝ) : ℝ :=
  (6 / 25) * (α - 1) ^ 2 / (α * distillPeakNode α)

noncomputable def distillPeak1 (α : ℝ) : ℝ :=
  (259 / 12500) * distillRatio α * Real.exp (distillPeakBoost1 α) *
    distillExpPeak α (distillPeakRate1 α)

lemma distillPeakNode_pos {α : ℝ} (hα : 0 ≤ α) : 0 < distillPeakNode α := by
  have := cubicPolarEnvelope_nonneg hα
  unfold distillPeakNode
  linarith

lemma distillPeakNode_lt_one {α : ℝ} (hα : 0 ≤ α) : distillPeakNode α < 1 := by
  have := cubicPolarEnvelope_lt_one hα
  unfold distillPeakNode
  linarith

lemma distillPeakRate1_pos {α : ℝ} (hα : 1 ≤ α) : 0 < distillPeakRate1 α := by
  have hb := distillPeakNode_pos (by linarith : 0 ≤ α)
  have hb1 := distillPeakNode_lt_one (by linarith : 0 ≤ α)
  have hfirst : 0 < (1 - distillPeakNode α) / (1 + distillPeakNode α) :=
    div_pos (by linarith) (by linarith)
  have hsecond : 0 ≤ (2 / 25 : ℝ) * (α - 1) / (α * distillPeakNode α) :=
    div_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)
  exact add_pos_of_pos_of_nonneg hfirst hsecond

/-- The reciprocal correction is a nonnegative square, not a discarded term. -/
lemma distillNode_rpow_le_exp {m α : ℝ} (hm : 5 ≤ m) (hα : 1 ≤ α) :
    distillNode m α ^ ((m - 3) / 2) ≤
      Real.exp (-distillPeakRate1 α * (m - 3) + distillPeakBoost1 α) := by
  have hα0 : 0 < α := by linarith
  have hm0 : 0 < m := by linarith
  have hb := distillPeakNode_pos hα0.le
  have hb1 := distillPeakNode_lt_one hα0.le
  have hn := distillNode_pos hm0 hα0.le
  have hlog := Real.log_le_sub_one_of_pos (div_pos hn hb)
  rw [Real.log_div hn.ne' hb.ne'] at hlog
  have hpade := log_le_pade hb hb1.le
  have hlogbound : Real.log (distillNode m α) ≤
      -2 * ((1 - distillPeakNode α) / (1 + distillPeakNode α)) +
        (distillNode m α - distillPeakNode α) / distillPeakNode α := by
    have hid : (distillNode m α - distillPeakNode α) / distillPeakNode α =
        distillNode m α / distillPeakNode α - 1 := by field_simp
    linarith
  have hmul := mul_le_mul_of_nonneg_right hlogbound (by linarith : 0 ≤ (m - 3) / 2)
  have hgap :
      -distillPeakRate1 α * (m - 3) + distillPeakBoost1 α -
        (-2 * ((1 - distillPeakNode α) / (1 + distillPeakNode α)) +
          (distillNode m α - distillPeakNode α) / distillPeakNode α) * ((m - 3) / 2) =
      (2 / 25) * (m - 3 * α) ^ 2 / (α * distillPeakNode α * m) := by
    unfold distillPeakRate1 distillPeakBoost1
    have hnode : distillNode m α = distillPeakNode α - 4 / 25 + 12 * α / (25 * m) := by
      unfold distillNode distillPeakNode
      ring
    rw [hnode]
    have hbplus : 1 + distillPeakNode α ≠ 0 := by positivity
    field_simp
    ring
  have hnonneg : 0 ≤ (2 / 25 : ℝ) * (m - 3 * α) ^ 2 /
      (α * distillPeakNode α * m) := by positivity
  rw [Real.rpow_def_of_pos hn]
  exact Real.exp_le_exp.mpr (by linarith)

theorem distillT1_le_peak {m α : ℝ} (hm : 5 ≤ m) (hα : 1 ≤ α)
    (hαm : 2 * α ≤ m) : distillT1 m α ≤ distillPeak1 α := by
  have hα0 : 0 ≤ α := by linarith
  have hm0 : 0 < m := by linarith
  have hK := distillKappa_le_shifted_cubic hm0 hα0
  have hpow := distillNode_rpow_le_exp hm hα
  have hp := mul_le_mul hK hpow
    (Real.rpow_nonneg (distillNode_pos hm0 hα0).le _) (by
      have := distillRatio_nonneg hα0
      positivity)
  have hpeak := distill_degree_exp_le_peak hα0 hαm (distillPeakRate1_pos hα)
  have h := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 259 / 3125)
  have hscaled := mul_le_mul_of_nonneg_left hpeak
    (by have := distillRatio_nonneg hα0
        positivity : 0 ≤ (259 / 12500) * distillRatio α * Real.exp (distillPeakBoost1 α))
  rw [Real.exp_add] at h
  unfold distillT1 distillPeak1
  nlinarith only [h, hscaled]

noncomputable def distillPeakRate2 (α : ℝ) : ℝ :=
  (1 - cubicPolarEnvelope α) / (1 + cubicPolarEnvelope α)

lemma distillPeakRate2_pos {α : ℝ} (hα : 0 ≤ α) : 0 < distillPeakRate2 α :=
  div_pos (sub_pos.mpr (cubicPolarEnvelope_lt_one hα))
    (by have := cubicPolarEnvelope_nonneg hα; positivity)

private lemma quartic_peak {z l : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) :
    z ^ 2 * (1 - z) * (1 - l * z) ≤ (1 - l) * (4 / 27) + l / 16 := by
  have h3 : z ^ 2 * (1 - z) ≤ 4 / 27 := by
    have h := mul_nonneg (sq_nonneg (z - 2 / 3)) (by linarith : 0 ≤ z + 1 / 3)
    nlinarith
  have h4 : z ^ 2 * (1 - z) ^ 2 ≤ 1 / 16 := by
    have hp : 0 ≤ z * (1 - z) := mul_nonneg hz (by linarith)
    have hq : z * (1 - z) ≤ 1 / 4 := by nlinarith [sq_nonneg (z - 1 / 2)]
    have hs := pow_le_pow_left₀ hp hq 2
    nlinarith only [hs]
  have h := add_le_add
    (mul_le_mul_of_nonneg_left h3 (by linarith : 0 ≤ 1 - l))
    (mul_le_mul_of_nonneg_left h4 hl)
  nlinarith only [h]

noncomputable def distillPeakD (α : ℝ) : ℝ :=
  21 / 25 - 3 / 5 * cubicPolarEnvelope α

noncomputable def distillPeak0 (α : ℝ) : ℝ :=
  (972 / 625) * distillRatio α * (4 * distillPeakD α / 27 - 37 / 1800) /
    (α * distillPeakD α ^ 3 * (distillPeakD α - 6 / 25) ^ 2)

lemma distillPeakD_gt {α : ℝ} (hα : 0 ≤ α) : 6 / 25 < distillPeakD α := by
  have := cubicPolarEnvelope_lt_one hα
  unfold distillPeakD
  linarith

/-- A quartic peak bound after compactifying the entire degree ray. -/
theorem distillT0_le_peak {m α : ℝ} (hm : 5 ≤ m) (hα : 0 < α)
    (hαm : 2 * α ≤ m) : distillT0 m α ≤ distillPeak0 α := by
  have hm0 : 0 < m := by linarith
  have hm1 : m - 1 ≠ 0 := by linarith
  have hnode := distillNode_lt_one hm0 hα.le (by linarith)
  let d := distillPeakD α
  have hd : 6 / 25 < d := distillPeakD_gt hα.le
  have hd0 : 0 < d := by linarith
  let l := (6 / 25) / d
  have hl : 0 ≤ l := by dsimp [l]; positivity
  have hl1 : l < 1 := (div_lt_one hd0).mpr hd
  let q := m - 2 * α * l
  have hq : 0 < q := by
    have h := mul_pos hα (sub_pos.mpr hl1)
    dsimp [q]
    nlinarith
  let z := (m - 2 * α) / q
  have hz : 0 ≤ z := div_nonneg (by linarith) hq.le
  have hz1 : z ≤ 1 := by
    apply (div_le_one hq).mpr
    dsimp [q]
    nlinarith
  let A := 24 * (3 / 5 : ℝ) ^ 4 * distillRatio α *
    m * (m - 2 * α) ^ 2 / (d * m - 12 * α / 25) ^ 4
  have hdenid : d * m - 12 * α / 25 = d * q := by
    dsimp [q, l]
    field_simp
    ring
  have hden : 0 < d * m - 12 * α / 25 := by
    rw [hdenid]
    positivity
  have hA : 0 ≤ A := by
    have := distillRatio_nonneg hα.le
    dsimp [A]
    positivity
  have hT : distillT0 m α = A * (m ^ 2 / ((m + 3) * (m + 5))) := by
    have hnodeid : 1 - distillNode m α = (d * m - 12 * α / 25) / m := by
      dsimp [d, distillPeakD, distillNode]
      field_simp
      ring
    unfold distillT0 distillKappa
    rw [hnodeid]
    dsimp [A]
    field_simp
    ring
  have hTA : distillT0 m α ≤ A := by
    rw [hT]
    apply mul_le_of_le_one_right hA
    apply (div_le_one (by positivity : 0 < (m + 3) * (m + 5))).mpr
    nlinarith
  let C := 24 * (3 / 5 : ℝ) ^ 4 * distillRatio α /
    (2 * α * d ^ 4 * (1 - l) ^ 2)
  have hC : 0 ≤ C := by
    have := distillRatio_nonneg hα.le
    dsimp [C]
    positivity
  have hAz : A = C * (z ^ 2 * (1 - z) * (1 - l * z)) := by
    have hlne : 1 - l ≠ 0 := by linarith
    dsimp [A, C, z]
    rw [hdenid]
    field_simp [hq.ne', hlne, hα.ne', hd0.ne']
    dsimp [q]
    ring
  have hcap : C * ((1 - l) * (4 / 27) + l / 16) = distillPeak0 α := by
    dsimp [C, l, distillPeak0]
    change _ = (972 / 625) * distillRatio α * (4 * d / 27 - 37 / 1800) /
      (α * d ^ 3 * (d - 6 / 25) ^ 2)
    have hsub : d - 6 / 25 ≠ 0 := by linarith
    field_simp
    ring
  rw [hAz] at hTA
  exact hTA.trans ((mul_le_mul_of_nonneg_left (quartic_peak hz hz1 hl hl1.le) hC).trans_eq hcap)

noncomputable def distillElementary (m α : ℝ) : ℝ :=
  distillRatio α / (2 * (1 - cubicPolarEnvelope α)) + distillRatio α / 4 +
    (1 / 2 + distillRatio α / 4) / m

lemma distillElementary_antitone_degree {m k α : ℝ} (hk : 0 < k)
    (hkm : k ≤ m) (hα : 0 ≤ α) :
    distillElementary m α ≤ distillElementary k α := by
  unfold distillElementary
  have hnum : 0 ≤ 1 / 2 + distillRatio α / 4 := by
    have := distillRatio_nonneg hα
    positivity
  exact add_le_add le_rfl (div_le_div_of_nonneg_left hnum hk hkm)

/-- Keep the actual elementary term before choosing any component peak estimates. -/
theorem distillScalar_le_elementary_components {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hαm : 2 * α ≤ m) :
    scalarObstruction m α (cubicPolarEnvelope α) ≤
      distillElementary m α + distillT0 m α + distillT1 m α + distillT2 m α := by
  have h := distillScalar_le_total_sub_loss hm hα hαm
  have hE : distillEBudget m - distillElementaryLoss m α = distillElementary m α := by
    have hid := distillScalar_eq_loss_integral (by linarith : 0 < m) hα
    unfold scalarObstruction at hid
    rw [← distillKappa_eq hα] at hid
    rw [← add_right_cancel hid]
    unfold distillElementary
    rw [distillRatio_eq hα]
    have he := (sub_pos.mpr (cubicPolarEnvelope_lt_one hα.le)).ne'
    have hm0 : m ≠ 0 := by linarith
    field_simp
    ring
  unfold distillTotal at h
  linarith only [h, hE]

/-- Actual elementary E is bounded on the same legal degree domain. -/
theorem distillScalar_le_correlated_peak2 {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hαm : 2 * α ≤ m) :
    scalarObstruction m α (cubicPolarEnvelope α) ≤
      distillElementary (max 5 (2 * α)) α +
        distillT0 m α + distillT1 m α + distillPeak2 α := by
  have h := distillScalar_le_elementary_components hm hα hαm
  have hEbound := distillElementary_antitone_degree
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 5) (le_max_left 5 (2 * α)))
    (max_le hm hαm) hα.le
  have h2 := distillT2_le_peak hm hα hαm
  linarith

noncomputable def distillCorrelatedPeak (α : ℝ) : ℝ :=
  distillElementary (max 5 (2 * α)) α +
    distillPeak0 α + distillPeak1 α + distillPeak2 α

/-- All three degree bounds retain the same original alpha. -/
theorem distillScalar_le_correlated_peak {m α : ℝ} (hm : 5 ≤ m)
    (hα : 1 ≤ α) (hαm : 2 * α ≤ m) :
    scalarObstruction m α (cubicPolarEnvelope α) ≤ distillCorrelatedPeak α := by
  have hα0 : 0 < α := by linarith
  have h := distillScalar_le_correlated_peak2 hm hα0 hαm
  have h0 := distillT0_le_peak hm hα0 hαm
  have h1 := distillT1_le_peak hm hα hαm
  unfold distillCorrelatedPeak
  linarith

end Sendov
