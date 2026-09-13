import Sendov.Common.DistillationFactors

/-!
# Critical polynomials and derivatives of the distillation components

Adaptation of Senjian An, *Proof Distillation for Sendov's Conjecture*,
revision e8ae601491ec171ab4f7f8456113dd6a047aa85d, Appendix B and (5.2)--(5.4).
Paper: CC BY 4.0, https://creativecommons.org/licenses/by/4.0/ .
The three definitions use exactly the descending coefficient order of
`verification/verify_paper.py`. They are not the old Sendov R or T1.
-/

namespace Sendov

noncomputable def distillCritical0 (m α : ℝ) : ℝ :=
  -4176 * α ^ 7 + 2 * (1363 * m - 36072) * α ^ 6 +
    (-377 * m ^ 2 + 22092 * m - 514512) * α ^ 5 +
    12 * (103 * m ^ 2 - 1323 * m - 161676) * α ^ 4 +
    1134 * (49 * m ^ 2 - 566 * m - 3600) * α ^ 3 +
    486 * (665 * m ^ 2 - 4752 * m - 9360) * α ^ 2 +
    972 * (743 * m ^ 2 - 3330 * m - 2160) * α + 43740 * m * (13 * m - 36)

noncomputable def distillCritical1 (m α : ℝ) : ℝ :=
  1392 * (m - 1) * α ^ 7 - 4 * (174 * m ^ 2 - 8279 * m + 4392) * α ^ 6 -
    2 * (2914 * m ^ 2 - 158961 * m + 34992) * α ^ 5 -
    3 * (783 * m ^ 3 - m ^ 2 - 538848 * m + 6048) * α ^ 4 -
    216 * (140 * m ^ 3 - 609 * m ^ 2 - 21974 * m - 2610) * α ^ 3 -
    216 * (660 * m ^ 3 - 2164 * m ^ 2 - 37581 * m - 6480) * α ^ 2 -
    648 * (450 * m ^ 3 - 934 * m ^ 2 - 11655 * m - 1620) * α -
    14580 * m * (15 * m ^ 2 - 17 * m - 204)

noncomputable def distillCritical2 (m α : ℝ) : ℝ :=
  116 * α ^ 4 + 2 * (110 * m + 453) * α ^ 3 -
    3 * (27 * m ^ 2 - 565 * m - 720) * α ^ 2 -
    540 * (m ^ 2 - 7 * m - 3) * α - 810 * m * (m - 3)

noncomputable def distillN (α : ℝ) : ℝ := 29 * α ^ 2 + 180 * α + 270

noncomputable def distillB (m α : ℝ) : ℝ :=
  24 * α ^ 4 + (37 * m + 216) * α ^ 3 + (252 * m + 648) * α ^ 2 +
    (486 * m + 648) * α + 216 * m

noncomputable def distillD (m α : ℝ) : ℝ := 50 * m * (α + 3) ^ 3 - distillB m α

noncomputable def distillK (m α : ℝ) : ℝ :=
  (α + 3) * (m - 2 * α) * (58 * α + 180) -
    (3 * (m - 2 * α) + 4 * (α + 3)) * distillN α

noncomputable def distillRp (m α : ℝ) : ℝ :=
  (α + 3) * (96 * α ^ 3 + 3 * (37 * m + 216) * α ^ 2 +
    2 * (252 * m + 648) * α + (486 * m + 648)) - 3 * distillB m α

noncomputable def distillL (α : ℝ) : ℝ := 81 * α ^ 2 + 540 * α + 810

lemma distillCritical0_eq (m α : ℝ) :
    distillCritical0 m α = distillK m α * distillD m α +
      4 * (m - 2 * α) * distillN α * distillRp m α := by
  unfold distillCritical0 distillK distillD distillN distillRp distillB
  ring

lemma distillCritical1_eq (m α : ℝ) :
    distillCritical1 m α = -2 * distillK m α * distillB m α -
      (m - 3) * (m - 2 * α) * distillN α * distillRp m α := by
  unfold distillCritical1 distillK distillN distillRp distillB
  ring

lemma distillCritical2_eq (m α : ℝ) :
    distillCritical2 m α = -2 * α * distillK m α -
      (m - 3) * (m - 2 * α) * distillL α := by
  unfold distillCritical2 distillK distillN distillL
  ring

lemma distillRatio_compact {α : ℝ} (hα : 0 ≤ α) :
    distillRatio α = distillN α / (30 * (α + 3) ^ 3) := by
  have ht : α + 3 ≠ 0 := by linarith
  unfold distillRatio distillN
  field_simp [ht]
  ring

lemma cubicPolarEnvelope_compact {α : ℝ} (hα : 0 ≤ α) :
    cubicPolarEnvelope α = α * distillN α / (30 * (α + 3) ^ 3) := by
  have ht : α + 3 ≠ 0 := by linarith
  unfold cubicPolarEnvelope distillN
  field_simp [ht]
  ring

lemma distillNode_compact {m α : ℝ} (hm : 0 < m) (hα : 0 ≤ α) :
    distillNode m α = distillB m α / (50 * m * (α + 3) ^ 3) := by
  rw [distillNode, cubicPolarEnvelope_compact hα]
  have ht : α + 3 ≠ 0 := by linarith
  unfold distillB distillN
  field_simp [ht, hm.ne']
  ring

lemma distillD_eq {m α : ℝ} (hm : 0 < m) (hα : 0 ≤ α) :
    distillD m α = 50 * m * (α + 3) ^ 3 * (1 - distillNode m α) := by
  rw [distillNode_compact hm hα, distillD]
  rw [mul_one_sub, mul_div_cancel₀ _ (by positivity)]

lemma distillN_pos {α : ℝ} (hα : 0 ≤ α) : 0 < distillN α := by
  unfold distillN
  positivity

lemma distillB_pos {m α : ℝ} (hm : 0 < m) (hα : 0 ≤ α) :
    0 < distillB m α := by
  unfold distillB
  positivity

lemma distillD_pos {m α : ℝ} (hm : 0 < m) (hα : 0 ≤ α) (hαm : α ≤ m / 2) :
    0 < distillD m α := by
  rw [distillD_eq hm hα]
  have := distillNode_lt_one hm hα hαm
  have : 0 < α + 3 := by linarith
  positivity

lemma distillRatio_pos {α : ℝ} (hα : 0 ≤ α) : 0 < distillRatio α := by
  rw [distillRatio_compact hα]
  exact div_pos (distillN_pos hα) (by positivity)

lemma cubicPolarEnvelope_pos {α : ℝ} (hα : 0 < α) : 0 < cubicPolarEnvelope α := by
  rw [cubicPolarEnvelope_compact hα.le]
  exact div_pos (mul_pos hα (distillN_pos hα.le)) (by positivity)

lemma distillKappa_pos {m α : ℝ} (hm : 5 ≤ m) (hα : 0 ≤ α) (hαm : 2 * α < m) :
    0 < distillKappa m α := by
  have hs : 0 < m ^ 2 - 1 := by nlinarith
  have hq : 0 < m - 2 * α := by linarith
  have hr := distillRatio_pos hα
  unfold distillKappa
  positivity

lemma distillT0_pos {m α : ℝ} (hm : 5 ≤ m) (hα : 0 ≤ α) (hαm : 2 * α < m) :
    0 < distillT0 m α := by
  have hk := distillKappa_pos hm hα hαm
  have hb := distillNode_lt_one (by linarith : 0 < m) hα (by linarith)
  have hm1 : 0 < m - 1 := by linarith
  unfold distillT0
  positivity

lemma distillT1_pos {m α : ℝ} (hm : 5 ≤ m) (hα : 0 ≤ α) (hαm : 2 * α < m) :
    0 < distillT1 m α := by
  have hk := distillKappa_pos hm hα hαm
  have hb := distillNode_pos (by linarith : 0 < m) hα
  unfold distillT1
  positivity

lemma distillT2_pos {m α : ℝ} (hm : 5 ≤ m) (hα : 0 < α) (hαm : 2 * α < m) :
    0 < distillT2 m α := by
  have hk := distillKappa_pos hm hα.le hαm
  have he := cubicPolarEnvelope_pos hα
  unfold distillT2
  positivity

lemma distillRatio_continuousOn : ContinuousOn distillRatio (Set.Ici 0) := by
  unfold distillRatio
  have hd : ∀ α ∈ Set.Ici (0 : ℝ), α + 3 ≠ 0 := by
    intro α hα
    have : 0 ≤ α := hα
    linarith
  have hu : ContinuousOn (fun α : ℝ ↦ α / (α + 3)) (Set.Ici 0) :=
    continuousOn_id.div (continuousOn_id.add continuousOn_const) hd
  fun_prop

lemma cubicPolarEnvelope_continuousOn : ContinuousOn cubicPolarEnvelope (Set.Ici 0) := by
  unfold cubicPolarEnvelope
  have hd : ∀ α ∈ Set.Ici (0 : ℝ), α + 3 ≠ 0 := by
    intro α hα
    have : 0 ≤ α := hα
    linarith
  have hu : ContinuousOn (fun α : ℝ ↦ α / (α + 3)) (Set.Ici 0) :=
    continuousOn_id.div (continuousOn_id.add continuousOn_const) hd
  fun_prop

lemma distillKappa_continuousOn (m : ℝ) :
    ContinuousOn (distillKappa m) (Set.Ici 0) := by
  unfold distillKappa
  exact (continuousOn_const.mul distillRatio_continuousOn).mul (by fun_prop)

lemma distillNode_continuousOn (m : ℝ) : ContinuousOn (distillNode m) (Set.Ici 0) := by
  unfold distillNode
  exact (continuousOn_const.add
    (continuousOn_const.mul cubicPolarEnvelope_continuousOn)).add (by fun_prop)

lemma distillT0_continuousOn {m : ℝ} (hm : 5 ≤ m) :
    ContinuousOn (distillT0 m) (Set.Icc 0 (m / 2)) := by
  have hk := (distillKappa_continuousOn m).mono (Set.Icc_subset_Ici_self (a := m / 2))
  have hb := (distillNode_continuousOn m).mono (Set.Icc_subset_Ici_self (a := m / 2))
  unfold distillT0
  apply hk.mul
  apply continuousOn_const.div
  · exact continuousOn_const.mul ((continuousOn_const.sub hb).pow 4)
  · intro α hα
    have hm1 : 0 < m - 1 := by linarith
    have hn := distillNode_lt_one (by linarith : 0 < m) hα.1 hα.2
    positivity

lemma distillT1_continuousOn {m : ℝ} (hm : 5 ≤ m) :
    ContinuousOn (distillT1 m) (Set.Icc 0 (m / 2)) := by
  have hk := (distillKappa_continuousOn m).mono (Set.Icc_subset_Ici_self (a := m / 2))
  have hb := (distillNode_continuousOn m).mono (Set.Icc_subset_Ici_self (a := m / 2))
  unfold distillT1
  exact (continuousOn_const.mul hk).mul (hb.rpow_const (fun _ _ ↦ Or.inr (by linarith)))

lemma distillT2_continuousOn {m : ℝ} (hm : 5 ≤ m) :
    ContinuousOn (distillT2 m) (Set.Icc 0 (m / 2)) := by
  have hk := (distillKappa_continuousOn m).mono (Set.Icc_subset_Ici_self (a := m / 2))
  have he := cubicPolarEnvelope_continuousOn.mono (Set.Icc_subset_Ici_self (a := m / 2))
  unfold distillT2
  exact (continuousOn_const.mul hk).mul (he.rpow_const (fun _ _ ↦ Or.inr (by linarith)))

/- The derivative calculation is factored through small logarithmic-slope
identities. No expanded degree-seven polynomial enters rational simplification. -/
private lemma hasDerivAt_distillU {α : ℝ} (hα : 0 ≤ α) :
    HasDerivAt (fun x : ℝ ↦ x / (x + 3)) (3 / (α + 3) ^ 2) α := by
  have ht : α + 3 ≠ 0 := by linarith
  convert! (hasDerivAt_id α).div ((hasDerivAt_id α).add_const 3) ht using 1
  simp only [id_eq]
  ring

lemma hasDerivAt_distillRatio {α : ℝ} (hα : 0 ≤ α) :
    HasDerivAt distillRatio
      (distillRatio α * ((58 * α + 180) / distillN α - 3 / (α + 3))) α := by
  have hu := hasDerivAt_distillU hα
  have ht : α + 3 ≠ 0 := by linarith
  have hn := (distillN_pos hα).ne'
  convert! ((hu.const_sub 1).mul ((hu.pow 2 |>.div_const 30).const_sub 1)).div_const 3
    using 1
  · rw [distillRatio_compact hα]
    norm_num only [Pi.pow_apply, Nat.reduceSub, Nat.cast_ofNat, pow_one, mul_one]
    field_simp [ht, hn]
    unfold distillN
    ring

lemma hasDerivAt_cubicPolarEnvelope {α : ℝ} (hα : 0 ≤ α) :
    HasDerivAt cubicPolarEnvelope (distillL α / (30 * (α + 3) ^ 4)) α := by
  have hu := hasDerivAt_distillU hα
  have ht : α + 3 ≠ 0 := by linarith
  convert! hu.sub ((hu.pow 3).div_const 30) using 1
  · unfold distillL
    norm_num only [Nat.reduceSub, Nat.cast_ofNat]
    field_simp [ht]
    ring

lemma hasDerivAt_distillNode {m α : ℝ} (hm : 0 < m) (hα : 0 ≤ α) :
    HasDerivAt (distillNode m) (distillRp m α / (50 * m * (α + 3) ^ 4)) α := by
  have he := hasDerivAt_cubicPolarEnvelope hα
  have ht : α + 3 ≠ 0 := by linarith
  convert! ((he.const_mul (3 / 5)).const_add (4 / 25)).add
    (((hasDerivAt_id α).const_mul 12).div_const (25 * m)) using 1
  · field_simp [ht, hm.ne']
    unfold distillRp distillB distillL
    ring

lemma hasDerivAt_distillKappa {m α : ℝ} (hα : 0 ≤ α) (hαm : 2 * α < m) :
    HasDerivAt (distillKappa m)
      (distillKappa m α * (distillK m α / ((α + 3) * (m - 2 * α) * distillN α))) α := by
  have hr := hasDerivAt_distillRatio hα
  have ht : α + 3 ≠ 0 := by linarith
  have hq : m - 2 * α ≠ 0 := by linarith
  have hn := (distillN_pos hα).ne'
  convert! (hr.const_mul ((m ^ 2 - 1) / (4 * m))).mul
    ((((hasDerivAt_id α).const_mul 2).const_sub m).pow 2) using 1
  · unfold distillKappa distillK
    norm_num only [Pi.pow_apply, id_eq, Nat.reduceSub, Nat.cast_ofNat, pow_one, mul_one]
    field_simp [ht, hq, hn]
    ring

private lemma hasDerivAt_mul_slope {f g : ℝ → ℝ} {α u v : ℝ}
    (hf : HasDerivAt f (f α * u) α) (hg : HasDerivAt g (g α * v) α) :
    HasDerivAt (fun x ↦ f x * g x) (f α * g α * (u + v)) α := by
  convert! hf.mul hg using 1
  ring

private lemma hasDerivAt_rpow_slope {f : ℝ → ℝ} {α u p : ℝ}
    (hf : HasDerivAt f (f α * u) α) (hpos : 0 < f α) :
    HasDerivAt (fun x ↦ f x ^ p) (f α ^ p * (p * u)) α := by
  convert! hf.rpow_const (Or.inl hpos.ne') using 1
  rw [Real.rpow_sub hpos, Real.rpow_one]
  field_simp

private lemma hasDerivAt_distillNode_slope {m α : ℝ} (hm : 0 < m) (hα : 0 ≤ α) :
    HasDerivAt (distillNode m)
      (distillNode m α * (distillRp m α / ((α + 3) * distillB m α))) α := by
  convert! hasDerivAt_distillNode hm hα using 1
  rw [distillNode_compact hm hα]
  have ht : α + 3 ≠ 0 := by linarith
  have hb := (distillB_pos hm hα).ne'
  field_simp [ht, hb, hm.ne']

private lemma hasDerivAt_cubicPolarEnvelope_slope {α : ℝ} (hα : 0 < α) :
    HasDerivAt cubicPolarEnvelope
      (cubicPolarEnvelope α * (distillL α / (α * (α + 3) * distillN α))) α := by
  convert! hasDerivAt_cubicPolarEnvelope hα.le using 1
  rw [cubicPolarEnvelope_compact hα.le]
  have ht : α + 3 ≠ 0 := by linarith
  have hn := (distillN_pos hα.le).ne'
  field_simp [ht, hn, hα.ne']

lemma hasDerivAt_distillT1 {m α : ℝ} (hm : 5 ≤ m) (hα : 0 < α) (hαm : 2 * α < m) :
    HasDerivAt (distillT1 m)
      (distillT1 m α * (-distillCritical1 m α /
        (2 * (α + 3) * (m - 2 * α) * distillN α * distillB m α))) α := by
  have hm0 : 0 < m := by linarith
  have hk := hasDerivAt_distillKappa hα.le hαm
  have hb := hasDerivAt_rpow_slope (p := (m - 3) / 2)
    (hasDerivAt_distillNode_slope hm0 hα.le) (distillNode_pos hm0 hα.le)
  have hs : distillK m α / ((α + 3) * (m - 2 * α) * distillN α) +
      (m - 3) / 2 * (distillRp m α / ((α + 3) * distillB m α)) =
      -distillCritical1 m α /
        (2 * (α + 3) * (m - 2 * α) * distillN α * distillB m α) := by
    rw [distillCritical1_eq]
    have ht : α + 3 ≠ 0 := by linarith
    have hq : m - 2 * α ≠ 0 := by linarith
    have hn := (distillN_pos hα.le).ne'
    have hB := (distillB_pos hm0 hα.le).ne'
    generalize hq' : m - 2 * α = q at hq ⊢
    field_simp [ht, hq, hn, hB]
    ring
  have hd := (hasDerivAt_mul_slope hk hb).const_mul (259 / 3125)
  rw [hs] at hd
  unfold distillT1
  simpa only [mul_assoc] using hd

lemma hasDerivAt_distillT2 {m α : ℝ} (_hm : 5 ≤ m) (hα : 0 < α) (hαm : 2 * α < m) :
    HasDerivAt (distillT2 m)
      (distillT2 m α * (-distillCritical2 m α /
        (2 * α * (α + 3) * (m - 2 * α) * distillN α))) α := by
  have hk := hasDerivAt_distillKappa hα.le hαm
  have he := hasDerivAt_rpow_slope (p := (m - 3) / 2)
    (hasDerivAt_cubicPolarEnvelope_slope hα) (cubicPolarEnvelope_pos hα)
  have hs : distillK m α / ((α + 3) * (m - 2 * α) * distillN α) +
      (m - 3) / 2 * (distillL α / (α * (α + 3) * distillN α)) =
      -distillCritical2 m α /
        (2 * α * (α + 3) * (m - 2 * α) * distillN α) := by
    rw [distillCritical2_eq]
    have ht : α + 3 ≠ 0 := by linarith
    have hq : m - 2 * α ≠ 0 := by linarith
    have hn := (distillN_pos hα.le).ne'
    generalize hq' : m - 2 * α = q at hq ⊢
    field_simp [ht, hq, hn, hα.ne']
    ring
  have hd := (hasDerivAt_mul_slope hk he).const_mul (421 / 3125)
  rw [hs] at hd
  unfold distillT2
  simpa only [mul_assoc] using hd

private lemma hasDerivAt_reciprocal_quartic {f : ℝ → ℝ} {α d A C : ℝ}
    (hf : HasDerivAt f d α) (hC : C ≠ 0) (hb : 1 - f α ≠ 0) :
    HasDerivAt (fun x ↦ A / (C * (1 - f x) ^ 4))
      ((A / (C * (1 - f α) ^ 4)) * (4 * d / (1 - f α))) α := by
  convert! (hasDerivAt_const α A).div (((hf.const_sub 1).pow 4).const_mul C)
    (mul_ne_zero hC (pow_ne_zero 4 hb)) using 1
  norm_num only [Pi.pow_apply, Nat.reduceSub, Nat.cast_ofNat]
  field_simp [hC, hb]
  ring

lemma hasDerivAt_distillT0 {m α : ℝ} (hm : 5 ≤ m) (hα : 0 < α) (hαm : 2 * α < m) :
    HasDerivAt (distillT0 m)
      (distillT0 m α * (distillCritical0 m α /
        ((α + 3) * (m - 2 * α) * distillN α * distillD m α))) α := by
  have hm0 : 0 < m := by linarith
  have ht : α + 3 ≠ 0 := by linarith
  have hq : m - 2 * α ≠ 0 := by linarith
  have hn := (distillN_pos hα.le).ne'
  have hD := (distillD_pos hm0 hα.le (by linarith)).ne'
  have hb : 1 - distillNode m α ≠ 0 :=
    (sub_pos.mpr (distillNode_lt_one hm0 hα.le (by linarith))).ne'
  have hC : (m - 1) * (m + 1) * (m + 3) * (m + 5) ≠ 0 := by
    have hm1 : 0 < m - 1 := by linarith
    positivity
  have hfrac := hasDerivAt_reciprocal_quartic (A := 96 * (3 / 5) ^ 4)
    (hasDerivAt_distillNode hm0 hα.le) hC hb
  have hs₀ : 4 * (distillRp m α / (50 * m * (α + 3) ^ 4)) /
      (1 - distillNode m α) = 4 * distillRp m α / ((α + 3) * distillD m α) := by
    rw [distillD_eq hm0 hα.le]
    field_simp [ht, hb, hm0.ne']
  rw [hs₀] at hfrac
  have hs : distillK m α / ((α + 3) * (m - 2 * α) * distillN α) +
      4 * distillRp m α / ((α + 3) * distillD m α) =
      distillCritical0 m α / ((α + 3) * (m - 2 * α) * distillN α * distillD m α) := by
    rw [distillCritical0_eq]
    generalize hq' : m - 2 * α = q at hq ⊢
    field_simp [ht, hq, hn, hD]
  have hd := hasDerivAt_mul_slope (hasDerivAt_distillKappa hα.le hαm) hfrac
  rw [hs] at hd
  exact hd

lemma distillT0_denom_pos {m α : ℝ} (hm : 5 ≤ m) (hα : 0 < α) (hαm : 2 * α < m) :
    0 < (α + 3) * (m - 2 * α) * distillN α * distillD m α := by
  have hq : 0 < m - 2 * α := by linarith
  have hn := distillN_pos hα.le
  have hd := distillD_pos (by linarith : 0 < m) hα.le (by linarith)
  positivity

lemma distillT1_denom_pos {m α : ℝ} (hm : 5 ≤ m) (hα : 0 < α) (hαm : 2 * α < m) :
    0 < 2 * (α + 3) * (m - 2 * α) * distillN α * distillB m α := by
  have hq : 0 < m - 2 * α := by linarith
  have hn := distillN_pos hα.le
  have hb := distillB_pos (by linarith : 0 < m) hα.le
  positivity

lemma distillT2_denom_pos {m α : ℝ} (_hm : 5 ≤ m) (hα : 0 < α) (hαm : 2 * α < m) :
    0 < 2 * α * (α + 3) * (m - 2 * α) * distillN α := by
  have hq : 0 < m - 2 * α := by linarith
  have hn := distillN_pos hα.le
  positivity

lemma distillT0_deriv_nonneg_iff {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hαm : 2 * α < m) :
    0 ≤ deriv (distillT0 m) α ↔ 0 ≤ distillCritical0 m α := by
  rw [(hasDerivAt_distillT0 hm hα hαm).deriv]
  have ht := distillT0_pos hm hα.le hαm
  have hd := distillT0_denom_pos hm hα hαm
  rw [mul_nonneg_iff_of_pos_left ht, le_div_iff₀ hd, zero_mul]

lemma distillT0_deriv_nonneg {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hαm : 2 * α < m) (hp : 0 ≤ distillCritical0 m α) :
    0 ≤ deriv (distillT0 m) α :=
  (distillT0_deriv_nonneg_iff hm hα hαm).mpr hp

lemma distillT0_deriv_nonpos_iff {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hαm : 2 * α < m) :
    deriv (distillT0 m) α ≤ 0 ↔ distillCritical0 m α ≤ 0 := by
  rw [(hasDerivAt_distillT0 hm hα hαm).deriv]
  have ht := distillT0_pos hm hα.le hαm
  have hd := distillT0_denom_pos hm hα hαm
  nth_rw 1 [← mul_zero (distillT0 m α)]
  rw [mul_le_mul_iff_right₀ ht, div_le_iff₀ hd, zero_mul]

lemma distillT0_deriv_nonpos {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hαm : 2 * α < m) (hp : distillCritical0 m α ≤ 0) :
    deriv (distillT0 m) α ≤ 0 :=
  (distillT0_deriv_nonpos_iff hm hα hαm).mpr hp

lemma distillT1_deriv_nonneg_iff {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hαm : 2 * α < m) :
    0 ≤ deriv (distillT1 m) α ↔ distillCritical1 m α ≤ 0 := by
  rw [(hasDerivAt_distillT1 hm hα hαm).deriv]
  have ht := distillT1_pos hm hα.le hαm
  have hd := distillT1_denom_pos hm hα hαm
  rw [mul_nonneg_iff_of_pos_left ht, le_div_iff₀ hd, zero_mul]
  exact neg_nonneg

lemma distillT1_deriv_nonneg {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hαm : 2 * α < m) (hp : distillCritical1 m α ≤ 0) :
    0 ≤ deriv (distillT1 m) α :=
  (distillT1_deriv_nonneg_iff hm hα hαm).mpr hp

lemma distillT1_deriv_nonpos_iff {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hαm : 2 * α < m) :
    deriv (distillT1 m) α ≤ 0 ↔ 0 ≤ distillCritical1 m α := by
  rw [(hasDerivAt_distillT1 hm hα hαm).deriv]
  have ht := distillT1_pos hm hα.le hαm
  have hd := distillT1_denom_pos hm hα hαm
  nth_rw 1 [← mul_zero (distillT1 m α)]
  rw [mul_le_mul_iff_right₀ ht, div_le_iff₀ hd, zero_mul, neg_nonpos]

lemma distillT1_deriv_nonpos {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hαm : 2 * α < m) (hp : 0 ≤ distillCritical1 m α) :
    deriv (distillT1 m) α ≤ 0 :=
  (distillT1_deriv_nonpos_iff hm hα hαm).mpr hp

lemma distillT2_deriv_nonneg_iff {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hαm : 2 * α < m) :
    0 ≤ deriv (distillT2 m) α ↔ distillCritical2 m α ≤ 0 := by
  rw [(hasDerivAt_distillT2 hm hα hαm).deriv]
  have ht := distillT2_pos hm hα hαm
  have hd := distillT2_denom_pos hm hα hαm
  rw [mul_nonneg_iff_of_pos_left ht, le_div_iff₀ hd, zero_mul]
  exact neg_nonneg

lemma distillT2_deriv_nonneg {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hαm : 2 * α < m) (hp : distillCritical2 m α ≤ 0) :
    0 ≤ deriv (distillT2 m) α :=
  (distillT2_deriv_nonneg_iff hm hα hαm).mpr hp

lemma distillT2_deriv_nonpos_iff {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hαm : 2 * α < m) :
    deriv (distillT2 m) α ≤ 0 ↔ 0 ≤ distillCritical2 m α := by
  rw [(hasDerivAt_distillT2 hm hα hαm).deriv]
  have ht := distillT2_pos hm hα hαm
  have hd := distillT2_denom_pos hm hα hαm
  nth_rw 1 [← mul_zero (distillT2 m α)]
  rw [mul_le_mul_iff_right₀ ht, div_le_iff₀ hd, zero_mul, neg_nonpos]

lemma distillT2_deriv_nonpos {m α : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hαm : 2 * α < m) (hp : 0 ≤ distillCritical2 m α) :
    deriv (distillT2 m) α ≤ 0 :=
  (distillT2_deriv_nonpos_iff hm hα hαm).mpr hp

end Sendov
