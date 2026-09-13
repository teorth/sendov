import Sendov.Common.DistillationEnvelope

/-!
# Regularized distillation factors

Adaptation of Senjian An (SJanPerth), *Proof Distillation for Sendov's Conjecture*,
revision e8ae601491ec171ab4f7f8456113dd6a047aa85d, Lemma 4.1 and (5.1).
Paper: CC BY 4.0, https://creativecommons.org/licenses/by/4.0/ .
These are new Lean proofs, not imported numerical certificates. The raw scalar
obstruction at zero is not its continuous extension; positive-alpha hypotheses
on the elementary and scalar bridges are intentional.
-/

namespace Sendov

noncomputable def distillRatio (α : ℝ) : ℝ :=
  (1 - α / (α + 3)) * (1 - (α / (α + 3)) ^ 2 / 30) / 3

noncomputable def distillKappa (m α : ℝ) : ℝ :=
  (m ^ 2 - 1) / (4 * m) * distillRatio α * (m - 2 * α) ^ 2

noncomputable def distillNode (m α : ℝ) : ℝ :=
  4 / 25 + 3 / 5 * cubicPolarEnvelope α + 12 * α / (25 * m)

noncomputable def distillEBudget (m : ℝ) : ℝ := 1 / 4 + 7 / (12 * m)

noncomputable def distillT0 (m α : ℝ) : ℝ :=
  distillKappa m α * (96 * (3 / 5) ^ 4 /
    ((m - 1) * (m + 1) * (m + 3) * (m + 5) * (1 - distillNode m α) ^ 4))

noncomputable def distillT1 (m α : ℝ) : ℝ :=
  (259 / 3125) * distillKappa m α * distillNode m α ^ ((m - 3) / 2)

noncomputable def distillT2 (m α : ℝ) : ℝ :=
  (421 / 3125) * distillKappa m α * cubicPolarEnvelope α ^ ((m - 3) / 2)

@[simp] lemma distillRatio_zero : distillRatio 0 = 1 / 3 := by
  norm_num [distillRatio]

lemma distillRatio_eq {α : ℝ} (hα : 0 < α) :
    distillRatio α = cubicPolarEnvelope α / α := by
  unfold distillRatio cubicPolarEnvelope
  field_simp
  ring

lemma distillRatio_nonneg {α : ℝ} (hα : 0 ≤ α) : 0 ≤ distillRatio α := by
  have hd : 0 < α + 3 := by linarith
  have hu : 0 ≤ α / (α + 3) := div_nonneg hα hd.le
  have hu1 : α / (α + 3) ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hu2 := pow_le_pow_left₀ hu hu1 2
  unfold distillRatio
  exact div_nonneg (mul_nonneg (by linarith)
    (by simp only [one_pow] at hu2; linarith)) (by norm_num)

lemma distillRatio_antitone {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) :
    distillRatio β ≤ distillRatio α := by
  have hβ : 0 ≤ β := hα.trans hαβ
  have hdα : 0 < α + 3 := by linarith
  have hdβ : 0 < β + 3 := by linarith
  have hu : 0 ≤ α / (α + 3) := div_nonneg hα hdα.le
  have hv : 0 ≤ β / (β + 3) := div_nonneg hβ hdβ.le
  have hv1 : β / (β + 3) ≤ 1 := (div_le_one hdβ).mpr (by linarith)
  have huv : α / (α + 3) ≤ β / (β + 3) := by
    rw [div_le_div_iff₀ hdα hdβ]
    nlinarith
  have hu2 := pow_le_pow_left₀ hu huv 2
  have hv2 := pow_le_pow_left₀ hv hv1 2
  unfold distillRatio
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul (by linarith) (by linarith) (by simp only [one_pow] at hv2; linarith)
  linarith

lemma distillKappa_nonneg {m α : ℝ} (hm : 5 ≤ m) (hα : 0 ≤ α) :
    0 ≤ distillKappa m α := by
  unfold distillKappa
  exact mul_nonneg (mul_nonneg (div_nonneg (by nlinarith) (by linarith))
    (distillRatio_nonneg hα)) (sq_nonneg _)

lemma distillKappa_antitone {m α β : ℝ} (hm : 5 ≤ m)
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ m / 2) :
    distillKappa m β ≤ distillKappa m α := by
  have hc : 0 ≤ (m ^ 2 - 1) / (4 * m) :=
    div_nonneg (by nlinarith) (by linarith)
  have hsq : (m - 2 * β) ^ 2 ≤ (m - 2 * α) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  exact mul_le_mul (mul_le_mul_of_nonneg_left (distillRatio_antitone hα hαβ) hc)
    hsq (sq_nonneg _) (mul_nonneg hc (distillRatio_nonneg hα))

lemma distillNode_eq (m α : ℝ) :
    distillNode m α = polarKernel m α (cubicPolarEnvelope α) (3 / 5) :=
  (cubicPolarEnvelope_node m α).symm

lemma distillNode_pos {m α : ℝ} (hm : 0 < m) (hα : 0 ≤ α) :
    0 < distillNode m α := by
  have he := cubicPolarEnvelope_nonneg hα
  have ht : 0 ≤ 12 * α / (25 * m) := div_nonneg (by positivity) (by positivity)
  unfold distillNode
  linarith

lemma distillNode_lt_one {m α : ℝ} (hm : 0 < m) (hα : 0 ≤ α)
    (hαm : α ≤ m / 2) : distillNode m α < 1 := by
  have he := cubicPolarEnvelope_lt_one hα
  have ht : 12 * α / (25 * m) ≤ 6 / 25 := by
    apply (div_le_iff₀ (by positivity : 0 < 25 * m)).mpr
    linarith
  unfold distillNode
  linarith

lemma distillNode_mono {m α β : ℝ} (hm : 0 < m) (hα : 0 ≤ α)
    (hαβ : α ≤ β) : distillNode m α ≤ distillNode m β := by
  rw [distillNode_eq, distillNode_eq]
  exact cubicPolarKernel_mono_alpha hm hα hαβ (by norm_num)

/-- The elementary part of the raw obstruction, only at positive alpha. -/
lemma distillElementary_le_budget {m α : ℝ} (hm : 0 < m) (hα : 0 < α) :
    cubicPolarEnvelope α / (2 * α * (1 - cubicPolarEnvelope α)) +
      cubicPolarEnvelope α / (4 * α) + 1 / (2 * m) +
      cubicPolarEnvelope α / (4 * α * m) ≤ distillEBudget m := by
  have he := cubicPolarEnvelope_le_linear hα.le
  have he1 := cubicPolarEnvelope_lt_one hα.le
  have her : cubicPolarEnvelope α ≤ α / 3 := by
    have hr := distillRatio_antitone (le_refl 0) hα.le
    rw [distillRatio_zero, distillRatio_eq hα] at hr
    exact (div_le_iff₀ hα).mp hr |>.trans_eq (by ring)
  have hfirst : cubicPolarEnvelope α / (2 * α * (1 - cubicPolarEnvelope α)) ≤
      1 / 6 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * α * (1 - cubicPolarEnvelope α))).mpr
    have := (le_div_iff₀ (by linarith : 0 < α + 3)).mp he
    nlinarith
  have hsecond : cubicPolarEnvelope α / (4 * α) ≤ 1 / 12 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * α)).mpr
    linarith
  have hlast : cubicPolarEnvelope α / (4 * α * m) ≤ 1 / (12 * m) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 4 * α * m) (by positivity : 0 < 12 * m)]
    nlinarith [mul_le_mul_of_nonneg_right her hm.le]
  have hid : (1 : ℝ) / 6 + 1 / 12 + 1 / (2 * m) + 1 / (12 * m) =
      distillEBudget m := by
    unfold distillEBudget
    ring
  linarith

/-- The prefactor is regularized only after cancelling a positive alpha. -/
lemma distillKappa_eq {m α : ℝ} (hα : 0 < α) :
    distillKappa m α =
      cubicPolarEnvelope α * (m ^ 2 - 1) * (m - 2 * α) ^ 2 / (4 * α * m) := by
  rw [distillKappa, distillRatio_eq hα]
  ring

/-- Explicitly record the raw zero endpoint, which is not the continuous extension. -/
@[simp] lemma scalarObstruction_zero (m : ℝ) :
    scalarObstruction m 0 (cubicPolarEnvelope 0) = 1 / (2 * m) := by
  simp [scalarObstruction, cubicPolarEnvelope]

lemma distillT0_mixed {m l α r : ℝ} (hm : 5 ≤ m) (hl : 0 ≤ l)
    (hlα : l ≤ α) (hαr : α ≤ r) (hr : r ≤ m / 2) :
    distillT0 m α ≤ distillKappa m l * (96 * (3 / 5) ^ 4 /
      ((m - 1) * (m + 1) * (m + 3) * (m + 5) * (1 - distillNode m r) ^ 4)) := by
  have hm0 : 0 < m := by linarith
  have hα0 : 0 ≤ α := hl.trans hlα
  have hr0 : 0 ≤ r := hα0.trans hαr
  have hnode := distillNode_mono hm0 hα0 hαr
  have hnoder := distillNode_lt_one hm0 hr0 hr
  have hnodeα := distillNode_lt_one hm0 hα0 (hαr.trans hr)
  have hc : 0 < (m - 1) * (m + 1) * (m + 3) * (m + 5) := by
    have : 0 < m - 1 := by linarith
    positivity
  have hd : (m - 1) * (m + 1) * (m + 3) * (m + 5) *
      (1 - distillNode m r) ^ 4 ≤
      (m - 1) * (m + 1) * (m + 3) * (m + 5) * (1 - distillNode m α) ^ 4 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) 4) hc.le
  have hfrac := div_le_div_of_nonneg_left (by positivity : 0 ≤ 96 * (3 / 5 : ℝ) ^ 4)
    (by positivity : 0 < (m - 1) * (m + 1) * (m + 3) * (m + 5) *
      (1 - distillNode m r) ^ 4) hd
  exact mul_le_mul (distillKappa_antitone hm hl hlα (hαr.trans hr)) hfrac
    (by positivity) (distillKappa_nonneg hm hl)

lemma distillT1_mixed {m l α r : ℝ} (hm : 5 ≤ m) (hl : 0 ≤ l)
    (hlα : l ≤ α) (hαr : α ≤ r) (hr : r ≤ m / 2) :
    distillT1 m α ≤ (259 / 3125) * distillKappa m l *
      distillNode m r ^ ((m - 3) / 2) := by
  have hm0 : 0 < m := by linarith
  have hα0 : 0 ≤ α := hl.trans hlα
  have hb := Real.rpow_le_rpow (distillNode_pos hm0 hα0).le
    (distillNode_mono hm0 hα0 hαr) (by linarith : 0 ≤ (m - 3) / 2)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (distillKappa_antitone hm hl hlα (hαr.trans hr))
      (by norm_num)) hb (Real.rpow_nonneg (distillNode_pos hm0 hα0).le _)
    (mul_nonneg (by norm_num) (distillKappa_nonneg hm hl))

lemma distillT2_mixed {m l α r : ℝ} (hm : 5 ≤ m) (hl : 0 ≤ l)
    (hlα : l ≤ α) (hαr : α ≤ r) (hr : r ≤ m / 2) :
    distillT2 m α ≤ (421 / 3125) * distillKappa m l *
      cubicPolarEnvelope r ^ ((m - 3) / 2) := by
  have hα0 : 0 ≤ α := hl.trans hlα
  have hb := Real.rpow_le_rpow (cubicPolarEnvelope_nonneg hα0)
    (cubicPolarEnvelope_mono hα0 hαr) (by linarith : 0 ≤ (m - 3) / 2)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (distillKappa_antitone hm hl hlα (hαr.trans hr))
      (by norm_num)) hb (Real.rpow_nonneg (cubicPolarEnvelope_nonneg hα0) _)
    (mul_nonneg (by norm_num) (distillKappa_nonneg hm hl))

/-- Algebraic assembly for a separately proved two-chord integral bound.
No integral estimate or polar implication is asserted by this interface. -/
lemma distillScalar_le_components {m α : ℝ} (hm : 5 ≤ m) (hα : 0 < α)
    (hJ : (∫ t in (0 : ℝ)..1,
      t ^ 3 * polarKernel m α (cubicPolarEnvelope α) t ^ ((m - 3) / 2)) ≤
      96 * (3 / 5) ^ 4 /
        ((m - 1) * (m + 1) * (m + 3) * (m + 5) * (1 - distillNode m α) ^ 4) +
      (259 / 3125) * distillNode m α ^ ((m - 3) / 2) +
      (421 / 3125) * cubicPolarEnvelope α ^ ((m - 3) / 2)) :
    scalarObstruction m α (cubicPolarEnvelope α) ≤
      distillEBudget m + distillT0 m α + distillT1 m α + distillT2 m α := by
  have hE := distillElementary_le_budget (by linarith : 0 < m) hα
  have hK := mul_le_mul_of_nonneg_left hJ (distillKappa_nonneg hm hα.le)
  unfold scalarObstruction
  rw [← distillKappa_eq hα]
  unfold distillT0 distillT1 distillT2
  nlinarith

end Sendov
