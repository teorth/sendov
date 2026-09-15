import Sendov.Common.DistillationFactors

/-!
# Positivity and continuity of the regularized factors

Common mathematics retained from the former critical-polynomial module.
Adapted from Senjian An's *Proof Distillation for Sendov's Conjecture*,
revision e8ae601491ec171ab4f7f8456113dd6a047aa85d (CC BY 4.0).
The raw scalar at zero is still separate from these regularized factors.
-/

namespace Sendov

noncomputable def distillN (α : ℝ) : ℝ := 29 * α ^ 2 + 180 * α + 270

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

lemma distillN_pos {α : ℝ} (hα : 0 ≤ α) : 0 < distillN α := by
  unfold distillN
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

end Sendov
