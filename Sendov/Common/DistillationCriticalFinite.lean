import Sendov.Common.DistillationCritical
import Sendov.Common.DistillationMajorant
import Sendov.Common.BernsteinCert
import Sendov.Common.BernsteinRing
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Finite critical-bracket bounds

Critical polynomials and fixed budgets from Senjian An, *Proof Distillation for
Sendov's Conjecture*, e8ae601491ec171ab4f7f8456113dd6a047aa85d (paper CC BY 4.0).
New Lean proofs, Apache-2.0 as the baseline. The interval outside the bracket is
controlled analytically; only the bracket uses the mixed factor estimate.
-/
namespace Sendov

/-- Two monotone flanks and a bounded central bracket cover the exact closed domain.
Degenerate flanks are allowed: their derivative hypotheses have empty open domains. -/
lemma distillPeak_le {f : ℝ → ℝ} {d l r b x : ℝ}
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ d)
    (hc : ContinuousOn f (Set.Icc 0 d))
    (hd : ∀ x ∈ Set.Ioo 0 d, DifferentiableAt ℝ f x)
    (hp : ∀ x ∈ Set.Ioo 0 l, 0 ≤ deriv f x)
    (hn : ∀ x ∈ Set.Ioo r d, deriv f x ≤ 0)
    (hb : ∀ x ∈ Set.Icc l r, f x ≤ b) (hx : x ∈ Set.Icc 0 d) : f x ≤ b := by
  have hld : l ≤ d := hlr.trans hr
  have hr0 : 0 ≤ r := hl.trans hlr
  have hleft : MonotoneOn f (Set.Icc 0 l) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (hc.mono (Set.Icc_subset_Icc le_rfl hld))
    · rw [interior_Icc]
      intro y hy
      exact (hd y ⟨hy.1, hy.2.trans_le hld⟩).differentiableWithinAt
    · simpa only [interior_Icc] using hp
  have hright : AntitoneOn f (Set.Icc r d) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (hc.mono (Set.Icc_subset_Icc hr0 le_rfl))
    · rw [interior_Icc]
      intro y hy
      exact (hd y ⟨hr0.trans_lt hy.1, hy.2⟩).differentiableWithinAt
    · simpa only [interior_Icc] using hn
  by_cases hxl : x ≤ l
  · exact (hleft ⟨hx.1, hxl⟩ ⟨hl, le_rfl⟩ hxl).trans (hb l ⟨le_rfl, hlr⟩)
  by_cases hxr : x ≤ r
  · exact hb x ⟨le_of_not_ge hxl, hxr⟩
  · have hrx : r ≤ x := le_of_not_ge hxr
    exact (hright ⟨le_rfl, hr⟩ ⟨hrx, hx.2⟩ hrx).trans (hb r ⟨hlr, le_rfl⟩)

/-- Squaring half-integer powers is exact, also at zero. -/
lemma distillRpow_half_sq {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    (b ^ ((n : ℝ) / 2)) ^ 2 = b ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
  norm_num

lemma distillMulRpow_le_of_sq {a b c m : ℝ} (n : ℕ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hn : (m - 3) / 2 = (n : ℝ) / 2)
    (hsq : a ^ 2 * b ^ n ≤ c ^ 2) : a * b ^ ((m - 3) / 2) ≤ c := by
  have hid : (a * b ^ ((m - 3) / 2)) ^ 2 = a ^ 2 * b ^ n := by
    rw [mul_pow, hn, distillRpow_half_sq hb]
  nlinarith [sq_nonneg (a * b ^ ((m - 3) / 2) - c)]

/-- Component 0: exact flanks from the critical derivative API and one mixed bracket. -/
lemma distillT0_le_of_critical {m d l r b α : ℝ}
    (hm : 5 ≤ m) (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ d) (hdm : d ≤ m / 2)
    (hp : ∀ x ∈ Set.Ioo 0 l, 0 ≤ distillCritical0 m x)
    (hq : ∀ x ∈ Set.Ioo r d, 0 ≤ -distillCritical0 m x)
    (hb : distillKappa m l * (96 * (3 / 5) ^ 4 /
      ((m - 1) * (m + 1) * (m + 3) * (m + 5) * (1 - distillNode m r) ^ 4)) ≤ b)
    (hα : α ∈ Set.Icc 0 d) : distillT0 m α ≤ b := by
  apply distillPeak_le hl hlr hr
    ((distillT0_continuousOn hm).mono (Set.Icc_subset_Icc le_rfl hdm))
    (fun x hx ↦ (hasDerivAt_distillT0 hm hx.1 (by have := hx.2; linarith)).differentiableAt)
    ?_ ?_ ?_ hα
  · intro x hx
    apply distillT0_deriv_nonneg hm hx.1 (by have := hx.2; linarith)
    exact hp x hx
  · intro x hx
    apply distillT0_deriv_nonpos hm (by have := hx.1; linarith)
      (by have := hx.2; linarith)
    exact neg_nonneg.mp (hq x hx)
  · intro x hx
    exact (distillT0_mixed hm hl hx.1 hx.2 (hr.trans hdm)).trans hb

/-- Component 1: exact flanks from the critical derivative API and one mixed bracket. -/
lemma distillT1_le_of_critical {m d l r b α : ℝ}
    (n : ℕ) (hb0 : 0 ≤ b) (hn : (m - 3) / 2 = (n : ℝ) / 2)
    (hm : 5 ≤ m) (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ d) (hdm : d ≤ m / 2)
    (hp : ∀ x ∈ Set.Ioo 0 l, 0 ≤ -distillCritical1 m x)
    (hq : ∀ x ∈ Set.Ioo r d, 0 ≤ distillCritical1 m x)
    (hb : ((259 / 3125) * distillKappa m l) ^ 2 * (distillNode m r) ^ n ≤ b ^ 2)
    (hα : α ∈ Set.Icc 0 d) : distillT1 m α ≤ b := by
  apply distillPeak_le hl hlr hr
    ((distillT1_continuousOn hm).mono (Set.Icc_subset_Icc le_rfl hdm))
    (fun x hx ↦ (hasDerivAt_distillT1 hm hx.1 (by have := hx.2; linarith)).differentiableAt)
    ?_ ?_ ?_ hα
  · intro x hx
    apply distillT1_deriv_nonneg hm hx.1 (by have := hx.2; linarith)
    exact neg_nonneg.mp (hp x hx)
  · intro x hx
    apply distillT1_deriv_nonpos hm (by have := hx.1; linarith)
      (by have := hx.2; linarith)
    exact hq x hx
  · intro x hx
    apply (distillT1_mixed hm hl hx.1 hx.2 (hr.trans hdm)).trans
    exact distillMulRpow_le_of_sq n (distillNode_pos (by linarith) (hl.trans hlr)).le hb0 hn hb

/-- Component 2: exact flanks from the critical derivative API and one mixed bracket. -/
lemma distillT2_le_of_critical {m d l r b α : ℝ}
    (n : ℕ) (hb0 : 0 ≤ b) (hn : (m - 3) / 2 = (n : ℝ) / 2)
    (hm : 5 ≤ m) (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ d) (hdm : d ≤ m / 2)
    (hp : ∀ x ∈ Set.Ioo 0 l, 0 ≤ -distillCritical2 m x)
    (hq : ∀ x ∈ Set.Ioo r d, 0 ≤ distillCritical2 m x)
    (hb : ((421 / 3125) * distillKappa m l) ^ 2 * (cubicPolarEnvelope r) ^ n ≤ b ^ 2)
    (hα : α ∈ Set.Icc 0 d) : distillT2 m α ≤ b := by
  apply distillPeak_le hl hlr hr
    ((distillT2_continuousOn hm).mono (Set.Icc_subset_Icc le_rfl hdm))
    (fun x hx ↦ (hasDerivAt_distillT2 hm hx.1 (by have := hx.2; linarith)).differentiableAt)
    ?_ ?_ ?_ hα
  · intro x hx
    apply distillT2_deriv_nonneg hm hx.1 (by have := hx.2; linarith)
    exact neg_nonneg.mp (hp x hx)
  · intro x hx
    apply distillT2_deriv_nonpos hm (by have := hx.1; linarith)
      (by have := hx.2; linarith)
    exact hq x hx
  · intro x hx
    apply (distillT2_mixed hm hl hx.1 hx.2 (hr.trans hdm)).trans
    exact distillMulRpow_le_of_sq n (cubicPolarEnvelope_nonneg (hl.trans hlr)) hb0 hn hb

end Sendov
