/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The integral comparison proof is generalized from Sendov.Common.Chord by Terence Tao.
-/
import Sendov.Common.Quadratic

/-!
# Scalar kernels for the two-chord distillation route

Mathematical source: Senjian An, *Proof Distillation for Sendov's Conjecture*,
revision e8ae601491ec171ab4f7f8456113dd6a047aa85d, equations (2.2), (4.4),
and the parameter comparison in Section 2.4. Paper: CC BY 4.0,
https://creativecommons.org/licenses/by/4.0/ . This is a new Lean formulation,
not a transcription of an upstream formal proof (the upstream has none).

The scalar kernel is nonnegative on the integration interval without the
stronger global feasibility hypothesis. This matters for the enlarged paper
parameter domain used by the scalar comparisons and the two-chord integral bound.
-/

namespace Sendov

open MeasureTheory

/-- Paper kernel, with real degree parameter `m = n - 1`. -/
noncomputable def polarKernel (m α η t : ℝ) : ℝ :=
  (1 - t) ^ 2 + η * t + (2 * α / m) * t * (1 - t)

/-- Exact coordinate map to the pre-existing quadratic. -/
lemma polarKernel_eq_QQ (m α η t : ℝ) :
    polarKernel m α η t = QQ (1 - α / m - η / 2) (1 - 2 * α / m) t := by
  simp only [polarKernel, QQ, div_eq_mul_inv]
  ring

/-- The enlarged scalar domain needs interval positivity, not global feasibility. -/
lemma polarKernel_nonneg {m α η t : ℝ} (hm : 0 ≤ m) (hα : 0 ≤ α)
    (hη : 0 ≤ η) (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ polarKernel m α η t := by
  unfold polarKernel
  exact add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hη ht.1))
    (mul_nonneg (mul_nonneg (div_nonneg (by positivity) hm) ht.1)
      (sub_nonneg.mpr ht.2))

/-- Increasing the endpoint parameter increases the kernel on `[0,1]`. -/
lemma polarKernel_mono_eta {m α η₁ η₂ t : ℝ} (hη : η₁ ≤ η₂) (ht : 0 ≤ t) :
    polarKernel m α η₁ t ≤ polarKernel m α η₂ t := by
  unfold polarKernel
  gcongr

/-- Increasing alpha increases the kernel for fixed endpoint parameter. -/
lemma polarKernel_mono_alpha {m α₁ α₂ η t : ℝ} (hm : 0 < m) (hα : α₁ ≤ α₂)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    polarKernel m α₁ η t ≤ polarKernel m α₂ η t := by
  unfold polarKernel
  gcongr
  · exact sub_nonneg.mpr ht.2
  · exact ht.1

/-- Exact secant gap, valid before imposing any sign hypotheses. -/
lemma QQ_secant_gap (c A l r t : ℝ) (hlr : l ≠ r) :
    ((r - t) * QQ c A l + (t - l) * QQ c A r) / (r - l) - QQ c A t =
      A * (t - l) * (r - t) := by
  have hrl : r - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hlr)
  unfold QQ
  field_simp
  ring

/-- Each secant is an upper bound on its own interval when the quadratic is convex. -/
lemma QQ_le_secant {c A l r t : ℝ} (hA : 0 ≤ A) (hlr : l < r)
    (ht : t ∈ Set.Icc l r) :
    QQ c A t ≤ ((r - t) * QQ c A l + (t - l) * QQ c A r) / (r - l) := by
  have h := QQ_secant_gap c A l r t hlr.ne
  have hn := mul_nonneg (mul_nonneg hA (sub_nonneg.mpr ht.1))
    (sub_nonneg.mpr ht.2)
  linarith

/-- Integral comparison with exactly the positivity needed on the interval.
This generalization serves both actual polynomial data and the enlarged scalar domain. -/
lemma integral_QQ_anti_on {c₁ c₂ A : ℝ} (hle : c₁ ≤ c₂)
    (hQ : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ QQ c₂ A t) {r : ℝ} (hr : 0 ≤ r)
    (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ k * QQ c₂ A t ^ r)
      ≤ ∫ t in (0 : ℝ)..1, t ^ k * QQ c₁ A t ^ r := by
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_pow_mul_QQ c₂ A k hr).intervalIntegrable _ _)
    ((continuous_pow_mul_QQ c₁ A k hr).intervalIntegrable _ _) ?_
  intro t ht
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ht.1 k)
  refine Real.rpow_le_rpow (hQ t ht) ?_ hr
  simp only [QQ]
  nlinarith [ht.1, hle]

/-- Paper parameter monotonicity of the integral, for every nonnegative exponent.
No geometric feasibility is assumed. -/
lemma integral_polarKernel_mono_eta {m α η₁ η₂ r : ℝ} (hm : 0 ≤ m)
    (hα : 0 ≤ α) (hη₁ : 0 ≤ η₁) (hη : η₁ ≤ η₂) (hr : 0 ≤ r) (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ k * polarKernel m α η₁ t ^ r)
      ≤ ∫ t in (0 : ℝ)..1, t ^ k * polarKernel m α η₂ t ^ r := by
  simp only [polarKernel_eq_QQ]
  refine integral_QQ_anti_on (by linarith) ?_ hr k
  intro t ht
  rw [← polarKernel_eq_QQ]
  exact polarKernel_nonneg hm hα hη₁ ht

end Sendov
