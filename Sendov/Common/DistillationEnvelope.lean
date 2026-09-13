import Sendov.Common.DistillationKernel

/-!
# Rational envelope ingredients and exact scalar coordinates

New Lean proofs of the algebraic/monotone portion of Senjian An's paper,
revision e8ae601491ec171ab4f7f8456113dd6a047aa85d, Sections 2--4.
Paper licensed CC BY 4.0: https://creativecommons.org/licenses/by/4.0/ .
No theorem here asserts that the polar constraint implies the cubic envelope:
that requires the stronger hyperbolic comparison in Appendix A.
-/

namespace Sendov

open MeasureTheory

/-- The cubic correction is in `u = α / (α + 3)`, not in alpha itself. -/
noncomputable def cubicPolarEnvelope (α : ℝ) : ℝ :=
  let u := α / (α + 3)
  u - u ^ 3 / 30

lemma cubicPolarEnvelope_nonneg {α : ℝ} (hα : 0 ≤ α) :
    0 ≤ cubicPolarEnvelope α := by
  have hd : 0 < α + 3 := by linarith
  have hu : 0 ≤ α / (α + 3) := div_nonneg hα hd.le
  have hu1 : α / (α + 3) ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hu3 : (α / (α + 3)) ^ 3 ≤ α / (α + 3) :=
    pow_le_of_le_one hu hu1 (by decide)
  unfold cubicPolarEnvelope
  exact sub_nonneg.mpr ((div_le_self (pow_nonneg hu 3) (by norm_num)).trans hu3)

lemma cubicPolarEnvelope_le_linear {α : ℝ} (hα : 0 ≤ α) :
    cubicPolarEnvelope α ≤ α / (α + 3) := by
  have hu : 0 ≤ α / (α + 3) := div_nonneg hα (by linarith)
  unfold cubicPolarEnvelope
  exact sub_le_self _ (div_nonneg (pow_nonneg hu 3) (by norm_num))

lemma cubicPolarEnvelope_lt_one {α : ℝ} (hα : 0 ≤ α) :
    cubicPolarEnvelope α < 1 := by
  refine (cubicPolarEnvelope_le_linear hα).trans_lt ?_
  exact (div_lt_one (by linarith : 0 < α + 3)).mpr (by linarith)

/-- Monotonicity without differentiating a rational function. -/
lemma cubicPolarEnvelope_mono {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) :
    cubicPolarEnvelope α ≤ cubicPolarEnvelope β := by
  have hβ : 0 ≤ β := hα.trans hαβ
  have hdα : 0 < α + 3 := by linarith
  have hdβ : 0 < β + 3 := by linarith
  set u := α / (α + 3) with hu
  set v := β / (β + 3) with hv
  have hu0 : 0 ≤ u := div_nonneg hα hdα.le
  have hv0 : 0 ≤ v := div_nonneg hβ hdβ.le
  have hu1 : u ≤ 1 := (div_le_one hdα).mpr (by linarith)
  have hv1 : v ≤ 1 := (div_le_one hdβ).mpr (by linarith)
  have huv : u ≤ v := by
    dsimp [u, v]
    rw [div_le_div_iff₀ hdα hdβ]
    nlinarith
  have hu2 : u ^ 2 ≤ 1 := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  have hv2 : v ^ 2 ≤ 1 := by nlinarith [mul_nonneg hv0 (sub_nonneg.mpr hv1)]
  have huv1 : u * v ≤ 1 := mul_le_one₀ hu1 hv0 hv1
  have hfactor : 0 ≤ 1 - (v ^ 2 + v * u + u ^ 2) / 30 := by nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr huv) hfactor
  change u - u ^ 3 / 30 ≤ v - v ^ 3 / 30
  nlinarith [hprod]

/-- The paper's exact chord node. -/
lemma cubicPolarEnvelope_node (m α : ℝ) :
    polarKernel m α (cubicPolarEnvelope α) (3 / 5) =
      4 / 25 + 3 / 5 * cubicPolarEnvelope α + 12 * α / (25 * m) := by
  unfold polarKernel
  ring

/-- A real consumer of envelope monotonicity in the enlarged parameter domain. -/
lemma cubicPolarKernel_mono_alpha {m α β t : ℝ} (hm : 0 < m)
    (hα : 0 ≤ α) (hαβ : α ≤ β) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    polarKernel m α (cubicPolarEnvelope α) t ≤
      polarKernel m β (cubicPolarEnvelope β) t := by
  exact (polarKernel_mono_alpha hm hαβ ht).trans
    (polarKernel_mono_eta (cubicPolarEnvelope_mono hα hαβ) ht.1)

/-- The paper's `H_m(α;η)` at positive alpha. At zero this raw formula is NOT its
continuous extension: real division is total in Lean. -/
noncomputable def scalarObstruction (m α η : ℝ) : ℝ :=
  η / (2 * α * (1 - η)) + η / (4 * α) + 1 / (2 * m) + η / (4 * α * m) +
    η * (m ^ 2 - 1) * (m - 2 * α) ^ 2 / (4 * α * m) *
      ∫ t in (0 : ℝ)..1, t ^ 3 * polarKernel m α η t ^ ((m - 3) / 2)

end Sendov
