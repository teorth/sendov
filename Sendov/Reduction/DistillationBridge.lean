import Sendov.Common.DistillationEnvelope
import Sendov.Reduction.Simplified

/-!
# Actual scalar data and the distillation obstruction

New Lean proofs of the coordinate change and eta comparison in Section 2 of
Senjian An, *Proof Distillation for Sendov's Conjecture*, revision
`e8ae601491ec171ab4f7f8456113dd6a047aa85d` (paper CC BY 4.0,
https://creativecommons.org/licenses/by/4.0/).

The actual-data equality uses the existing `A_eq_sq` and `mul_eq_c` interfaces.
The origin wrapper converts `one_le_of_origin` directly into the scalar obstruction.
The polar wrapper uses the weak input `1 ≤ integral` to obtain eta < 1.
The strict cubic envelope and finite closure are established in downstream modules.
-/

namespace Sendov

open MeasureTheory

/-- Nonnegativity of the weighted integral on the enlarged scalar domain. -/
lemma integral_polarKernel_nonneg {m α η r : ℝ} (hm : 0 ≤ m)
    (hα : 0 ≤ α) (hη : 0 ≤ η) (k : ℕ) :
    0 ≤ ∫ t in (0 : ℝ)..1, t ^ k * polarKernel m α η t ^ r := by
  refine intervalIntegral.integral_nonneg (by norm_num) ?_
  intro t ht
  exact mul_nonneg (pow_nonneg ht.1 k)
    (Real.rpow_nonneg (polarKernel_nonneg hm hα hη ht) r)

/-- The squared factor stays nonnegative, including at alpha = m/2. -/
lemma scalarObstruction_prefactor_nonneg {m α η : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hη : 0 ≤ η) :
    0 ≤ η * (m ^ 2 - 1) * (m - 2 * α) ^ 2 / (4 * α * m) := by
  have hm0 : 0 ≤ m := by linarith
  have hm2 : 0 ≤ m ^ 2 - 1 := by nlinarith
  positivity

/-- The full obstruction increases with eta. Both the coefficient and the
integral are compared, with their signs proved, not presumed from the formula. -/
lemma scalarObstruction_mono_eta {m α η₁ η₂ : ℝ} (hm : 5 ≤ m)
    (hα : 0 < α) (hη₁ : 0 ≤ η₁) (hη : η₁ ≤ η₂) (hη₂ : η₂ < 1) :
    scalarObstruction m α η₁ ≤ scalarObstruction m α η₂ := by
  have hm0 : 0 ≤ m := by linarith
  have hm2 : 0 ≤ m ^ 2 - 1 := by nlinarith
  have hη₂0 : 0 ≤ η₂ := hη₁.trans hη
  have hr : 0 ≤ (m - 3) / 2 := by linarith
  have hd₁ : 0 < 2 * α * (1 - η₁) :=
    mul_pos (by positivity) (by linarith)
  have hd₂ : 0 < 2 * α * (1 - η₂) :=
    mul_pos (by positivity) (by linarith)
  have he₁ : η₁ / (2 * α * (1 - η₁)) ≤ η₂ / (2 * α * (1 - η₂)) := by
    rw [div_le_div_iff₀ hd₁ hd₂]
    nlinarith [mul_nonneg hα.le (sub_nonneg.mpr hη)]
  have he₂ : η₁ / (4 * α) ≤ η₂ / (4 * α) :=
    div_le_div_of_nonneg_right hη (by positivity)
  have he₄ : η₁ / (4 * α * m) ≤ η₂ / (4 * α * m) :=
    div_le_div_of_nonneg_right hη (by positivity)
  have hk : η₁ * (m ^ 2 - 1) * (m - 2 * α) ^ 2 / (4 * α * m) ≤
      η₂ * (m ^ 2 - 1) * (m - 2 * α) ^ 2 / (4 * α * m) := by
    gcongr
  have hi := integral_polarKernel_mono_eta hm0 hα.le hη₁ hη hr 3
  have hi0 := integral_polarKernel_nonneg (r := (m - 3) / 2) hm0 hα.le hη₁ 3
  have hk0 := scalarObstruction_prefactor_nonneg hm hα hη₂0
  have hlast := mul_le_mul hk hi hi0 hk0
  unfold scalarObstruction
  linarith

/-- Exact actual-data coordinates; no polar or origin inequality is required. -/
lemma polarKernel_actual {n : ℕ} {a x α : ℝ} (hn : 2 ≤ n)
    (hα : α = M n * (1 - a ^ 2) / 2) (t : ℝ) :
    polarKernel (M n) α (QQ (a * x) (a ^ 2) 1) t = QQ (a * x) (a ^ 2) t := by
  rw [polarKernel_eq_QQ]
  have hc := mul_eq_c (x := x) hn hα
  have hA := A_eq_sq hn hα
  change 1 - 2 * α / M n = a ^ 2 at hA
  rw [hA, show 1 - α / M n - QQ (a * x) (a ^ 2) 1 / 2 = a * x by linarith]

/-- The raw RHS of `(1le)` is exactly H at actual eta, not H at the old envelope. -/
lemma scalarObstruction_actual_eq {n : ℕ} {a x α : ℝ} (hn : 2 ≤ n)
    (hα : α = M n * (1 - a ^ 2) / 2) :
    scalarObstruction (M n) α (QQ (a * x) (a ^ 2) 1) =
      QQ (a * x) (a ^ 2) 1 / (2 * α * (1 - QQ (a * x) (a ^ 2) 1))
      + QQ (a * x) (a ^ 2) 1 / (4 * α) + 1 / (2 * M n)
      + QQ (a * x) (a ^ 2) 1 / (4 * α * M n)
      + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * QQ (a * x) (a ^ 2) 1 / (4 * α)
        * ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by
  have hm : M n ≠ 0 := (M_pos hn).ne'
  have hA := A_eq_sq hn hα
  have hs : M n - 2 * α = M n * a ^ 2 := by
    change 1 - 2 * α / M n = a ^ 2 at hA
    field_simp at hA
    nlinarith [hA]
  have hk : QQ (a * x) (a ^ 2) 1 * (M n ^ 2 - 1) * (M n - 2 * α) ^ 2 /
      (4 * α * M n) =
      (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * QQ (a * x) (a ^ 2) 1 / (4 * α) := by
    rw [hs]
    by_cases ha0 : α = 0
    · simp [ha0]
    · field_simp
      unfold M
      ring
  have hi : (∫ t in (0 : ℝ)..1,
      t ^ 3 * polarKernel (M n) α (QQ (a * x) (a ^ 2) 1) t ^ ((M n - 3) / 2)) =
      ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp only
    rw [polarKernel_actual hn hα]
    congr 2
    unfold M
    ring
  unfold scalarObstruction
  rw [hk, hi]

/-- Direct `(1le)` bridge. The sole analytic input is the original weak inequality. -/
theorem one_le_scalarObstruction_of_one_le {n : ℕ} {a x α : ℝ} (hn : 2 ≤ n)
    (hα : α = M n * (1 - a ^ 2) / 2)
    (h1le : 1 ≤ QQ (a * x) (a ^ 2) 1 / (2 * α * (1 - QQ (a * x) (a ^ 2) 1))
      + QQ (a * x) (a ^ 2) 1 / (4 * α) + 1 / (2 * M n)
      + QQ (a * x) (a ^ 2) 1 / (4 * α * M n)
      + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * QQ (a * x) (a ^ 2) 1 / (4 * α)
        * ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2)) :
    1 ≤ scalarObstruction (M n) α (QQ (a * x) (a ^ 2) 1) := by
  rw [scalarObstruction_actual_eq hn hα]
  exact h1le

/-- Consume the existing raw origin reduction, before the old R enlargement. -/
theorem one_le_scalarObstruction_of_origin {n : ℕ} (hn : 5 ≤ n) {a x α : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2) (hη : QQ (a * x) (a ^ 2) 1 < 1)
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1,
        t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :
    1 ≤ scalarObstruction (M n) α (QQ (a * x) (a ^ 2) 1) := by
  have hn2 : 2 ≤ n := by omega
  have hα0 := alpha_pos hn2 ha1 ha.le hα
  exact one_le_scalarObstruction_of_one_le hn2 hα
    (one_le_of_origin hn ha ha1 hx hα hα0 hη horigin)

/-- The OLD polar upper bound already puts actual eta in the monotonicity domain.
The polar premise is `1 ≤ integral`, not the paper's strict inequality. -/
lemma actualEta_mem_Ico_of_polar {n : ℕ} (hn : 2 ≤ n) {a x α : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2)) :
    QQ (a * x) (a ^ 2) 1 ∈ Set.Ico (0 : ℝ) 1 := by
  have hα0 := alpha_pos hn ha1 ha hα
  have hf : (a * x) ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a]
  have hη0 := QQ_nonneg hf 1
  have hb := beta_le hα0 hη0 (polar_exp hn hx hα hpolar)
  refine ⟨hη0, hb.trans_lt ?_⟩
  exact (div_lt_one (by linarith : 0 < 3 + α)).mpr (by linarith)

/-- Actual old-parameter wrapper: neither eta < 1 nor `(1le)` is left as an
extra premise. These follow from the original weak polar and origin inputs. -/
theorem one_le_scalarObstruction_of_polar_origin {n : ℕ} (hn : 5 ≤ n) {a x α : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2))
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1,
        t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :
    1 ≤ scalarObstruction (M n) α (QQ (a * x) (a ^ 2) 1) := by
  have hn2 : 2 ≤ n := by omega
  exact one_le_scalarObstruction_of_origin hn ha ha1 hx hα
    (actualEta_mem_Ico_of_polar hn2 ha.le ha1 hx hα hpolar).2 horigin

end Sendov
