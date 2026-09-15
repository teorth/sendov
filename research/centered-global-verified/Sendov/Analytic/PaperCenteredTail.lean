import Sendov.Analytic.PaperCenteredBound

/-! # All-degree centered endpoint cancellation

This removes inverse mean powers before taking norms, for arbitrary complex
means and every finite degree. The resulting integral envelope is conditional
only on nonzero mean; it does not assert the open C-near budget.
-/
noncomputable section
open scoped BigOperators
namespace Sendov.PaperCenteredTail
open PaperCentered PaperCenteredBound

/-- All-degree analogue of top endpoint suppression. No endpoint is dropped. -/
theorem normalized_H_integral (m k : ℕ) (hk : k ≤ m) (a μ : ℂ) (hμ : μ ≠ 0) :
    H m k (a * μ) / ((m.choose k : ℂ) * μ ^ k) =
      ((m + 1 : ℂ) * a ^ (k + 1) * μ) *
        (∫ t in (0 : ℝ)..1, (t : ℂ) ^ k * (1 - a * μ * t) ^ (m - k)) := by
  have hc : (m.choose k : ℂ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hk
  rw [← finite_beta m k hk (a * μ)]
  simp only [mul_pow, pow_succ]
  field_simp

/-- Exact norm identity for the square-root majorant, retaining actual variance. -/
theorem majorant_term_integral (r : Multiset ℂ) (k : ℕ) (hk : k ≤ r.card)
    (a μ : ℂ) (hμ : μ ≠ 0) :
    C r.card k (variance r) / ((r.card.choose k : ℝ) * ‖μ‖ ^ k) *
      ‖H r.card k (a * μ)‖ =
    C r.card k (variance r) * (r.card + 1 : ℝ) * ‖a‖ ^ (k + 1) * ‖μ‖ *
      ‖∫ t in (0 : ℝ)..1, (t : ℂ) ^ k * (1 - a * μ * t) ^ (r.card - k)‖ := by
  have hn := congrArg norm (normalized_H_integral r.card k hk a μ hμ)
  have hcard : ‖(r.card : ℂ) + 1‖ = (r.card : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (r.card + 1)
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast, hcard] at hn
  calc
    _ = C r.card k (variance r) *
        (‖H r.card k (a * μ)‖ / ((r.card.choose k : ℝ) * ‖μ‖ ^ k)) := by ring
    _ = _ := by rw [hn]; ring

/-- A finite, complex-mean-safe H envelope without inverse powers of the mean.
The absolute value of real t avoids imposing a global sign off the interval. -/
theorem majorant_term_le_integral (r : Multiset ℂ) (k : ℕ) (hk : k ≤ r.card)
    (a μ : ℂ) (hμ : μ ≠ 0) :
    C r.card k (variance r) / ((r.card.choose k : ℝ) * ‖μ‖ ^ k) *
      ‖H r.card k (a * μ)‖ ≤
    C r.card k (variance r) * (r.card + 1 : ℝ) * ‖a‖ ^ (k + 1) * ‖μ‖ *
      (∫ t in (0 : ℝ)..1, |t| ^ k * ‖1 - a * μ * t‖ ^ (r.card - k)) := by
  rw [majorant_term_integral r k hk a μ hμ]
  apply mul_le_mul_of_nonneg_left _ (by positivity [C_nonneg r.card k (variance r)])
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] using
    (intervalIntegral.norm_integral_le_integral_norm
      (f := fun t : ℝ => (t : ℂ) ^ k * (1 - a * μ * t) ^ (r.card - k))
      (by norm_num : (0 : ℝ) ≤ 1))

/-- Every high-degree block inherits the same finite integral envelope.
This is a structural estimate, not a per-degree numerical certificate table. -/
theorem majorant_block_le_integral (r : Multiset ℂ) (K : ℕ)
    (a μ : ℂ) (hμ : μ ≠ 0) :
    (∑ k ∈ Finset.Ico K (r.card + 1),
      C r.card k (variance r) / ((r.card.choose k : ℝ) * ‖μ‖ ^ k) *
        ‖H r.card k (a * μ)‖) ≤
    ∑ k ∈ Finset.Ico K (r.card + 1),
      C r.card k (variance r) * (r.card + 1 : ℝ) * ‖a‖ ^ (k + 1) * ‖μ‖ *
        (∫ t in (0 : ℝ)..1, |t| ^ k * ‖1 - a * μ * t‖ ^ (r.card - k)) := by
  apply Finset.sum_le_sum
  intro k hk
  exact majorant_term_le_integral r k (by have := (Finset.mem_Ico.mp hk).2; omega) a μ hμ

end Sendov.PaperCenteredTail
