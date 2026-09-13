/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.FiniteRange.Batch

/-!
# From a batch moment and a positive deficit to `R < 1`

The analytic batch bound and the supplied algebraic identity have different jobs.
This interface joins them without expanding the moment polynomial or its certificate.
The lower endpoint needs only `c ≥ 0`, not feasibility; feasibility remains at the
actual degree.  Thus the same contract covers low-degree and large-degree batches.
-/

namespace Sendov

/-- An integer moment at the lower endpoint and a positive deficit certify the whole
batch.  `m₀` and `m₁` allow the caller's exact endpoint numerals in the supplied identity.
No sign assumption on the moment or on the numerator's individual coefficients is needed.
The denominator and the complete deficit must both be strictly positive. -/
theorem R_lt_one_of_batch_certificate {n₀ n n₁ k : ℕ} {α m₀ m₁ I P D : ℝ}
    (h0 : 5 ≤ n₀) (h1 : n₀ ≤ n) (h2 : n ≤ n₁) (hα : 0 ≤ α)
    (hc0 : 0 ≤ c n₀ α) (hfeas : c n α ^ 2 ≤ A n α)
    (hk : ((n₀ : ℝ) - 4) / 2 = (k : ℝ))
    (hM0 : M n₀ = m₀) (hM1 : M n₁ = m₁)
    (hmoment : (∫ t in (0 : ℝ)..1, t ^ 3 * Q n₀ α t ^ k) = I)
    (hcert : 1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * m₀)
      + 1 / (4 * m₀ * (3 + α))
      + (1 - 2 * α / m₁) ^ 2 * n₁ * m₁ * ((n₁ : ℝ) - 2)
        / (4 * (3 + α)) * I = 1 - P / D)
    (hP : 0 < P) (hD : 0 < D) : R n α < 1 := by
  have hb := R_le_batch h0 h1 h2 hα hc0 hfeas
  simp only [hk, Real.rpow_natCast, hmoment, A, hM0, hM1] at hb
  rw [hcert] at hb
  exact hb.trans_lt (sub_lt_self _ (div_pos hP hD))

end Sendov
