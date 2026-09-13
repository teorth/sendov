/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.FiniteRange.PackBridge

/-!
# Numeric conditions for a packed batch moment

The analytic recurrence bounds discharge the true row obligations uniformly.
Each batch still supplies its exact numerator and kernel-checked packed equality.
-/

namespace Sendov

/-- Numeric overflow and length bounds suffice to verify a supplied moment numerator.
The three recurrence multipliers have length at most three, so the true weighted row
has length at most `1 + 3*k`.  Its coefficients and packed row are bounded analytically;
only the supplied numerator and the single packed equality are computed by the caller.
Trailing zeros are permitted, and no recurrence row needs to be expanded. -/
theorem pev_moment_eq_of_packed_bounds (n k : ℕ) (L β τ : ℤ) (Nmom : List ℤ)
    (hL : 0 ≤ L) (hβ : 1 ≤ β) (hτ : 0 < τ)
    (hrow : 2 * ((l1 (gg0 n) + l1 (gg1 n) + l1 (gg2 n)) ^ k
      * β ^ (1 + 3 * k)) < τ)
    (hweight : 2 * (L * (l1 (gg0 n) + l1 (gg1 n) + l1 (gg2 n)) ^ k) < β)
    (hN : ∀ a ∈ Nmom, 2 * |a| < β) (hlen : Nmom.length ≤ 1 + 3 * k)
    (hcheck : wsumZ L 0 (unpackZ τ (2 * k + 1)
      ((pevZ (gg0 n) β + pevZ (gg1 n) β * τ + pevZ (gg2 n) β * τ ^ 2) ^ k))
      = pevZ Nmom β) (α : ℝ) :
    pev Nmom α = pev (wsum L 0 (qrow (gg0 n) (gg1 n) (gg2 n) k)) α := by
  refine pev_wsum_eq_of_packed (gg0 n) (gg1 n) (gg2 n) k (1 + 3 * k)
    L β τ Nmom (by omega) hτ ?_ hN ?_ hlen ?_ ?_ α
  · exact rowZ_bound (gg0 n) (gg1 n) (gg2 n) k 3 β τ hβ
      (by simp) (by simp) (by simp) hrow
  · exact wsum_bound (gg0 n) (gg1 n) (gg2 n) k L β hL hweight
  · exact wsum_length_le L _ 0
      (qrow_entry_length_le (gg0 n) (gg1 n) (gg2 n) 3
        (by simp) (by simp) (by simp) k)
  · simpa only [qrow_length] using hcheck

end Sendov
