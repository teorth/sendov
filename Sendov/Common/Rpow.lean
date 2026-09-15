/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.Common.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Real powers and integration

The zero-to-one real-power integral and continuity lemma support the linear and cubic Beta
integrals and the actual quadratic kernel.
-/

namespace Sendov

open MeasureTheory

/-- `∫₀¹ xˢ dx = 1/(s+1)` for `s > -1`. -/
lemma integral_rpow_zero_one {s : ℝ} (hs : -1 < s) :
    (∫ x in (0 : ℝ)..1, x ^ s) = 1 / (s + 1) := by
  rw [integral_rpow (Or.inl hs), Real.one_rpow, Real.zero_rpow (by linarith)]
  ring

/-- `fun x ↦ x ^ e` is continuous on all of `ℝ` for a nonnegative real exponent `e`.  The
exponent must be nonnegative: at `e < 0` the function blows up at the origin. -/
lemma continuous_rpow_const {e : ℝ} (he : 0 ≤ e) : Continuous fun x : ℝ => x ^ e :=
  Real.continuous_rpow_const he

end Sendov
