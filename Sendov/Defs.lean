/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Shared coordinates

`M n = n - 1` and `A n α = 1 - 2α/M n` are the actual degree and squared-radius coordinates.
The selected scalar route uses the actual quadratic and the cubic polar envelope.
-/

namespace Sendov

/-- `M n = n - 1`.  All of the quantities below are naturally expressed in terms of it. -/
noncomputable def M (n : ℕ) : ℝ := (n : ℝ) - 1

/-- `A n α = a ^ 2 = 1 - 2α/(n-1)`, from the definition `α = (n-1)(1-a²)/2` of `α`.
The blog post's `a ^ 4` is therefore `A n α ^ 2`. -/
noncomputable def A (n : ℕ) (α : ℝ) : ℝ := 1 - 2 * α / M n



end Sendov
