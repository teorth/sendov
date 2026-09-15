/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.Defs

/-!
# Positivity of the degree coordinate

`M_pos` supplies the positive denominator used by the analytic reduction and scalar coordinates.
-/

namespace Sendov

variable {n : ℕ} {α t : ℝ}

lemma M_pos (hn : 2 ≤ n) : 0 < M n := by
  have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simp only [M]
  linarith

end Sendov
