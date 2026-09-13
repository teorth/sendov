/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.Reduction.CubicScalar
import Sendov.Common.DistillationBounds

/-!
# Polar/origin incompatibility through the cubic scalar obstruction

For `n ≥ 6`, the original geometric hypotheses produce the scalar domain and
`1 ≤ H`. The complete finite/tail bound proves `H < 1` on that same domain.
Degrees two through five are handled directly by the low-degree analytic argument
in `Interior`; no old `R` certificate route is needed.
-/

namespace Sendov

/-- The original polar and origin inequalities are incompatible in degrees at
least six. No scalar inequality is assumed as an extra hypothesis. -/
theorem polar_origin_incompatible {n : ℕ} (hn : 6 ≤ n) {a x α : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2))
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1,
        t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) : False := by
  obtain ⟨hpos, hhalf, h17, hlower⟩ :=
    cubicScalar_constraints_of_polar_origin hn ha ha1 hx hα hpolar horigin
  exact (not_lt_of_ge hlower) (distillScalar_lt_one hn hpos h17 hhalf)

end Sendov
