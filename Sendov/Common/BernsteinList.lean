import Sendov.Common.BernsteinCert
import Sendov.Common.BernsteinRing

/-!
# Coefficient-list frontend for the existing Bernstein certificate theorem

The raw list `[c₀, …, cₙ]` denotes `∑ cᵢ X^i Y^(n-i)` (no extra binomial
factors). Natural coefficients give nonnegativity; both axis supports are checked
by the existing `Cert.edge`. Empty data denotes zero and cannot have either support.
Every application still supplies a complete polynomial identity proved in Lean.
-/
namespace BernsteinCert

/-- Build the existing addition tree, starting the X exponent at `i`.
The singleton case avoids adding an artificial zero monomial of a different degree. -/
def coeffTree : List ℕ → ℕ → Cert
  | [], _ => .mono 0 0 0
  | [c], i => .mono c i 0
  | c :: d :: cs, i => .add (.mono c i (cs.length + 1)) (coeffTree (d :: cs) (i + 1))

/-- Closed-interval positivity from raw coefficients; no new positivity checker.
The interval, scale, two endpoint supports and full identity are explicit obligations. -/
theorem coeffs_pos (cs : List ℕ) {lo hi s P x : ℝ}
    (hab : lo < hi) (hs : 0 < s) (hx : x ∈ Set.Icc lo hi)
    (hl : (coeffTree cs 0).edge true = true)
    (hr : (coeffTree cs 0).edge false = true)
    (hid : s * P = (coeffTree cs 0).eval (x - lo) (hi - x)) : 0 < P := by
  exact scaled_pos (coeffTree cs 0) hid hs (sub_nonneg.mpr hx.1)
    (sub_nonneg.mpr hx.2)
    (by simpa only [sub_add_sub_cancel'] using sub_pos.mpr hab) hl hr

end BernsteinCert
