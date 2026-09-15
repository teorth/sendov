import Sendov.Common.BernsteinCert
import Sendov.Common.BernsteinRing

/-!
# Coefficient-list frontend for the existing Bernstein certificate theorem

The raw list `[c₀, …, cₙ]` denotes `∑ cᵢ X^i Y^(n-i)` (no extra binomial
factors). Natural coefficients give nonnegativity; both axis supports are checked
by the existing `Cert.edge`. Empty data denotes zero and cannot have either support.
Every application still supplies a complete polynomial identity proved in Lean.
`coeffTree_eval_cons` factors the existing evaluation into Horner form, so a
single `ring1` can check that identity after structural simplification. No new
certificate representation or positivity checker is involved.
-/
namespace BernsteinCert

/-- Build the existing addition tree, starting the X exponent at `i`.
The singleton case avoids adding an artificial zero monomial of a different degree. -/
def coeffTree : List ℕ → ℕ → Cert
  | [], _ => .mono 0 0 0
  | [c], i => .mono c i 0
  | c :: d :: cs, i => .add (.mono c i (cs.length + 1)) (coeffTree (d :: cs) (i + 1))

/-- Factor the common X power without expanding either coordinate. -/
theorem coeffTree_eval_shift (cs : List ℕ) (i : ℕ) (x y : ℝ) :
    (coeffTree cs i).eval x y = x ^ i * (coeffTree cs 0).eval x y := by
  induction cs generalizing i with
  | nil => simp [coeffTree, Cert.eval]
  | cons c cs ih =>
    cases cs with
    | nil => simp [coeffTree, Cert.eval, mul_comm]
    | cons d cs =>
      simp only [coeffTree, Cert.eval, ih (i + 1), ih 1]
      ring

/-- One Horner step for the complete supplied coefficient list.
Rewriting with this identity shares X powers; it does not replace the data or
assume an identity for the polynomial being certified. -/
theorem coeffTree_eval_cons (c : ℕ) (cs : List ℕ) (x y : ℝ) :
    (coeffTree (c :: cs) 0).eval x y =
      (c : ℝ) * y ^ cs.length + x * (coeffTree cs 0).eval x y := by
  cases cs with
  | nil => simp [coeffTree, Cert.eval]
  | cons d cs =>
    simp only [coeffTree, Cert.eval, coeffTree_eval_shift (d :: cs) 1,
      List.length_cons, pow_zero, pow_one, mul_one]

theorem coeffTree_eval_nil (x y : ℝ) :
    (coeffTree [] 0).eval x y = 0 := by
  simp [coeffTree, Cert.eval]

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
