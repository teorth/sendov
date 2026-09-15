import Sendov.Common.BernsteinList

namespace Localcertificates
open BernsteinCert

example (cs : List ℕ) (i : ℕ) (x y : ℝ) :
    (coeffTree cs i).eval x y = x ^ i * (coeffTree cs 0).eval x y :=
  coeffTree_eval_shift cs i x y

example (c : ℕ) (cs : List ℕ) (x y : ℝ) :
    (coeffTree (c :: cs) 0).eval x y =
      (c : ℝ) * y ^ cs.length + x * (coeffTree cs 0).eval x y :=
  coeffTree_eval_cons c cs x y

example (x y : ℝ) : (coeffTree [] 0).eval x y = 0 :=
  coeffTree_eval_nil x y

example (x y : ℝ) : (coeffTree [7] 0).eval x y = 7 := by
  simp only [coeffTree_eval_cons, coeffTree_eval_nil, List.length_nil, Nat.cast_ofNat]
  ring1

theorem full_identity (x : ℝ) :
    2 * (1 - x) ^ 2 + 3 * x ^ 2 = (coeffTree [2, 0, 3] 0).eval x (1 - x) := by
  simp only [coeffTree_eval_cons, coeffTree_eval_nil,
    List.length_cons, List.length_nil, Nat.cast_ofNat]
  ring1

example : (coeffTree [2, 0, 3] 0).eval 0 1 = 2 ∧
    (coeffTree [2, 0, 3] 0).eval 1 0 = 3 := by
  norm_num [coeffTree_eval_cons, coeffTree_eval_nil]

example : (coeffTree [] 0).edge true = false ∧
    (coeffTree [] 0).edge false = false := by decide

example : (coeffTree [0, 1] 0).edge true = false ∧
    (coeffTree [1, 0] 0).edge false = false := by decide

example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : 0 < 2 * (1 - x) ^ 2 + 3 * x ^ 2 :=
  coeffs_pos [2, 0, 3] (lo := 0) (hi := 1) (s := 1)
    (by norm_num) (by norm_num) hx (by decide) (by decide)
    (by simpa using full_identity x)

-- Each negation concerns the full identity with the same inputs on both sides.
-- The interior coefficient mutation even preserves both endpoint values.
example : ¬ (∀ x : ℝ, 2 * (1 - x) ^ 2 + 3 * x ^ 2 =
    (coeffTree [2, 1, 3] 0).eval x (1 - x)) := by
  intro h
  have hq := h (1 / 2)
  norm_num [coeffTree_eval_cons, coeffTree_eval_nil] at hq

example : ¬ (∀ x : ℝ, 2 * (2 * (1 - x) ^ 2 + 3 * x ^ 2) =
    (coeffTree [2, 0, 3] 0).eval x (1 - x)) := by
  intro h
  have hq := h 0
  norm_num [coeffTree_eval_cons, coeffTree_eval_nil] at hq

example : ¬ (∀ x : ℝ, 2 * (1 - x) ^ 2 + 3 * x ^ 2 =
    (coeffTree [3, 0, 2] 0).eval x (1 - x)) := by
  intro h
  have hq := h 0
  norm_num [coeffTree_eval_cons, coeffTree_eval_nil] at hq

example : ¬ (∀ x : ℝ, 2 * (1 - x) ^ 2 + 3 * x ^ 2 =
    (coeffTree [2, 0] 0).eval x (1 - x)) := by
  intro h
  have hq := h 1
  norm_num [coeffTree_eval_cons, coeffTree_eval_nil] at hq

example : ¬ (∀ x : ℝ, 2 * (1 - x) ^ 2 + 3 * x ^ 2 =
    (coeffTree [2, 0, 3] 0).eval x (2 - x)) := by
  intro h
  have hq := h 0
  norm_num [coeffTree_eval_cons, coeffTree_eval_nil] at hq

example (x y : ℝ) : (x + y) ^ 2 = y ^ 2 + 2 * x * y + x ^ 2 := by
  bernstein_ring x y

end Localcertificates
