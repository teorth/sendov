import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

/-!
# Parameter-preserving bulk budget

The algebraic middle-region argument of first-origin-uniform/round5, §4.
These lemmas close the scalar budget from the stated integral estimate;
they do not assert that estimate or claim the complete uniform D theorem.
-/

namespace Sendov.PaperBulk

/-- The middle-region cubic has an explicit positive decomposition. -/
theorem middle_cubic_pos {a : ℝ} (ha : 1 / 3 ≤ a) (hb : a ≤ 4 / 5) :
    0 < 256 * a ^ 2 * (1 - a) - 24 * a ^ 2 - 16 := by
  have h₁ : 0 ≤ (a - 1 / 3) * (536 / 225) := by positivity
  have h₂ : 0 ≤ (a - 1 / 3) * (4 / 5 - a) * (256 * a + 872 / 15) := by
    positivity
  have hid : 256 * a ^ 2 * (1 - a) - 24 * a ^ 2 - 16 =
      8 / 27 + (a - 1 / 3) * (536 / 225) +
        (a - 1 / 3) * (4 / 5 - a) * (256 * a + 872 / 15) := by ring
  rw [hid]
  linarith

/-- All real m ≥ 256 satisfy the retained-a budget on the middle interval. -/
theorem middle_budget {m a : ℝ} (hm : 256 ≤ m)
    (ha : 1 / 3 ≤ a) (hb : a ≤ 4 / 5) :
    16 / (m * a ^ 2) + 24 / m < 1 - a := by
  have hm0 : 0 < m := by linarith
  have ha0 : 0 < a := by linarith
  have hh : 0 ≤ 1 - a := by linarith
  have hc := middle_cubic_pos ha hb
  have hmul : 0 ≤ (m - 256) * a ^ 2 * (1 - a) := by positivity
  have hp : 16 + 24 * a ^ 2 < (1 - a) * (m * a ^ 2) := by nlinarith
  have hd : 0 < m * a ^ 2 := by positivity
  calc
    16 / (m * a ^ 2) + 24 / m = (16 + 24 * a ^ 2) / (m * a ^ 2) := by
      field_simp
    _ < 1 - a := (div_lt_iff₀ hd).2 hp

/-- A consumer of the analytic estimate, with strictness unchanged. -/
theorem direct_budget_middle {m a T : ℝ} (hm : 256 ≤ m)
    (ha : 1 / 3 ≤ a) (hb : a ≤ 4 / 5)
    (hT : T < 16 / (m * a ^ 2) + 24 / m) :
    T < 1 - m * a / (m + 1) := by
  have hm0 : 0 < m + 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hp : 0 < a / (m + 1) := div_pos ha0 hm0
  have he : 1 - m * a / (m + 1) = 1 - a + a / (m + 1) := by
    field_simp
    ring
  rw [he]
  have ht := hT.trans (middle_budget hm ha hb)
  linarith

/-- The same retained-a estimate closes the large-a, large-ray region. -/
theorem large_ray_budget {m a : ℝ} (hm : 0 < m) (ha : 4 / 5 ≤ a)
    (hscale : 49 ≤ m * (1 - a)) :
    16 / (m * a ^ 2) + 24 / m ≤ 1 - a := by
  have ha0 : 0 < a := by linarith
  have ha2 : (4 / 5 : ℝ) ^ 2 ≤ a ^ 2 := by nlinarith
  have hd : 0 < m * a ^ 2 := by positivity
  have hfirst : 16 / (m * a ^ 2) ≤ 25 / m := by
    apply (div_le_iff₀ hd).2
    have he : 25 / m * (m * a ^ 2) = 25 * a ^ 2 := by field_simp
    rw [he]
    nlinarith
  have hlast : 49 / m ≤ 1 - a := (div_le_iff₀ hm).2 (by nlinarith [hscale])
  calc
    16 / (m * a ^ 2) + 24 / m ≤ 25 / m + 24 / m := by linarith
    _ = 49 / m := by ring
    _ ≤ 1 - a := hlast

/-- Small-a closure of the global two-thirds bound. -/
theorem direct_budget_small {m a T : ℝ} (hm : 0 ≤ m)
    (ha : 0 < a) (hb : a ≤ 1 / 3) (hT : T < 2 / 3) :
    T < 1 - m * a / (m + 1) := by
  have hd : 0 < m + 1 := by linarith
  have he : 1 - m * a / (m + 1) = 1 - a + a / (m + 1) := by
    field_simp
    ring
  have hp := div_pos ha hd
  rw [he]
  linarith

end Sendov.PaperBulk
