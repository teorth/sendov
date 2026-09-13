import Sendov.Common.BernsteinList
import Sendov.Common.DistillationFinite
import Sendov.Common.Sinh

namespace Localgenerators

open BernsteinCert

example (a : Cert) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : 0 < x + y) (hl : a.edge true = true) (hr : a.edge false = true) :
    0 < a.eval x y := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · exact a.pos_left le_rfl (by simpa only [zero_add] using hxy) hl
  · exact a.pos_right hx hy hr

example {lo hi x : ℝ} (hab : lo < hi) : 0 < (x - lo) + (hi - x) := by
  simpa only [sub_add_sub_cancel'] using sub_pos.mpr hab

example : (coeffTree [] 0).edge true = false ∧
    (coeffTree [] 0).edge false = false := by decide

example : (coeffTree [1] 0).edge true = true ∧
    (coeffTree [1] 0).edge false = true := by decide

example : (coeffTree [0, 1] 0).edge true = false ∧
    (coeffTree [1, 0] 0).edge false = false := by decide

example : (coeffTree [2, 3, 5] 0).eval 2 3 = 56 := by
  norm_num [coeffTree, Cert.eval]

example (x : ℝ) : 0 < (coeffTree [1] 0).eval x (-x) := by
  norm_num [coeffTree, Cert.eval]

example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : 0 < x ^ 2 + (1 - x) ^ 2 := by
  refine coeffs_pos [1, 0, 1] (lo := 0) (hi := 1) (s := 1)
    (by norm_num) (by norm_num) hx (by decide) (by decide) ?_
  norm_num only [coeffTree, Cert.eval, List.length_cons, List.length_nil]
  ring

example : 0 < (coeffTree [2, 0, 3] 0).eval 0 1 :=
  (coeffTree [2, 0, 3] 0).pos (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide)

example : 0 < (coeffTree [2, 0, 3] 0).eval 1 0 :=
  (coeffTree [2, 0, 3] 0).pos (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide)

example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : 0 < x + y) : 0 < x + y := by
  have hid : 1 * (x + y) = x + y := one_mul _
  bernstein_cert x y using hid

example (x y : ℝ) : (x + y) ^ 2 = y ^ 2 + 2 * x * y + x ^ 2 := by
  bernstein_ring x y

example (x y : ℝ) : x + y + 1 = 1 + (x + y) := by
  fail_if_success bernstein_ring x y
  ring

example (x y : ℝ) : y - x = -1 * x + y := by
  fail_if_success bernstein_ring x y
  ring

example {m : ℕ} (hm : 5 ≤ m) (hm63 : m ≤ 63) {α : ℝ} (hα : 0 ≤ α)
    (hαm : α ≤ (m : ℝ) / 2) (h17 : α ≤ 17) :
    Sendov.distillEBudget m + Sendov.distillT0 m α + Sendov.distillT1 m α +
      Sendov.distillT2 m α < 199 / 200 :=
  Sendov.distillFinite_components hm hm63 hα hαm h17

example {α : ℝ} (hα : 0 ≤ α) (h17 : α ≤ 17) :
    Sendov.distillT0 64 α ≤ 217 / 1000 :=
  Sendov.CriticalRow64.component0 α hα h17

example {α : ℝ} (hα : 0 ≤ α) (h17 : α ≤ 17) :
    Sendov.distillT1 64 α ≤ 37 / 1000 :=
  Sendov.CriticalRow64.component1 α hα h17

example {α : ℝ} (hα : 0 ≤ α) (h17 : α ≤ 17) :
    Sendov.distillT2 64 α ≤ 317 / 1000 :=
  Sendov.CriticalRow64.component2 α hα h17

example : Real.sinh 0 ≤ 0 * Real.exp (Real.sqrt (0 ^ 2 + 9) - 3) :=
  Sendov.sinh_le_mul_exp le_rfl

example {h : ℝ} (hh : 0 < h) :
    Real.log (Real.sinh h / h) ≤ Real.sqrt (h ^ 2 + 9) - 3 :=
  Sendov.log_sinh_div_le hh

end Localgenerators
