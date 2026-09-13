/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.Common.Chord

/-!
# Actual polar/origin coordinates

The raw polar kernel, `A_eq_sq`, and `mul_eq_c` describe actual data, not an enlarged scalar
obstruction.
Positivity and the half-degree bound for alpha are shared by the selected reduction.
-/

namespace Sendov

/-- The integrand of the raw polar inequality `(1Q)`. -/
noncomputable def Ppolar (a x t : ℝ) : ℝ :=
  a ^ 2 + 2 * a * t * x * (1 - a ^ 2) + t ^ 2 * (1 - a ^ 2) ^ 2

variable {n : ℕ} {a x t α : ℝ}

/-- `P` is a sum of squares once `|x| ≤ 1`; this is the same computation that makes
`Sendov.QQ_nonneg` work. -/
lemma Ppolar_eq (a x t : ℝ) :
    Ppolar a x t = (a + t * (1 - a ^ 2) * x) ^ 2 + t ^ 2 * (1 - a ^ 2) ^ 2 * (1 - x ^ 2) := by
  simp only [Ppolar]; ring

lemma Ppolar_nonneg (hx : x ^ 2 ≤ 1) (a t : ℝ) : 0 ≤ Ppolar a x t := by
  rw [Ppolar_eq]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (by linarith))

lemma continuous_Ppolar (a x : ℝ) : Continuous fun t : ℝ => Ppolar a x t := by
  simp only [Ppolar]; fun_prop

/-- With `α = (n-1)(1-a²)/2`, the `A` of `Sendov.Defs` is exactly `a²`. -/
lemma A_eq_sq (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) : A n α = a ^ 2 := by
  have hM : M n ≠ 0 := (M_pos hn).ne'
  simp only [A, hα]
  field_simp
  ring

/-- `ax = 1 - β(1)/2 - α/(n-1)`: the blog post's rearrangement of `β(1) = 1 - 2ax + a²`. -/
lemma mul_eq_c (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) :
    a * x = 1 - QQ (a * x) (a ^ 2) 1 / 2 - α / M n := by
  have hM : M n ≠ 0 := (M_pos hn).ne'
  simp only [QQ, hα]
  field_simp
  ring

lemma alpha_pos (hn : 2 ≤ n) (ha1 : a < 1) (_ha0 : 0 ≤ a)
    (hα : α = M n * (1 - a ^ 2) / 2) : 0 < α := by
  have hM : 0 < M n := M_pos hn
  rw [hα]
  have : 0 < 1 - a ^ 2 := by nlinarith
  positivity

lemma alpha_le_half (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) :
    α ≤ M n / 2 := by
  have hM : 0 < M n := M_pos hn
  rw [hα]
  nlinarith [sq_nonneg a]

end Sendov
