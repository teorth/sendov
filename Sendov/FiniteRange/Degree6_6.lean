/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.FiniteRange.Batch
import Sendov.FiniteRange.PackBridge
import Sendov.Common.BernsteinCert
import Sendov.FiniteRange.BatchCertificate
import Sendov.FiniteRange.PackedMomentCertificate
import Sendov.Common.BernsteinRing

/-!
# The batch 6 to 6

`Sendov.R_le_batch` bounds every `R n α` for `6 ≤ n ≤ 6` by the elementary part and
moment at `n₀ = 6` together with the prefactor at `n₁ = 6`, so one moment and one
certificate serve all 1 degrees.  The certificate has degree 4, set by `n₀` rather
than `n₁`.

Feasibility at `n₀` is proved rather than assumed: for `n ≥ 36` it follows from
`0 ≤ α ≤ 17`, since `A - c²` increases with `n`.  This matters because feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`.
-/

-- Generated numerals cannot be wrapped, so the long-line linter is off in this file.
set_option linter.style.longLine false
set_option maxRecDepth 4000000

namespace Sendov

namespace B6_6

lemma M_lo : M 6 = 5 := by norm_num [M]

lemma M_hi : M 6 = 5 := by norm_num [M]

lemma A_lo (α : ℝ) : A 6 α = 1 - 2 * α / 5 := by rw [A, M]; push_cast; ring

lemma A_hi (α : ℝ) : A 6 α = 1 - 2 * α / 5 := by rw [A, M]; push_cast; ring

lemma c_lo {α : ℝ} (hα : 0 ≤ α) : c 6 α = (30 - 1 * α - 2 * α ^ 2) / (10 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring

/-- `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
which for `n₀ < 36` does not follow from `α ≤ 17`. -/
lemma c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 5 / 2) : 0 ≤ c 6 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

def Lc : ℤ := 60

def betac : ℤ := 17041

def tauc : ℤ := 23949621038340868125

/-- The moment numerator at `n₀ = 6`, `k = 1`. -/
def Nmomc : List ℤ :=
  [30, 154, 8]

theorem pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 6) (gg1 6) (gg2 6) 1)) α := by
  refine pev_moment_eq_of_packed_bounds 6 1 Lc betac tauc Nmomc
    (by norm_num [Lc]) (by norm_num [betac]) (by norm_num [tauc]) ?_ ?_
    (by decide) (by decide) (by rfl) α
  · norm_num [gg0, gg1, gg2, l1, betac, tauc]
  · norm_num [gg0, gg1, gg2, l1, Lc, betac]

theorem integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 6 α t ^ 1)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 6 * (3 + α)) ^ 1) :=
  integral_moment_packed 6 1 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)

set_option maxHeartbeats 2000000 in
-- the degree-4 Bernstein identity exceeds the default budget
/-- The certificate: `17 ^ 4 * P α` is a positive combination of `αʲ (17-α)^(4-j)`. -/
lemma P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 5 / 2) :
    0 < 1575 - 900 * α + 2345 * α ^ 2 - 342 * α ^ 3 - 24 * α ^ 4 := by
  have hu : (0 : ℝ) ≤ 5 - 2 * α := by linarith
  have hid : (5 : ℝ) ^ 4 * (1575 - 900 * α + 2345 * α ^ 2 - 342 * α ^ 3 - 24 * α ^ 4) = 1575 * (5 - 2 * α) ^ 4 + 8100 * α ^ 1 * (5 - 2 * α) ^ 3 + 69425 * α ^ 2 * (5 - 2 * α) ^ 2 + 188150 * α ^ 3 * (5 - 2 * α) ^ 1 + 123200 * α ^ 4 := by
    bernstein_ring α (5 - 2 * α)
  -- The certificate checks coefficient signs. The last summand is positive for α > 0;
  -- at α = 0 the first summand is positive. The identity above checks every coefficient.
  bernstein_cert α (5 - 2 * α) using hid

set_option maxHeartbeats 2000000 in
-- clearing denominators across the batch identity exceeds the default budget
/-- **The batch `6 ≤ n ≤ 6`.** -/
theorem finite_range {n : ℕ} (h0 : 6 ≤ n) (h1 : n ≤ 6) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 5 / 2 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (6 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (6 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 5) + 1 / (4 * 5 * (3 + α))
      + (1 - 2 * α / 5) ^ 2 * 6 * 5 * (6 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 5 * (3 + α)) ^ 1))
      = 1 - (1575 - 900 * α + 2345 * α ^ 2 - 342 * α ^ 3 - 24 * α ^ 4) / (375 * (3 + α) ^ 2) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  exact R_lt_one_of_batch_certificate (n₀ := 6) (n₁ := 6) (k := 1)
    (by norm_num) h0 h1 hα (c_lo_nonneg hα hUn) hfeas
    (by norm_num) M_lo M_hi (by simpa only [M_lo] using integral_lo α hα)
    hid (P_pos hα hUn) (by positivity)

end B6_6

end Sendov
