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
# The batch 12 to 13

`Sendov.R_le_batch` bounds every `R n α` for `12 ≤ n ≤ 13` by the elementary part and
moment at `n₀ = 12` together with the prefactor at `n₁ = 13`, so one moment and one
certificate serve all 2 degrees.  The certificate has degree 10, set by `n₀` rather
than `n₁`.

Feasibility at `n₀` is proved rather than assumed: for `n ≥ 36` it follows from
`0 ≤ α ≤ 17`, since `A - c²` increases with `n`.  This matters because feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`.
-/

-- Generated numerals cannot be wrapped, so the long-line linter is off in this file.
set_option linter.style.longLine false
set_option maxRecDepth 4000000

namespace Sendov

namespace B12_13

lemma M_lo : M 12 = 11 := by norm_num [M]

lemma M_hi : M 13 = 12 := by norm_num [M]

lemma A_lo (α : ℝ) : A 12 α = 1 - 2 * α / 11 := by rw [A, M]; push_cast; ring

lemma A_hi (α : ℝ) : A 13 α = 1 - 2 * α / 12 := by rw [A, M]; push_cast; ring

lemma c_lo {α : ℝ} (hα : 0 ≤ α) : c 12 α = (66 + 5 * α - 2 * α ^ 2) / (22 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring

/-- `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
which for `n₀ < 36` does not follow from `α ≤ 17`. -/
lemma c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 6) : 0 ≤ c 12 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

def Lc : ℤ := 27720

def betac : ℤ := 538941732215041

def tauc : ℤ := 6292050050870377734039180756234778163021074014036716599319294695000296491713270664825204672831809746575409998007435248501929604780211870392204795696401964180489810388769719091757577450834981070202288673

/-- The moment numerator at `n₀ = 12`, `k = 4`. -/
def Nmomc : List ℤ :=
  [265646304, 754389504, 1044603648, 1046977536, 1399732528, 127959680, 6424320, 167936, 1792]

theorem pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 12) (gg1 12) (gg2 12) 4)) α := by
  refine pev_moment_eq_of_packed_bounds 12 4 Lc betac tauc Nmomc
    (by norm_num [Lc]) (by norm_num [betac]) (by norm_num [tauc]) ?_ ?_
    (by decide) (by decide) (by rfl) α
  · norm_num [gg0, gg1, gg2, l1, betac, tauc]
  · norm_num [gg0, gg1, gg2, l1, Lc, betac]

theorem integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 12 α t ^ 4)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 12 * (3 + α)) ^ 4) :=
  integral_moment_packed 12 4 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)

set_option maxHeartbeats 2000000 in
-- the degree-10 Bernstein identity exceeds the default budget
/-- The certificate: `17 ^ 10 * P α` is a positive combination of `αʲ (17-α)^(10-j)`. -/
lemma P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 6) :
    0 < 67214552328 + 108758874312 * α + 64248083658 * α ^ 2 + 8893434528 * α ^ 3 - 26471207052 * α ^ 4 + 9402730740 * α ^ 5 - 77587159 * α ^ 6 - 46242248 * α ^ 7 - 3634800 * α ^ 8 - 118976 * α ^ 9 - 1456 * α ^ 10 := by
  have hu : (0 : ℝ) ≤ 6 - α := by linarith
  have hid : (6 : ℝ) ^ 10 * (67214552328 + 108758874312 * α + 64248083658 * α ^ 2 + 8893434528 * α ^ 3 - 26471207052 * α ^ 4 + 9402730740 * α ^ 5 - 77587159 * α ^ 6 - 46242248 * α ^ 7 - 3634800 * α ^ 8 - 118976 * α ^ 9 - 1456 * α ^ 10) = 67214552328 * (6 - α) ^ 10 + 1324698769152 * α ^ 1 * (6 - α) ^ 9 + 11210565079296 * α ^ 2 * (6 - α) ^ 8 + 51982093082304 * α ^ 3 * (6 - α) ^ 7 + 112831785636336 * α ^ 4 * (6 - α) ^ 6 + 136300060037952 * α ^ 5 * (6 - α) ^ 5 + 172834300408608 * α ^ 6 * (6 - α) ^ 4 + 277236880276032 * α ^ 7 * (6 - α) ^ 3 + 281516219316936 * α ^ 8 * (6 - α) ^ 2 + 131510134768320 * α ^ 9 * (6 - α) ^ 1 + 19805743188000 * α ^ 10 := by
    bernstein_ring α (6 - α)
  -- The certificate checks coefficient signs. The last summand is positive for α > 0;
  -- at α = 0 the first summand is positive. The identity above checks every coefficient.
  bernstein_cert α (6 - α) using hid

set_option maxHeartbeats 2000000 in
-- clearing denominators across the batch identity exceeds the default budget
/-- **The batch `12 ≤ n ≤ 13`.** -/
theorem finite_range {n : ℕ} (h0 : 12 ≤ n) (h1 : n ≤ 13) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 6 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (13 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (13 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 11) + 1 / (4 * 11 * (3 + α))
      + (1 - 2 * α / 12) ^ 2 * 13 * 12 * (13 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 11 * (3 + α)) ^ 4))
      = 1 - (67214552328 + 108758874312 * α + 64248083658 * α ^ 2 + 8893434528 * α ^ 3 - 26471207052 * α ^ 4 + 9402730740 * α ^ 5 - 77587159 * α ^ 6 - 46242248 * α ^ 7 - 3634800 * α ^ 8 - 118976 * α ^ 9 - 1456 * α ^ 10) / (442743840 * (3 + α) ^ 5) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  exact R_lt_one_of_batch_certificate (n₀ := 12) (n₁ := 13) (k := 4)
    (by norm_num) h0 h1 hα (c_lo_nonneg hα hUn) hfeas
    (by norm_num) M_lo M_hi (by simpa only [M_lo] using integral_lo α hα)
    hid (P_pos hα hUn) (by positivity)

end B12_13

end Sendov
