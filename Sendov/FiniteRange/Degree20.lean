/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.FiniteRange.Reduce

/-!
# The finite-range claim in degree twenty

A scaling test for the general machinery: here `k = 8`, so `Sendov.mom 20 α 8` is a
45-term double sum, and the cleared numerator `P` has degree 18 with coefficients of up to
22 digits.  Positivity of `P` on `[0, 19/2]` is well beyond `nlinarith`, so this is the
first degree needing an explicit certificate.

The certificate is a Bernstein representation on `[0, 19/2]`:

  `19 ^ 18 * P α = ∑ j < 19, Γ j * α ^ j * (19 - 2α) ^ (18 - j)`

with all nineteen `Γ j` positive integers (of up to 34 digits).  Since `α ≥ 0` and
`19 - 2α ≥ 0` on the range, every summand is nonnegative, and at least one is strictly
positive, so `P > 0`.  `P` in fact stays positive up to `α = 12.05`, while feasibility
gives only `α ≤ 19/2`, so the certificate has room to spare.
-/

set_option maxRecDepth 8000

namespace Sendov

open MeasureTheory

variable {α : ℝ}

lemma M_twenty : M 20 = 19 := by norm_num [M]

lemma A_twenty (α : ℝ) : A 20 α = 1 - 2 * α / 19 := by
  rw [A, M]
  push_cast
  ring

lemma c_twenty (α : ℝ) : c 20 α = 1 - α / 19 - α / (2 * (3 + α)) := by
  rw [c, M]
  push_cast
  ring

lemma c_twenty' (hα : 0 ≤ α) : c 20 α = (114 + 13 * α - 2 * α ^ 2) / (38 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c_twenty]
  field_simp
  ring

/-- The Bernstein certificate for the degree-twenty numerator on `[0, 19/2]`. -/
lemma P_twenty_pos (hα : 0 ≤ α) (hle : α ≤ 19 / 2) :
    0 <     2428684725423666483774 + 7331467129251995458872 * α + 9806391760574638480284 * α ^ 2 +
      7611575747798170524888 * α ^ 3 + 3758723770378675135797 * α ^ 4 + 1206125979814312523496 * α
      ^ 5 + 235504051379657180694 * α ^ 6 + 11454730616615814828 * α ^ 7 - 32607895082957507571 *
      α ^ 8 + 5227920728232680812 * α ^ 9 + 102472476340054572 * α ^ 10 - 2640164743526400 * α ^
      11 - 847605280292160 * α ^ 12 - 61937116512768 * α ^ 13 - 2508597900288 * α ^ 14 -
      62979502080 * α ^ 15 - 979335936 * α ^ 16 - 8690688 * α ^ 17 - 33792 * α ^ 18 := by
  have hu : (0 : ℝ) ≤ 19 - 2 * α := by linarith
  have hid : (19 : ℝ) ^ 18 *
      (2428684725423666483774 + 7331467129251995458872 * α + 9806391760574638480284 * α ^ 2 +
        7611575747798170524888 * α ^ 3 + 3758723770378675135797 * α ^ 4 + 1206125979814312523496 *
        α ^ 5 + 235504051379657180694 * α ^ 6 + 11454730616615814828 * α ^ 7 -
        32607895082957507571 * α ^ 8 + 5227920728232680812 * α ^ 9 + 102472476340054572 * α ^ 10 -
        2640164743526400 * α ^ 11 - 847605280292160 * α ^ 12 - 61937116512768 * α ^ 13 -
        2508597900288 * α ^ 14 - 62979502080 * α ^ 15 - 979335936 * α ^ 16 - 8690688 * α ^ 17 -
        33792 * α ^ 18)
      = 2428684725423666483774 * (19 - 2 * α) ^ 18 +
          226730525571039907134432 * α ^ 1 * (19 - 2 *
          α) ^ 17 + 9762590243023517445883524 * α ^ 2 * (19 - 2 * α) ^ 16 +
          257123733807820195223425224 * α ^ 3 * (19 - 2 * α) ^ 15 + 4632014993012551188816601077 *
          α ^ 4 * (19 - 2 * α) ^ 14 + 60459331875837108393876395364 * α ^ 5 * (19 - 2 * α) ^ 13 +
          590623191218980187440834237938 * α ^ 6 * (19 - 2 * α) ^ 12 +
          4389613323288949613610408693204 * α ^ 7 * (19 - 2 * α) ^ 11 +
          24480093296536555966858990491717 * α ^ 8 * (19 - 2 * α) ^ 10 +
          100744503274528106203930847272696 * α ^ 9 * (19 - 2 * α) ^ 9 +
          306223243964547514886419597653624 * α ^ 10 * (19 - 2 * α) ^ 8 +
          708731127961028987356988552204352 * α ^ 11 * (19 - 2 * α) ^ 7 +
          1342727866428363194166781707341088 * α ^ 12 * (19 - 2 * α) ^ 6 +
          2273564082246386518492641655978752 * α ^ 13 * (19 - 2 * α) ^ 5 +
          3442867955253474296197691549373696 * α ^ 14 * (19 - 2 * α) ^ 4 +
          4130621657305785039523793191219200 * α ^ 15 * (19 - 2 * α) ^ 3 +
          3349606068894706620649142246807040 * α ^ 16 * (19 - 2 * α) ^ 2 +
          1529243641677728878687500000000000 * α ^ 17 * (19 - 2 * α) ^ 1 +
          274558827655262150000000000000000 * α ^ 18 := by
    ring
  -- The last Bernstein term is positive away from zero; the first handles zero.
  apply (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 19 ^ 18)).mp
  rw [hid]
  rcases lt_or_eq_of_le hα with hpos | hzero
  · positivity
  · subst α
    norm_num

/-- The upper bound for `R 20 α`, from the general moment formula with `k = 8`. -/
lemma R_twenty_le (hα : 0 ≤ α) :
    R 20 α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / 38 + 1 / (76 * (3 + α))
      + 1710 * A 20 α ^ 2 / (3 + α) * mom 20 α 8 := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  have hk : ((((20 : ℕ) : ℝ) - 4) / 2) = ((8 : ℕ) : ℝ) := by norm_num
  have h := R_le_of_integral_le (n := 20) (by norm_num) hα (le_of_eq (integral_eq_mom 8 hk))
  rw [M_twenty] at h
  push_cast at h
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

/-- **The finite-range claim in degree twenty.** -/
theorem finite_range_twenty (hα : 0 ≤ α) (hfeas : c 20 α ^ 2 ≤ A 20 α) : R 20 α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hle : α ≤ 19 / 2 := by
    have h := alpha_le_half_M (n := 20) (by norm_num) hfeas
    rw [M_twenty] at h
    linarith
  have hR := R_twenty_le hα
  have hid : 1 / 6 + 1 / (4 * (3 + α)) + 1 / 38 + 1 / (76 * (3 + α))
      + 1710 * A 20 α ^ 2 / (3 + α) * mom 20 α 8
      = 1 -
        (2428684725423666483774 + 7331467129251995458872 * α + 9806391760574638480284 * α ^ 2 +
          7611575747798170524888 * α ^ 3 + 3758723770378675135797 * α ^ 4 + 1206125979814312523496
          * α ^ 5 + 235504051379657180694 * α ^ 6 + 11454730616615814828 * α ^ 7 -
          32607895082957507571 * α ^ 8 + 5227920728232680812 * α ^ 9 + 102472476340054572 * α ^ 10
          - 2640164743526400 * α ^ 11 - 847605280292160 * α ^ 12 - 61937116512768 * α ^ 13 -
          2508597900288 * α ^ 14 - 62979502080 * α ^ 15 - 979335936 * α ^ 16 - 8690688 * α ^ 17 -
          33792 * α ^ 18)
          / (178855464872570772 * (3 + α) ^ 9) := by
    rw [mom, A_twenty, c_twenty' hα]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.cast_one]
    norm_num
    field_simp
    ring
  rw [hid] at hR
  have hP := P_twenty_pos hα hle
  exact hR.trans_lt (sub_lt_self _ (div_pos hP (by positivity)))

end Sendov
