/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.Common.Quadratic

/-!
# Chord bounds and Beta integrals

Retain the linear and cubic Beta integrals, scaled chord integrals, generic split and linear tail.
`Alpha17` consumes the linear tail; `Simplified` the linear chord; `TwoChord` the cubic Beta
integral.
-/

namespace Sendov

open MeasureTheory

/-! ### The Beta integrals -/

/-- The Beta integral `B(2, s+1)`. -/
lemma integral_lin_mul_rpow {s : ℝ} (hs : 0 < s) :
    (∫ x in (0 : ℝ)..1, x * (1 - x) ^ s) = 1 / ((s + 1) * (s + 2)) := by
  have hrefl : (∫ x in (0 : ℝ)..1, x * (1 - x) ^ s)
      = ∫ x in (0 : ℝ)..1, (1 - x) * x ^ s := by
    have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
      (fun y : ℝ => (1 - y) * y ^ s) 1
    simpa using this
  have hcongr : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      (1 - x) * x ^ s = x ^ s - x ^ (s + (1 : ℕ)) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rw [Real.rpow_add_natCast' hx.1 (by positivity : s + (1 : ℕ) ≠ 0)]
    ring
  rw [hrefl, intervalIntegral.integral_congr hcongr]
  have hi' : IntervalIntegrable (fun x : ℝ => x ^ s) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hi : IntervalIntegrable (fun x : ℝ => x ^ (s + (1 : ℕ))) volume 0 1 := by
    apply intervalIntegral.intervalIntegrable_rpow'
    push_cast
    linarith
  rw [intervalIntegral.integral_sub hi' hi, integral_rpow_zero_one (by linarith),
    integral_rpow_zero_one (by push_cast; linarith)]
  push_cast
  field_simp
  ring

/-- The Beta integral `B(4, s+1)`. -/
lemma integral_cube_mul_rpow {s : ℝ} (hs : 0 < s) :
    (∫ x in (0 : ℝ)..1, x ^ 3 * (1 - x) ^ s)
      = 6 / ((s + 1) * (s + 2) * (s + 3) * (s + 4)) := by
  have h1 : (0 : ℝ) < s + 1 := by linarith
  have hrefl : (∫ x in (0 : ℝ)..1, x ^ 3 * (1 - x) ^ s)
      = ∫ x in (0 : ℝ)..1, (1 - x) ^ 3 * x ^ s := by
    have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
      (fun y : ℝ => (1 - y) ^ 3 * y ^ s) 1
    simpa using this
  have hcongr : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      (1 - x) ^ 3 * x ^ s
        = x ^ s - 3 * x ^ (s + (1 : ℕ)) + 3 * x ^ (s + (2 : ℕ)) - x ^ (s + (3 : ℕ)) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rw [Real.rpow_add_natCast' hx.1 (by positivity : s + (1 : ℕ) ≠ 0),
      Real.rpow_add_natCast' hx.1 (by positivity : s + (2 : ℕ) ≠ 0),
      Real.rpow_add_natCast' hx.1 (by positivity : s + (3 : ℕ) ≠ 0)]
    ring
  rw [hrefl, intervalIntegral.integral_congr hcongr]
  have hi' : IntervalIntegrable (fun x : ℝ => x ^ s) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hi : ∀ m : ℕ, IntervalIntegrable (fun x : ℝ => x ^ (s + (m : ℕ))) volume 0 1 := by
    intro m
    apply intervalIntegral.intervalIntegrable_rpow'
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hc : ∀ (a : ℝ) (m : ℕ),
      IntervalIntegrable (fun x : ℝ => a * x ^ (s + (m : ℕ))) volume 0 1 :=
    fun a m => (hi m).const_mul a
  rw [intervalIntegral.integral_sub ((hi'.sub (hc 3 1)).add (hc 3 2)) (hi 3),
    intervalIntegral.integral_add (hi'.sub (hc 3 1)) (hc 3 2),
    intervalIntegral.integral_sub hi' (hc 3 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [integral_rpow_zero_one (by linarith), integral_rpow_zero_one (by push_cast; linarith),
    integral_rpow_zero_one (by push_cast; linarith),
    integral_rpow_zero_one (by push_cast; linarith)]
  push_cast
  field_simp
  ring

/-- The chord integral with weight `t`, over `[0, 1/c]`. -/
lemma integral_chord_lin {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    (∫ t in (0 : ℝ)..1 / c, t * (1 - c * t) ^ s) = 1 / (c ^ 2 * ((s + 1) * (s + 2))) := by
  have hc' : c ≠ 0 := hc.ne'
  have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1 / c)
    (fun y : ℝ => (y / c) * (1 - y) ^ s) hc'
  simp only [mul_div_cancel_left₀ _ hc', mul_one_div_cancel hc', mul_zero,
    div_mul_eq_mul_div, intervalIntegral.integral_div, integral_lin_mul_rpow hs,
    smul_eq_mul] at h
  rw [h]
  field_simp

/-- The chord integral with weight `t³`, over `[0, 1/c]`. -/
lemma integral_chord_pow {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    (∫ t in (0 : ℝ)..1 / c, t ^ 3 * (1 - c * t) ^ s)
      = 6 / (c ^ 4 * ((s + 1) * (s + 2) * (s + 3) * (s + 4))) := by
  have hc' : c ≠ 0 := hc.ne'
  have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1 / c)
    (fun y : ℝ => (y / c) ^ 3 * (1 - y) ^ s) hc'
  simp only [mul_div_cancel_left₀ _ hc', mul_one_div_cancel hc', mul_zero,
    div_pow, div_mul_eq_mul_div, intervalIntegral.integral_div, integral_cube_mul_rpow hs,
    smul_eq_mul] at h
  rw [h]
  field_simp

/-! ### The split -/

/-- **The tail bound, for an arbitrary weight `t^k`.**  `QQ` is a convex parabola with vertex
at `c/A`; below the vertex it lies under the chord `1 - ct`, above it it is increasing and so
at most `QQ 1`.  Splitting `∫₀¹` there gives the bound.

Two points shape the proof.  The chord bound needs `1 - ct ≥ 0`, which comes from
`ct ≤ c²/A ≤ 1` — feasibility again.  And the vertex may lie outside `[0,1]`: the split is
made at `s = min (c/A) 1`, after which the first piece is enlarged to `[0, 1/c]` (legitimate
because `s ≤ 1/c`, using `c ≤ 1` when the vertex is to the right) and the second piece is
empty when the vertex is beyond `1`. -/
theorem integral_le_tail_gen {c A : ℝ} (hfeas : c ^ 2 ≤ A) (hc : 0 < c) (hc1 : c ≤ 1)
    {r : ℝ} (hr : 0 < r) (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ k * QQ c A t ^ r)
      ≤ (∫ t in (0 : ℝ)..1 / c, t ^ k * (1 - c * t) ^ r) + QQ c A 1 ^ r / (k + 1) := by
  have hA : 0 < A := lt_of_lt_of_le (by positivity) hfeas
  set t₀ : ℝ := c / A with ht₀def
  have ht₀pos : 0 < t₀ := by positivity
  set s : ℝ := min t₀ 1 with hsdef
  have hs0 : 0 < s := lt_min ht₀pos one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  have hcont : Continuous fun u : ℝ => u ^ k * QQ c A u ^ r := continuous_pow_mul_QQ c A k hr.le
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u : ℝ => u ^ k * QQ c A u ^ r) volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have hchordcont : Continuous fun u : ℝ => u ^ k * (1 - c * u) ^ r :=
    (by fun_prop : Continuous fun u : ℝ => u ^ k).mul
      ((continuous_rpow_const hr.le).comp (by fun_prop))
  have hsc : s ≤ 1 / c := by
    rcases min_cases t₀ 1 with ⟨h, _⟩ | ⟨h, _⟩
    · rw [hsdef, h, ht₀def, le_div_iff₀ hc, div_mul_eq_mul_div, div_le_one hA]
      simpa only [pow_two] using hfeas
    · rw [hsdef, h, le_div_iff₀ hc]
      simpa only [one_mul] using hc1
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 s) (hint s 1)]
  have hfirst : (∫ u in (0 : ℝ)..s, u ^ k * QQ c A u ^ r)
      ≤ ∫ u in (0 : ℝ)..1 / c, u ^ k * (1 - c * u) ^ r := by
    have hle : (∫ u in (0 : ℝ)..s, u ^ k * QQ c A u ^ r)
        ≤ ∫ u in (0 : ℝ)..s, u ^ k * (1 - c * u) ^ r := by
      refine intervalIntegral.integral_mono_on hs0.le (hint 0 s)
        (hchordcont.intervalIntegrable _ _) ?_
      intro u hu
      obtain ⟨hu0, hus⟩ := hu
      have huv : A * u ≤ c := by
        have hut : u ≤ t₀ := le_trans hus (min_le_left _ _)
        rw [ht₀def, le_div_iff₀ hA] at hut
        linarith
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (QQ_nonneg hfeas u) (QQ_le_chord hu0 huv) hr.le) (pow_nonneg hu0 k)
    refine hle.trans ?_
    have hrest : 0 ≤ ∫ u in s..1 / c, u ^ k * (1 - c * u) ^ r := by
      refine intervalIntegral.integral_nonneg hsc ?_
      intro u hu
      have : 0 ≤ 1 - c * u := by
        have := hu.2
        rw [le_div_iff₀ hc] at this
        linarith
      exact mul_nonneg (pow_nonneg (le_trans hs0.le hu.1) k) (Real.rpow_nonneg this _)
    have hadd : (∫ u in (0 : ℝ)..s, u ^ k * (1 - c * u) ^ r)
        + (∫ u in s..1 / c, u ^ k * (1 - c * u) ^ r)
        = ∫ u in (0 : ℝ)..1 / c, u ^ k * (1 - c * u) ^ r :=
      intervalIntegral.integral_add_adjacent_intervals
        (hchordcont.intervalIntegrable 0 s) (hchordcont.intervalIntegrable s (1 / c))
    exact (le_add_of_nonneg_right hrest).trans_eq hadd
  have hsecond : (∫ u in s..1, u ^ k * QQ c A u ^ r) ≤ QQ c A 1 ^ r / (k + 1) := by
    have hBnn : (0 : ℝ) ≤ QQ c A 1 ^ r := Real.rpow_nonneg (QQ_nonneg hfeas 1) _
    have hQB : ∀ u ∈ Set.Icc s 1, QQ c A u ≤ QQ c A 1 := by
      intro u hu
      rcases le_or_gt t₀ u with h | h
      · rw [ht₀def, div_le_iff₀ hA] at h
        exact QQ_le_at_one hA.le (by linarith) hu.2
      · have hu1 : u = 1 := by
          rcases min_cases t₀ 1 with ⟨he, _⟩ | ⟨he, _⟩
          · rw [hsdef, he] at hu; linarith [hu.1]
          · rw [hsdef, he] at hu; linarith [hu.1, hu.2]
        rw [hu1]
    have hle : (∫ u in s..1, u ^ k * QQ c A u ^ r)
        ≤ ∫ u in s..1, QQ c A 1 ^ r * u ^ k := by
      refine intervalIntegral.integral_mono_on hs1 (hint s 1)
        ((by fun_prop : Continuous fun u : ℝ => QQ c A 1 ^ r * u ^ k).intervalIntegrable _ _) ?_
      intro u hu
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (QQ_nonneg hfeas u) (hQB u hu) hr.le)
        (pow_nonneg (le_trans hs0.le hu.1) k)
    refine hle.trans ?_
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have hsk : (0 : ℝ) ≤ s ^ (k + 1) := pow_nonneg hs0.le _
    rw [one_pow, ← mul_div_assoc]
    gcongr
    nlinarith [mul_nonneg hBnn hsk]
  exact add_le_add hfirst hsecond

/-- The instance with weight `t`, used for `α ≤ 17`. -/
theorem integral_le_tail_lin {c A : ℝ} (hfeas : c ^ 2 ≤ A) (hc : 0 < c) (hc1 : c ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..1, t * QQ c A t ^ r)
      ≤ 1 / (c ^ 2 * ((r + 1) * (r + 2))) + QQ c A 1 ^ r / 2 := by
  have h := integral_le_tail_gen hfeas hc hc1 hr 1
  simp only [pow_one] at h
  rw [integral_chord_lin hr hc, show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num] at h
  exact h

end Sendov
