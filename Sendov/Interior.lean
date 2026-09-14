/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.Analytic.OriginExact
import Sendov.Analytic.Polar
import Sendov.Analytic.LowDegree
import Sendov.Analytic.FirstOriginSmall
import Sendov.Analytic.FirstOriginBudget
import Sendov.Analytic.Jsum
import Sendov.Counterexample.Factor
import Sendov.Reduction.Main

/-!
# Sendov's conjecture for a real interior zero

This file assembles everything: if `p` has degree `n ≥ 2`, all zeroes in the closed unit disk,
and a zero at a real `a` with `0 < a < 1`, then `p'` has a zero within distance `1` of `a`.

The proof is by contradiction.  Suppose not; then every critical point `w` satisfies
`‖w - a‖ ≥ 1`, so `Sendov.exists_crit_multiset` writes `p'` over points `qⱼ` of the closed unit
disk, and `Sendov.exists_root_multiset` writes `p` over the other zeroes `zⱼ`.  Setting
`x + iy = (∑ⱼ qⱼ)/(n-1)`, the two channels are:

* **polar**: the polar identity and `p'(a)` two ways feed the branch point `(⋆)`.

From `(⋆)` the argument branches on the degree.

* For `n = 6` or `n = 7`, the first-origin factorization bound and `(⋆)` feed
  `Sendov.FirstOriginSmall.first_origin_polar_six_seven`, without the second-origin channel.
* For `n ≥ 257`, raw polar and first-origin alone close the entire interval `0 < a < 1`.
* For `8 ≤ n ≤ 256` with `(n-1)(1-a) ≤ 2/5`, the uniform near-endpoint budget
  also closes with first-origin alone.
* In the remaining finite-degree region, the centroid identity and the two origin identities
  give `(origin-exact)`, and `Sendov.polar_origin_incompatible` closes the contradiction.
* For `n ≤ 5`, `Sendov.low_degree_contradiction` shows `(⋆)` is already contradictory on its own,
  with no recourse to the origin channel. Degree five belongs only to this low-degree branch.

The zero `a = 0` is excluded above (the polar identity divides by `a`) but needs none of this
machinery: `p'(a)` two ways already says `(∏ⱼ qⱼ)(∏ⱼ (a - zⱼ)) = n`, and at `a = 0` both factors
have norm at most one.

## Main statements

* `Sendov.sendov_interior`: the conjecture for a real zero `0 < a < 1`, every degree `n ≥ 2`;
* `Sendov.sendov_center`: the conjecture at `a = 0`;
* `Sendov.sendov_interior_real`: the two combined, `0 ≤ a < 1`.
-/

namespace Sendov

open Polynomial
open Complex (I)

/-- **Sendov's conjecture for a real interior zero.**  If every zero of `p` lies in the
closed unit disk and `p(a) = 0` for a real `a` with `0 < a < 1`, then some zero of `p'` lies
within distance `1` of `a`. -/
theorem sendov_interior {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hpa : p.eval (a : ℂ) = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - (a : ℂ)‖ < 1 := by
  by_contra hcon
  have hcrit : ∀ w : ℂ, (derivative p).eval w = 0 → 1 ≤ ‖w - (a : ℂ)‖ := by
    intro w hw
    by_contra hlt
    exact hcon ⟨w, hw, not_le.1 hlt⟩
  -- the two factorizations
  obtain ⟨z, hzcard, hz1, hpz⟩ := exists_root_multiset (by omega : 1 ≤ n) hdeg hroots hpa
  obtain ⟨q, hqcard, hq1, hq0, hpq⟩ := exists_crit_multiset hn hdeg hcrit
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hp0
  have hpq' : derivative p = C ((n : ℂ) * p.leadingCoeff)
      * ((q.map (fun v => (a : ℂ) - v⁻¹)).map (fun w => X - C w)).prod := by
    simp only [Multiset.map_map, Function.comp_def]
    exact hpq
  -- basic numerology
  have hne : ((n : ℂ) - 1) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (show n ≠ 1 by omega)
  have hqne : q ≠ 0 := by
    intro h
    rw [h, Multiset.card_zero] at hqcard
    omega
  have haC0 : ((a : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt ha0
  have haC2 : ((a : ℝ) : ℂ) ^ 2 ≠ 1 := by
    intro h
    have h1 : a ^ 2 = 1 := by exact_mod_cast h
    nlinarith only [h1, ha0, ha1]
  have hstar := one_le_integral_prod_norm hn (a := a)
    (by rw [abs_of_nonneg ha0.le]; linarith only [ha1]) hz1
    (polar_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n) (z := z) (q := q) (p := p)
      hc0 haC0 haC2 hzcard hqcard hq0 hpa hpz hpq')
    (prod_sub_mul_prod (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n) (z := z) (q := q)
      (p := p) hc0 hq0 hpz hpq')
  -- the branch: low degree needs nothing further
  rcases (by omega : n ≤ 5 ∨ 6 ≤ n) with hn5 | hn6
  · exact low_degree_contradiction hn hn5 ha0 ha1 hqcard hq1 hstar
  by_cases hn67 : n = 6 ∨ n = 7
  · exact FirstOriginSmall.first_origin_polar_six_seven hn67 ha0 ha1 hqcard hq1 hstar
      (FirstOriginSmall.norm_integral_Fprod_le_of_factorization (by omega) (ne_of_gt ha0)
        hc0 hzcard hq0 hq1 hz1 hpa hpz hpq')
  have hn5 : 5 ≤ n := by omega
  -- `x + iy` is the centroid of the `qⱼ`
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℝ, q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * I) := by
    refine ⟨(q.sum / ((n : ℂ) - 1)).re, (q.sum / ((n : ℂ) - 1)).im, ?_⟩
    rw [Complex.re_add_im, mul_div_cancel₀ _ hne]
  obtain ⟨hxre, hx2⟩ := xy_bounds hn hqcard hq1 hxy
  have hpolar := one_le_integral_Ppolar hn (a := a) (x := x) hqcard hq1 hxre hstar
  -- All sufficiently large degrees use only the first-origin channel.
  by_cases hlarge : 257 ≤ n
  · have hxSq : x ^ 2 ≤ 1 := (le_add_of_nonneg_right (sq_nonneg y)).trans hx2
    exact FirstOriginBudget.uniform_contradiction hlarge ha0 ha1
      (by nlinarith [sq_nonneg (x + 1)]) (by nlinarith [sq_nonneg (x - 1)])
      hqcard hq1 hxre hxy hpolar
      (FirstOriginSmall.norm_integral_Fprod_le_of_factorization (by omega) (ne_of_gt ha0)
        hc0 hzcard hq0 hq1 hz1 hpa hpz hpq')
  -- The uniform near-endpoint region uses only the first-origin channel.
  by_cases hnear : ((n : ℝ) - 1) * (1 - a) ≤ 2 / 5
  · have hxSq : x ^ 2 ≤ 1 := (le_add_of_nonneg_right (sq_nonneg y)).trans hx2
    exact FirstOriginBudget.near_contradiction (by omega) ha0 ha1
      (by nlinarith [sq_nonneg (x + 1)]) (by nlinarith [sq_nonneg (x - 1)])
      hqcard hq1 hxre hxy hpolar hnear
      (FirstOriginSmall.norm_integral_Fprod_le_of_factorization (by omega) (ne_of_gt ha0)
        hc0 hzcard hq0 hq1 hz1 hpa hpz hpq')
  -- the remaining origin channel
  have hcent := centroid_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n)
    (z := z) (q := q) (p := p) hn hc0 hzcard hqcard hpz hpq'
  have hfirst := first_origin_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n)
    (z := z) (q := q) (p := p) hc0 haC0 hzcard hq0 hpa hpz hpq'
  have hsecond := second_origin_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n)
    (z := z) (q := q) (p := p) hc0 hzcard hq0 hpz hpq'
  have horigin := origin_exact (n := n) (α := M n * (1 - a ^ 2) / 2) hn5 ha0 ha1 hqcard hqne
    hz1 hq1 hxy hcent hfirst hsecond rfl
  -- the two are incompatible
  exact polar_origin_incompatible hn6 ha0 ha1
    ((le_add_of_nonneg_right (sq_nonneg y)).trans hx2) rfl hpolar horigin

/-- **The conjecture at `a = 0`.**  `p'(a)` two ways gives `(∏ⱼ qⱼ)(∏ⱼ (a - zⱼ)) = n`.  At
`a = 0` the second factor is `∏ⱼ zⱼ` up to sign, so both factors have norm at most one and
`n ≤ 1` — impossible for `n ≥ 2`.  No polar or origin estimate is involved. -/
theorem sendov_center {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) (hp0 : p.eval 0 = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ‖ < 1 := by
  by_contra hcon
  have hcrit : ∀ w : ℂ, (derivative p).eval w = 0 → 1 ≤ ‖w - (0 : ℂ)‖ := by
    intro w hw
    rw [sub_zero]
    by_contra hlt
    exact hcon ⟨w, hw, not_le.1 hlt⟩
  obtain ⟨z, hzcard, hz1, hpz⟩ := exists_root_multiset (by omega : 1 ≤ n) hdeg hroots hp0
  obtain ⟨q, hqcard, hq1, hq0, hpq⟩ := exists_crit_multiset hn hdeg hcrit
  have hpne : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hpne
  have hpq' : derivative p = C ((n : ℂ) * p.leadingCoeff)
      * ((q.map (fun v => (0 : ℂ) - v⁻¹)).map (fun w => X - C w)).prod := by
    simp only [Multiset.map_map, Function.comp_def]
    exact hpq
  -- `p'(0)` two ways
  have hkey := prod_sub_mul_prod (c := p.leadingCoeff) (a := (0 : ℂ)) (n := n) (z := z) (q := q)
    (p := p) hc0 hq0 hpz hpq'
  have hnorm := congrArg norm hkey
  rw [norm_mul] at hnorm
  have h1 : ‖q.prod‖ ≤ 1 := norm_prod_le_one q hq1
  have h2 : ‖(z.map (fun w => (0 : ℂ) - w)).prod‖ ≤ 1 := by
    refine norm_prod_le_one _ ?_
    intro u hu
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hu
    simpa using hz1 w hw
  have h3 : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  rw [h3] at hnorm
  have hn1 : (n : ℝ) ≤ 1 := by
    rw [← hnorm]
    exact mul_le_one₀ h1 (norm_nonneg _) h2
  have : n ≤ 1 := by exact_mod_cast hn1
  omega

/-- **The conjecture for a real zero in `[0,1)`**, every degree `n ≥ 2`. -/
theorem sendov_interior_real {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hpa : p.eval (a : ℂ) = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - (a : ℂ)‖ < 1 := by
  rcases eq_or_lt_of_le ha0 with hz | hz
  · obtain ⟨ζ, hζ, hlt⟩ := sendov_center hn hdeg hroots (by rw [← hz] at hpa; simpa using hpa)
    exact ⟨ζ, hζ, by rw [← hz]; simpa using hlt⟩
  · exact sendov_interior hn hdeg hroots hz ha1 hpa

end Sendov
