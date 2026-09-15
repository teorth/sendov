import Sendov.Analytic.PaperCenteredBound

noncomputable section
open scoped BigOperators
namespace Sendov.PaperBinomialMode

/-- Sum of the descending integer ramp, in division-free form. -/
theorem ramp_sum (L : ℕ) :
    2 * (∑ j ∈ Finset.range L, ((L : ℝ) - j)) = (L : ℝ) * (L + 1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    have h : (∑ j ∈ Finset.range L, ((L : ℝ) + 1 - j)) =
        (∑ j ∈ Finset.range L, ((L : ℝ) - j)) + L := by
      simp_rw [show ∀ j : ℕ, (L : ℝ) + 1 - j = ((L : ℝ) - j) + 1 by intro j; ring]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [h]
    nlinarith

/-- A finite first-moment inequality. The support is any finite set of naturals;
no assumption that its size is bounded by the mean is used. -/
theorem first_moment_mass_bound (s : Finset ℕ) (p : ℕ → ℝ) (k : ℕ) (P T : ℝ)
    (hP : 0 ≤ P) (hp : ∀ j ∈ s, 0 ≤ p j)
    (hmax : ∀ j ∈ s, p j ≤ P)
    (hmass : ∑ j ∈ s, p j = T)
    (hmean : ∑ j ∈ s, (j : ℝ) * p j = k * T) :
    T ≤ (2 * (k : ℝ) + 1) * P := by
  let L : ℕ := 2 * k + 1
  have hL : (L : ℝ) = 2 * (k : ℝ) + 1 := by simp [L]
  have hweight : (∑ j ∈ s, ((L : ℝ) - j) * p j) = ((k : ℝ) + 1) * T := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hmass, hmean, hL]
    ring
  have hcut : (∑ j ∈ s, ((L : ℝ) - j) * p j) ≤
      ∑ j ∈ s.filter (fun j => j < L), ((L : ℝ) - j) * P := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro j hj
    split_ifs with h
    · exact mul_le_mul_of_nonneg_left (hmax j hj)
        (sub_nonneg.mpr (by exact_mod_cast Nat.le_of_lt h))
    · have hjL : (L : ℝ) ≤ j := by exact_mod_cast (Nat.le_of_not_gt h)
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hjL) (hp j hj)
  have hext : (∑ j ∈ s.filter (fun j => j < L), ((L : ℝ) - j) * P) ≤
      ∑ j ∈ Finset.range L, ((L : ℝ) - j) * P := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
    · intro j hj _
      apply mul_nonneg _ hP
      have h : j < L := Finset.mem_range.mp hj
      exact sub_nonneg.mpr (by exact_mod_cast Nat.le_of_lt h)
  have hramp := ramp_sum L
  rw [hweight] at hcut
  have h := hcut.trans hext
  rw [← Finset.sum_mul] at h
  have hs : (∑ j ∈ Finset.range L, ((L : ℝ) - j)) =
      (2 * (k : ℝ) + 1) * ((k : ℝ) + 1) := by
    nlinarith [hL]
  rw [hs] at h
  by_contra hn
  have hpos := mul_pos (by positivity : 0 < (k : ℝ) + 1)
    (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [h, hpos]

/-- Every upper bound on a finite probability distribution with integer mean k
is at least 1/(2k+1). -/
theorem probability_max_mass (s : Finset ℕ) (p : ℕ → ℝ) (k : ℕ) (P : ℝ)
    (hP : 0 ≤ P) (hp : ∀ j ∈ s, 0 ≤ p j)
    (hmax : ∀ j ∈ s, p j ≤ P)
    (hmass : ∑ j ∈ s, p j = 1)
    (hmean : ∑ j ∈ s, (j : ℝ) * p j = k) :
    1 / (2 * (k : ℝ) + 1) ≤ P := by
  apply (div_le_iff₀ (by positivity : 0 < 2 * (k : ℝ) + 1)).2
  simpa [mul_comm] using first_moment_mass_bound s p k P 1 hP hp hmax hmass (by simpa using hmean)

#print axioms first_moment_mass_bound
#print axioms probability_max_mass
end Sendov.PaperBinomialMode
