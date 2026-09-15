import FirstMoment

noncomputable section
open scoped BigOperators
namespace Sendov.PaperBinomialMode

/-- Unnormalized binomial masses; avoids all singular ratio denominators. -/
def weight (m : ℕ) (x y : ℝ) (j : ℕ) : ℝ :=
  (m.choose j : ℝ) * x ^ j * y ^ (m - j)

theorem weight_nonneg (m j : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ weight m x y j := by unfold weight; positivity

theorem weight_sum (m : ℕ) (x y : ℝ) :
    ∑ j ∈ Finset.range (m + 1), weight m x y j = (x + y) ^ m := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro j _
  unfold weight
  ring

theorem weight_adjacent (m j : ℕ) (x y : ℝ) (hj : j < m) :
    ((j : ℝ) + 1) * y * weight m x y (j + 1) =
      ((m : ℝ) - j) * x * weight m x y j := by
  have hc : (m.choose (j + 1) : ℝ) * ((j : ℝ) + 1) =
      (m.choose j : ℝ) * ((m : ℝ) - j) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hj.le] using
      congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq m j)
  have he : m - j = (m - (j + 1)) + 1 := by omega
  unfold weight
  rw [he, pow_succ]
  simp only [pow_succ]
  nlinarith only [congrArg (fun t : ℝ => t * x ^ j * y ^ (m - (j + 1)) * x * y) hc]

/-- The distinguished integer-mean binomial mass is a mode, uniformly in m,k. -/
theorem weight_mode (m k : ℕ) (hk : 0 < k) (hkm : k < m)
    (j : ℕ) (hj : j ≤ m) :
    weight m k (m - k) j ≤ weight m k (m - k) k := by
  have hx : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hy : 0 < (m : ℝ) - k := sub_pos.mpr (by exact_mod_cast hkm)
  have hn (i : ℕ) : 0 ≤ weight m k (m - k) i := weight_nonneg _ _ hx hy.le
  have hinc (i : ℕ) (hi : i < k) :
      weight m k (m - k) i ≤ weight m k (m - k) (i + 1) := by
    have ha := weight_adjacent m i k (m - k) (hi.trans hkm)
    have hc : ((i : ℝ) + 1) * ((m : ℝ) - k) ≤ ((m : ℝ) - i) * k := by
      have hri : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
      have hrm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    apply le_of_mul_le_mul_left (a := ((i : ℝ) + 1) * ((m : ℝ) - k))
      _ (by positivity)
    calc
      _ ≤ (((m : ℝ) - i) * k) * weight m k (m - k) i :=
        mul_le_mul_of_nonneg_right hc (hn i)
      _ = _ := ha.symm
  have hdec (i : ℕ) (hi : k ≤ i) (him : i < m) :
      weight m k (m - k) (i + 1) ≤ weight m k (m - k) i := by
    have ha := weight_adjacent m i k (m - k) him
    have hc : ((m : ℝ) - i) * k ≤ ((i : ℝ) + 1) * ((m : ℝ) - k) := by
      have hri : (k : ℝ) ≤ i := by exact_mod_cast hi
      have hrm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    apply le_of_mul_le_mul_left (a := ((i : ℝ) + 1) * ((m : ℝ) - k))
      _ (by positivity)
    calc
      _ = (((m : ℝ) - i) * k) * weight m k (m - k) i := ha
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (hn i)
  have hleft : ∀ n, n ≤ k → ∀ i ≤ n,
      weight m k (m - k) i ≤ weight m k (m - k) n := by
    intro n
    induction n with
    | zero =>
      intro _ i hi
      have he : i = 0 := by omega
      subst i
      rfl
    | succ n ih =>
      intro hn' i hi
      by_cases he : i = n + 1
      · subst i; rfl
      · exact (ih (by omega) i (by omega)).trans (hinc n (by omega))
  have hright : ∀ n, k ≤ n → n ≤ m →
      weight m k (m - k) n ≤ weight m k (m - k) k := by
    intro n
    induction n with
    | zero => intro hn'; omega
    | succ n ih =>
      intro hn' hnm
      by_cases he : k = n + 1
      · rw [he]
      · exact (hdec n (by omega) (by omega)).trans (ih (by omega) (by omega))
  rcases le_total j k with h | h
  · exact hleft k le_rfl j h
  · exact hright j h hj

theorem weight_first_moment_succ (m : ℕ) (x y : ℝ) :
    ∑ j ∈ Finset.range (m + 1 + 1), (j : ℝ) * weight (m + 1) x y j =
      ((m : ℝ) + 1) * x * (x + y) ^ m := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  rw [← weight_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hc : ((m : ℝ) + 1) * (m.choose j : ℝ) =
      ((m + 1).choose (j + 1) : ℝ) * ((j : ℝ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq m j
  simp only [weight, Nat.add_sub_add_right, Nat.cast_add, Nat.cast_one, pow_succ]
  nlinarith only [congrArg (fun t : ℝ => t * x ^ j * y ^ (m - j) * x) hc]

#print axioms weight_adjacent
#print axioms weight_mode
#print axioms weight_first_moment_succ
end Sendov.PaperBinomialMode
