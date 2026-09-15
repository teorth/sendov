import BinomialMode

noncomputable section
open scoped BigOperators
namespace Sendov.PaperBinomialMode

/-- The unnormalized binomial mean is exactly k times its total mass. -/
theorem integer_mean_identity (m k : ℕ) (hm : 0 < m) :
    ∑ j ∈ Finset.range (m + 1), (j : ℝ) * weight m k (m - k) j =
      (k : ℝ) * (m : ℝ) ^ m := by
  cases m with
  | zero => omega
  | succ n =>
    rw [weight_first_moment_succ]
    have he' : (k : ℝ) + (((n + 1 : ℕ) : ℝ) - k) = ((n + 1 : ℕ) : ℝ) := by ring
    rw [he', pow_succ]
    push_cast
    ring

/-- The universal entropy coefficient estimate, with no Stirling bounds and no
per-degree premises. -/
theorem entropy_coefficient_bound (m k : ℕ) (hk : 0 < k) (hkm : k < m) :
    (m : ℝ) ^ m / ((k : ℝ) ^ k * ((m - k : ℕ) : ℝ) ^ (m - k)) ≤
      (2 * (k : ℝ) + 1) * (m.choose k : ℝ) := by
  have hx : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hy : (0 : ℝ) ≤ (m : ℝ) - k := sub_nonneg.mpr (by exact_mod_cast hkm.le)
  have hmass : (∑ j ∈ Finset.range (m + 1), weight m k (m - k) j) = (m : ℝ) ^ m := by
    rw [weight_sum]
    congr 1
    ring
  have h := first_moment_mass_bound (Finset.range (m + 1)) (weight m k (m - k)) k
    (weight m k (m - k) k) ((m : ℝ) ^ m)
    (weight_nonneg _ _ hx hy) (fun j _ => weight_nonneg _ _ hx hy)
    (fun j hj => weight_mode m k hk hkm j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    hmass (integer_mean_identity m k (hk.trans hkm))
  have hd : 0 < (k : ℝ) ^ k * ((m - k : ℕ) : ℝ) ^ (m - k) := by
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hmk : (0 : ℝ) < ((m - k : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hkm
    positivity
  apply (div_le_iff₀ hd).2
  unfold weight at h
  rw [Nat.cast_sub hkm.le]
  nlinarith only [h]

/-- The requested bound on the actual paper coefficient, including its top
branch and every zero/out-of-range branch. Only nonnegative variance is needed. -/
theorem C_sq_le_binomial (m k : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    PaperCenteredBound.C m k v ^ 2 ≤
      (2 * (k : ℝ) + 1) * (m.choose k : ℝ) * v ^ k := by
  by_cases ht : k = m
  · subst k
    rw [PaperCenteredBound.C_top, Real.sq_sqrt (pow_nonneg hv _), Nat.choose_self]
    simp only [Nat.cast_one, mul_one]
    have h := mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hv m)
    nlinarith
  · by_cases hi : 0 < k ∧ k < m
    · rw [PaperCenteredBound.C_interior m k v hi.1 hi.2]
      rw [Real.sq_sqrt (by positivity)]
      exact mul_le_mul_of_nonneg_right (entropy_coefficient_bound m k hi.1 hi.2)
        (pow_nonneg hv k)
    · simp only [PaperCenteredBound.C, ht, hi, ite_false, zero_pow (by decide : 2 ≠ 0)]
      positivity

#print axioms integer_mean_identity
#print axioms entropy_coefficient_bound
#print axioms C_sq_le_binomial
end Sendov.PaperBinomialMode
