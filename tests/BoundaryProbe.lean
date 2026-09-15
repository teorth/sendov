import Sendov.Boundary

open Sendov

-- This first consumer was compiled RED before the new declaration existed.
example (s : Multiset ℂ)
    (hsecond : (s.map (fun v => ‖v‖ ^ 2)).sum ≤ (s.card : ℝ))
    (hfirst : (s.card : ℝ) ≤ s.sum.re) : ∀ v ∈ s, v = 1 := by
  exact all_eq_one_of_sum_norm_sq_le_card hsecond hfirst

-- The single average boundary interface is consumed, not re-proved here.
example {N : ℕ} {qs zs : Multiset ℂ}
    (hqcard : qs.card = N) (hzcard : zs.card = N)
    (hqsecond : (qs.map (fun v => ‖v‖ ^ 2)).sum ≤ (N : ℝ))
    (hz1 : ∀ w ∈ zs, ‖w‖ ≤ 1) (hzne : ∀ w ∈ zs, w ≠ 1)
    (hBR : qs.sum = 2 * (zs.map (fun w => ((1 : ℂ) - w)⁻¹)).sum) :
    ∀ v ∈ qs, v = 1 :=
  all_q_eq_one_of_sum_norm_sq_le hqcard hzcard hqsecond hz1 hzne hBR

example {N : ℕ} {qs zs : Multiset ℂ}
    (hqcard : qs.card = N) (hzcard : zs.card = N)
    (hq1 : ∀ v ∈ qs, ‖v‖ ≤ 1) (hz1 : ∀ w ∈ zs, ‖w‖ ≤ 1)
    (hzne : ∀ w ∈ zs, w ≠ 1)
    (hBR : qs.sum = 2 * (zs.map (fun w => ((1 : ℂ) - w)⁻¹)).sum) :
    ∀ v ∈ qs, v = 1 := by
  -- Migrated pointwise consumer: form the second moment at the call site.
  apply all_q_eq_one_of_sum_norm_sq_le hqcard hzcard ?_ hz1 hzne hBR
  have h := Multiset.sum_le_card_nsmul (qs.map (fun v => ‖v‖ ^ 2)) (1 : ℝ) (by
    intro r hr
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.1 hr
    exact pow_le_one₀ (norm_nonneg v) (hq1 v hv))
  simpa only [Multiset.card_map, hqcard, nsmul_eq_mul, mul_one] using h

-- Empty, singleton, and repeated points: no division by card or deduplication.
example : ∀ v ∈ (0 : Multiset ℂ), v = 1 :=
  all_eq_one_of_sum_norm_sq_le_card (by simp) (by simp)

example : ∀ v ∈ ({1} : Multiset ℂ), v = 1 :=
  all_eq_one_of_sum_norm_sq_le_card (by simp) (by simp)

example (k : ℕ) : ∀ v ∈ Multiset.replicate k (1 : ℂ), v = 1 :=
  all_eq_one_of_sum_norm_sq_le_card (by simp) (by simp)

example : ∀ v ∈ ({1, 1} : Multiset ℂ), v = 1 :=
  all_q_eq_one_of_sum_norm_sq_le (N := 2) (zs := {-1, -1})
    (by simp) (by simp) (by norm_num) (by simp) (by norm_num)
    (by norm_num)

example : ∀ v ∈ (0 : Multiset ℂ), v = 1 :=
  all_q_eq_one_of_sum_norm_sq_le (N := 0) (zs := 0)
    rfl rfl (by simp) (by simp) (by simp) (by simp)

example (s : Multiset ℂ) :
    (s.map (fun v => ‖v - 1‖ ^ 2)).sum =
      (s.map (fun v => ‖v‖ ^ 2)).sum - 2 * s.sum.re + s.card :=
  sum_norm_sub_one_sq s

example : (({Complex.I, Complex.I} : Multiset ℂ).map (fun v => ‖v - 1‖ ^ 2)).sum = 4 := by
  rw [sum_norm_sub_one_sq]
  norm_num

-- The aggregate second-moment assumption alone is genuinely weaker than the pointwise one.
example : ∃ s : Multiset ℂ,
    (s.map (fun v => ‖v‖ ^ 2)).sum ≤ (s.card : ℝ) ∧ ¬ (∀ v ∈ s, ‖v‖ ≤ 1) := by
  refine ⟨{(6 / 5 : ℂ), 0}, ?_, ?_⟩ <;> norm_num

-- Real counterexamples to dropping either generic hypothesis (no inconsistent assumptions).
example : ∃ s : Multiset ℂ,
    (s.map (fun v => ‖v‖ ^ 2)).sum ≤ (s.card : ℝ) ∧ ¬ (∀ v ∈ s, v = 1) := by
  exact ⟨{0}, by norm_num, by norm_num⟩

example : ∃ s : Multiset ℂ,
    (s.card : ℝ) ≤ s.sum.re ∧ ¬ (∀ v ∈ s, v = 1) := by
  exact ⟨{2}, by norm_num, by norm_num⟩

-- Even equality of the first moment does not control the imaginary part.
example : ∃ s : Multiset ℂ,
    (s.card : ℝ) = s.sum.re ∧ ¬ (∀ v ∈ s, v = 1) := by
  refine ⟨{1 + Complex.I}, by norm_num, ?_⟩
  simp only [Multiset.mem_singleton, forall_eq, add_eq_left, Complex.I_ne_zero, not_false_eq_true]

-- Every retained premise of the boundary helper has a consistent omission witness.
-- Without second moment: q={2}, z={0}; all remaining boundary premises hold.
example : ∃ qs zs : Multiset ℂ,
    qs.card = 1 ∧ zs.card = 1 ∧
    (∀ w ∈ zs, ‖w‖ ≤ 1) ∧ (∀ w ∈ zs, w ≠ 1) ∧
    qs.sum = 2 * (zs.map (fun w => ((1 : ℂ) - w)⁻¹)).sum ∧
    ¬ (∀ v ∈ qs, v = 1) := by
  refine ⟨{2}, {0}, ?_⟩
  norm_num

-- Without z != 1, totalized inverse at zero makes BR hold with q=0.
example : ∃ qs zs : Multiset ℂ,
    qs.card = 1 ∧ zs.card = 1 ∧
    (qs.map (fun v => ‖v‖ ^ 2)).sum ≤ (1 : ℝ) ∧ (∀ w ∈ zs, ‖w‖ ≤ 1) ∧
    qs.sum = 2 * (zs.map (fun w => ((1 : ℂ) - w)⁻¹)).sum ∧
    ¬ (∀ v ∈ qs, v = 1) := by
  refine ⟨{0}, {1}, ?_⟩
  norm_num

-- Without the z disk bound: q=-1, z=3.
example : ∃ qs zs : Multiset ℂ,
    qs.card = 1 ∧ zs.card = 1 ∧
    (qs.map (fun v => ‖v‖ ^ 2)).sum ≤ (1 : ℝ) ∧ (∀ w ∈ zs, w ≠ 1) ∧
    qs.sum = 2 * (zs.map (fun w => ((1 : ℂ) - w)⁻¹)).sum ∧
    ¬ (∀ v ∈ qs, v = 1) := by
  refine ⟨{-1}, {3}, ?_⟩
  norm_num

-- Without BR: q=0, z=-1.
example : ∃ qs zs : Multiset ℂ,
    qs.card = 1 ∧ zs.card = 1 ∧
    (qs.map (fun v => ‖v‖ ^ 2)).sum ≤ (1 : ℝ) ∧
    (∀ w ∈ zs, ‖w‖ ≤ 1) ∧ (∀ w ∈ zs, w ≠ 1) ∧ ¬ (∀ v ∈ qs, v = 1) := by
  refine ⟨{0}, {-1}, ?_⟩
  norm_num

-- Without matching z cardinality: N=1, q={0}, z=empty.
example : ∃ qs zs : Multiset ℂ,
    qs.card = 1 ∧ (qs.map (fun v => ‖v‖ ^ 2)).sum ≤ (1 : ℝ) ∧
    (∀ w ∈ zs, ‖w‖ ≤ 1) ∧ (∀ w ∈ zs, w ≠ 1) ∧
    qs.sum = 2 * (zs.map (fun w => ((1 : ℂ) - w)⁻¹)).sum ∧
    ¬ (∀ v ∈ qs, v = 1) := by
  refine ⟨{0}, 0, ?_⟩
  norm_num

-- Direct polynomial consumer of the rewired strict-or-extremal theorem.
example {n : ℕ} (hn : 2 ≤ n) {p : Polynomial ℂ} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) (hp1 : p.eval 1 = 0) :
    (∃ ζ : ℂ, (Polynomial.derivative p).eval ζ = 0 ∧ ‖ζ - 1‖ < 1)
      ∨ p = Polynomial.C p.leadingCoeff * (Polynomial.X ^ n - 1) :=
  rubinstein_one hn hdeg hroots hp1

-- Without matching q cardinality: N=0, q={0}, z=empty.
example : ∃ qs zs : Multiset ℂ,
    zs.card = 0 ∧ (qs.map (fun v => ‖v‖ ^ 2)).sum ≤ (0 : ℝ) ∧
    (∀ w ∈ zs, ‖w‖ ≤ 1) ∧ (∀ w ∈ zs, w ≠ 1) ∧
    qs.sum = 2 * (zs.map (fun w => ((1 : ℂ) - w)⁻¹)).sum ∧
    ¬ (∀ v ∈ qs, v = 1) := by
  refine ⟨{0}, 0, ?_⟩
  norm_num
