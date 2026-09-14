import Sendov.Analytic.PaperCentered

/-! Regression contracts: complex endpoints, top degree, repeated roots, degree two,
and the actual finite (not assumed) expansion. -/
noncomputable section
open scoped BigOperators
open Sendov.PaperCentered

-- Zero scaling is covered by the division-free beta theorem.
example (m k : ℕ) (hk : k ≤ m) :
    ((m + 1) * (m.choose k : ℂ) * (0 : ℂ) ^ (k + 1)) *
      (∫ t in (0 : ℝ)..1, (t : ℂ) ^ k * (1 - (0 : ℂ) * t) ^ (m - k)) =
        H m k 0 := finite_beta m k hk 0

-- Nonreal endpoints are not treated as probabilities.
example (m k : ℕ) (hk : k ≤ m) :
    ((m + 1) * (m.choose k : ℂ) * Complex.I ^ (k + 1)) *
      (∫ t in (0 : ℝ)..1, (t : ℂ) ^ k * (1 - Complex.I * t) ^ (m - k)) =
        H m k Complex.I := finite_beta m k hk Complex.I

-- The top-degree H factor really remains present.
example (m : ℕ) (z : ℂ) :
    ((m + 1 : ℂ) * z ^ (m + 1)) *
      (∫ t in (0 : ℝ)..1, (t : ℂ) ^ m) = z ^ (m + 1) := by
  simpa [H_top] using finite_beta m m le_rfl z

-- Public contract with no normalized-coefficient notation hiding the denominator.
example (q : Multiset ℂ) (a μ : ℂ) (hμ : μ ≠ 0) :
    (q.card + 1) * (a * μ) *
      (∫ t in (0 : ℝ)..1, (q.map (fun v => 1 - a * t * v)).prod) =
      ∑ k ∈ Finset.range (q.card + 1),
        ((-1) ^ k * (q.map (fun v => v - μ)).esymm k /
          ((q.card.choose k : ℂ) * μ ^ k)) * H q.card k (a * μ) := by
  simpa [coeff] using centered_integral q a μ hμ

-- Multisets retain multiplicities: no distinctness assumptions are needed.
example (x y u : ℂ) :
    ((u ::ₘ u ::ₘ (0 : Multiset ℂ)).map (fun v => x + y * v)).prod =
      ∑ k ∈ Finset.range 3, y ^ k * (u ::ₘ u ::ₘ (0 : Multiset ℂ)).esymm k * x ^ (2 - k) := by
  simpa using prod_affine (u ::ₘ u ::ₘ (0 : Multiset ℂ)) x y

-- The minimum degree has an empty high-degree tail, not an omitted H_2 endpoint.
example (u v μ z : ℂ) : tail (u ::ₘ {v}) μ z = 0 := by
  simp [tail]

example (z : ℂ) : B 2 2 z = (1 - z) ^ 3 + 3 * z * (1 - z) ^ 2 +
    3 * z ^ 2 * (1 - z) := by
  norm_num [B, Finset.sum_range_succ, Nat.choose]

-- Explicit nonreal mean and nonzero second correction.
example (a : ℂ) :
    (3 : ℂ) * (a * Complex.I) *
      (∫ t in (0 : ℝ)..1,
        (((Complex.I + 1) ::ₘ {Complex.I - 1}).map
          (fun v => 1 - a * t * v)).prod) =
      1 - correction ((((Complex.I + 1) ::ₘ {Complex.I - 1}).map
        (fun v => v - Complex.I))) Complex.I +
      epsilon ((((Complex.I + 1) ::ₘ {Complex.I - 1}).map
        (fun v => v - Complex.I))) Complex.I (a * Complex.I) := by
  convert second_order ((Complex.I + 1) ::ₘ {Complex.I - 1}) a Complex.I
    (by simp) (by simp; ring) Complex.I_ne_zero using 1
  norm_num

example : correction ((1 : ℂ) ::ₘ {-1}) Complex.I = -1 := by
  norm_num [correction, kappa, Complex.I_sq]

-- End-to-end consumption: the finite budget is discharged, not supplied as an axiom.
example : 1 < ‖(3 : ℂ) * (∫ t in (0 : ℝ)..1,
    (((1 : ℂ) ::ₘ {1}).map (fun v => 1 - (1 / 2 : ℂ) * t * v)).prod)‖ := by
  have hb : Efin ((((1 : ℂ) ::ₘ {1}).map (fun v => v - 1))) 1 (1 / 2) +
      Gamma ((((1 : ℂ) ::ₘ {1}).map (fun v => v - 1))) 1 <
        1 - (1 / 2 : ℝ) * ‖(1 : ℂ)‖ := by
    norm_num [Efin, Gamma, variance]
  convert C_budget ((1 : ℂ) ::ₘ {1}) (1 / 2) 1 (by simp) (by norm_num)
    (by norm_num) one_ne_zero (by simpa using hb) using 1
  norm_num

-- Independent audit roots for the general, not numerical, results.
#print axioms Sendov.PaperCentered.finite_beta
#print axioms Sendov.PaperCentered.centered_integral
#print axioms Sendov.PaperCentered.second_order
#print axioms Sendov.PaperCentered.norm_epsilon_le
#print axioms Sendov.PaperCentered.C_budget
