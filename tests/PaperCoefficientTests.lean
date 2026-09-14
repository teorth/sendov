import Sendov.Analytic.PaperCoefficient

/-!
Interface and edge-case regressions for the general centered coefficient theorem.
These are tests of the already proved arbitrary-family theorem, not substitutes
for it. The final declarations print the exact transitive axiom dependencies.
-/

open scoped BigOperators
open Sendov.PaperCoefficient

namespace Sendov.PaperCoefficientTests

-- The paper interface: arbitrary cardinality and an explicitly supplied mean square.
example (m k : ℕ) (r : Multiset ℂ) (hm : r.card = m) (hr : r.sum = 0)
    (v R : ℝ) (hv : v = (r.map (fun z ↦ ‖z‖ ^ 2)).sum / m) (hk : k ≤ m) :
    ‖r.esymm k‖ ^ 2 * R ^ (2 * k) ≤ (1 + R ^ 2 * v) ^ m := by
  have h := norm_esymm_sq_mul_pow_le r hr k (by omega) R
  simpa [variance, hm, hv] using h

example (m k : ℕ) (r : Multiset ℂ) (hm : r.card = m) (hr : r.sum = 0)
    (v : ℝ) (hv : v = (r.map (fun z ↦ ‖z‖ ^ 2)).sum / m)
    (hk : 0 < k) (hkm : k < m) :
    ‖r.esymm k‖ ^ 2 ≤
      (m : ℝ) ^ m / ((k : ℝ) ^ k * ((m - k : ℕ) : ℝ) ^ (m - k)) * v ^ k := by
  have h := norm_esymm_sq_le_optimized r hr k hk (by omega)
  simpa [variance, hm, hv] using h

-- No centeredness is needed for the sharp top coefficient / product bound.
example (r : Multiset ℂ) : ‖r.esymm r.card‖ ^ 2 ≤ variance r ^ r.card :=
  norm_esymm_card_sq_le r

-- Empty family, zero radius, negative radius, and zero variance are legal inputs.
example : ‖(0 : Multiset ℂ).esymm 0‖ ^ 2 * (0 : ℝ) ^ (2 * 0) ≤
    (1 + (0 : ℝ) ^ 2 * variance 0) ^ (0 : Multiset ℂ).card :=
  norm_esymm_sq_mul_pow_le 0 (by simp) 0 (by simp) 0

example (r : Multiset ℂ) (hr : r.sum = 0) (k : ℕ) (hk : k ≤ r.card) :
    ‖r.esymm k‖ ^ 2 * (-3 : ℝ) ^ (2 * k) ≤ (1 + 9 * variance r) ^ r.card := by
  convert norm_esymm_sq_mul_pow_le r hr k hk (-3) using 1; norm_num

example (r : Multiset ℂ) (hv : variance r = 0) (k : ℕ) (hk : 0 < k) :
    r.esymm k = 0 := esymm_eq_zero_of_variance_eq_zero r hv k hk

-- A genuinely complex arbitrary centered family; no assumption ‖z‖ ≤ 1.
example (z : ℂ) (R : ℝ) :
    ‖(z ::ₘ {-z}).esymm 1‖ ^ 2 * R ^ 2 ≤
      (1 + R ^ 2 * variance (z ::ₘ {-z})) ^ 2 := by
  simpa using norm_esymm_sq_mul_pow_le (z ::ₘ {-z}) (by simp) 1 (by simp) R

-- The complex finite-function formulation also feeds the theorem directly.
example {m : ℕ} (r : Fin m → ℂ) (hr : ∑ i, r i = 0)
    (k : ℕ) (hk : 0 < k) (hkm : k < m) :
    let s := (Finset.univ : Finset (Fin m)).val.map r
    ‖s.esymm k‖ ^ 2 ≤
      (m : ℝ) ^ m / ((k : ℝ) ^ k * ((m - k : ℕ) : ℝ) ^ (m - k)) *
        ((∑ i, ‖r i‖ ^ 2) / m) ^ k := by
  dsimp
  have hs : ((Finset.univ : Finset (Fin m)).val.map r).sum = 0 := by
    simpa [List.sum_ofFn] using hr
  have h := norm_esymm_sq_le_optimized ((Finset.univ : Finset (Fin m)).val.map r) hs k hk
    (by simpa using hkm)
  simpa [variance, Multiset.map_map, List.sum_ofFn, Function.comp_def] using h

end Sendov.PaperCoefficientTests

#print axioms Sendov.PaperCoefficient.circleIntegral_coeff
#print axioms Sendov.PaperCoefficient.norm_coeff_le_of_circle
#print axioms Sendov.PaperCoefficient.norm_coeff_sq_le_of_circle
#print axioms Sendov.PaperCoefficient.norm_prod_sq_le_variance_pow
#print axioms Sendov.PaperCoefficient.sum_norm_add_sq
#print axioms Sendov.PaperCoefficient.norm_prod_add_sq_le
#print axioms Sendov.PaperCoefficient.norm_esymm_sq_le
#print axioms Sendov.PaperCoefficient.variance_map_mul
#print axioms Sendov.PaperCoefficient.norm_esymm_sq_mul_pow_le
#print axioms Sendov.PaperCoefficient.variance_nonneg
#print axioms Sendov.PaperCoefficient.esymm_eq_zero_of_variance_eq_zero
#print axioms Sendov.PaperCoefficient.optimized_scalar_bound
#print axioms Sendov.PaperCoefficient.norm_esymm_sq_le_optimized
#print axioms Sendov.PaperCoefficient.norm_esymm_card_sq_le
