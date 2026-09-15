import Sendov.Analytic.PaperOriginCorollaries

namespace Sendov.PaperOriginCorollariesTests
open MeasureTheory Polynomial PaperOriginCorollaries

-- Test the literal derivative with mμ, including the negative residual sign.
example {m : ℕ} {μ : ℂ} (a t : ℝ) (q : Multiset ℂ)
    (hsum : q.sum = (m : ℂ) * μ) :
    HasDerivAt (Fprod a q)
      (-(m : ℂ) * (a : ℂ) * μ * Fprod a q t -
        (a : ℂ) ^ 2 * (t : ℂ) * sumEraseProdC q (fun v => v ^ 2)
          (fun v => 1 - (a : ℂ) * (t : ℂ) * v)) t := by
  apply (derivative_decomposition a t q).congr_deriv
  rw [hsum]
  ring

-- The residual is tested expanded as a complex integral, not as an abstract R.
example {m : ℕ} (hm : 1 ≤ m) (a : ℝ) (q : Multiset ℂ) (hqcard : q.card = m) :
    (1 : ℂ) = Fprod a q 1 + (m : ℂ) * (a : ℂ) * (q.sum / (m : ℂ)) *
      (∫ t in (0 : ℝ)..1, Fprod a q t) +
      (a : ℂ) ^ 2 * ∫ t in (0 : ℝ)..1,
        (t : ℂ) * sumEraseProdC q (fun v => v ^ 2)
          (fun v => 1 - (a : ℂ) * (t : ℂ) * v) := by
  exact integrated_residual_mean hm a q hqcard

-- Public consumer: norm_majorants.
example {m : ℕ} (hm : 1 ≤ m) {a x y : ℝ} {q : Multiset ℂ}
    (ha : 0 ≤ a) (hx1 : x ≤ 1)
    (hqcard : q.card = m) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = (m : ℝ) * x)
    (hsum : q.sum = (m : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    (‖(a : ℂ) ^ 2 * ∫ t in (0 : ℝ)..1,
      (t : ℂ) * sumEraseProdC q (fun v => v ^ 2)
        (fun v => 1 - (a : ℂ) * (t : ℂ) * v)‖ ≤ (m : ℝ) * a ^ 2 *
      ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((m : ℝ) - 1) / 2)) ∧
    (‖Fprod a q 1‖ ≤ QQ (a * x) (a ^ 2) 1 ^ ((m : ℝ) / 2)) := by
  exact norm_majorants hm ha hx1 hqcard hq1 hx hsum

-- Public consumer: norm_budget.
example {m : ℕ} (hm : 1 ≤ m) {a x y : ℝ} {q : Multiset ℂ}
    (ha : 0 ≤ a) (hx1 : x ≤ 1)
    (hqcard : q.card = m) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = (m : ℝ) * x)
    (hsum : q.sum = (m : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    1 ≤ FirstOriginMargins.T (m : ℝ) a x + (m : ℝ) * a / ((m : ℝ) + 1) *
      ‖((m : ℂ) + 1) * (∫ t in (0 : ℝ)..1, Fprod a q t)‖ := by
  exact norm_budget hm ha hx1 hqcard hq1 hx hsum

-- Public consumer: first_origin_budget.
example {m : ℕ} (hm : 1 ≤ m) {a x y : ℝ} {q : Multiset ℂ}
    (ha : 0 ≤ a) (hx1 : x ≤ 1)
    (hqcard : q.card = m) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = (m : ℝ) * x)
    (hsum : q.sum = (m : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))
    (hfirst : ‖((m : ℂ) + 1) * (∫ t in (0 : ℝ)..1, Fprod a q t)‖ ≤ 1) :
    1 ≤ FirstOriginMargins.T (m : ℝ) a x + (m : ℝ) * a / ((m : ℝ) + 1) := by
  exact first_origin_budget hm ha hx1 hqcard hq1 hx hsum hfirst

-- Public consumer: polar_hierarchy.
example {n : ℕ} (hn : 2 ≤ n) {a x : ℝ} (ha : |a| ≤ 1)
    {z q : Multiset ℂ} (hz : ∀ w ∈ z, ‖w‖ ≤ 1)
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hpolar : q.prod * (z.map (fun w => 1 - (a : ℂ) * w)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod)
    (hdenom : q.prod * (z.map (fun w => (a : ℂ) - w)).prod = (n : ℂ)) :
    (1 ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖) ∧
    (‖∫ t in (0 : ℝ)..1,
      (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ ≤
      ∫ t in (0 : ℝ)..1,
        (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) ∧
    ((∫ t in (0 : ℝ)..1,
        (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) ≤
      ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2)) := by
  exact polar_hierarchy hn ha hz hqcard hq1 hx hpolar hdenom

-- Public consumer: polar_factorization_hierarchy.
example {n : ℕ} (hn : 2 ≤ n) {a x : ℝ}
    (ha : |a| ≤ 1) (ha0 : a ≠ 0) (ha2 : a ^ 2 ≠ 1)
    {c : ℂ} {p : ℂ[X]} {z q : Multiset ℂ}
    (hc0 : c ≠ 0) (hzcard : z.card = n - 1)
    (hz : ∀ w ∈ z, ‖w‖ ≤ 1)
    (hqcard : q.card = n - 1) (hq0 : ∀ v ∈ q, v ≠ 0)
    (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hpz : p = C c * ((X - C (a : ℂ)) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p = C ((n : ℂ) * c) *
      ((q.map (fun v => (a : ℂ) - v⁻¹)).map (fun w => X - C w)).prod) :
    (q.prod * (z.map (fun w => (a : ℂ) - w)).prod = (n : ℂ)) ∧
    (q.prod * (z.map (fun w => 1 - (a : ℂ) * w)).prod =
      (n : ℂ) * ∫ t in (0 : ℝ)..1,
        (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod) ∧
    (1 ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖) ∧
    (‖∫ t in (0 : ℝ)..1,
      (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ ≤
      ∫ t in (0 : ℝ)..1,
        (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) ∧
    ((∫ t in (0 : ℝ)..1,
        (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) ≤
      ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2)) := by
  exact polar_factorization_hierarchy hn ha ha0 ha2 hc0 hzcard hz hqcard hq0 hq1 hx hpz hpq

end Sendov.PaperOriginCorollariesTests

#print axioms Sendov.PaperOriginCorollaries.derivative_decomposition
#print axioms Sendov.PaperOriginCorollaries.integrated_residual_sum
#print axioms Sendov.PaperOriginCorollaries.integrated_residual
#print axioms Sendov.PaperOriginCorollaries.residual_norm_bound
#print axioms Sendov.PaperOriginCorollaries.endpoint_norm_bound
#print axioms Sendov.PaperOriginCorollaries.norm_budget
#print axioms Sendov.PaperOriginCorollaries.first_origin_budget
#print axioms Sendov.PaperOriginCorollaries.integrated_residual_mean
#print axioms Sendov.PaperOriginCorollaries.norm_majorants
#print axioms Sendov.PaperOriginCorollaries.polar_hierarchy
#print axioms Sendov.PaperOriginCorollaries.polar_factorization_hierarchy
