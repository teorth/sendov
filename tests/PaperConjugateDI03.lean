import Sendov.Analytic.PaperConjugate

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.style.whitespace false
open scoped BigOperators
namespace Sendov.PaperConjugate.DI03
open PaperCentered PaperCenteredBound
def a : ℝ := (9 / 10)
def x : ℝ := (49 / 50)
def q : Multiset ℂ := family 3 x

theorem endpoint_0 : BR 6 0 (a*x) = (2488651484819 / 7812500000000000000) := by
  norm_num [BR, a, x]

theorem endpoint_1 : BR 6 1 (a*x) = (66349979417293 / 3906250000000000000) := by
  change BR 6 (0+1) (a*x) = _
  rw [BR_succ, endpoint_0]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_2 : BR 6 2 (a*x) = (610504600660957 / 1562500000000000000) := by
  change BR 6 (1+1) (a*x) = _
  rw [BR_succ, endpoint_1]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_3 : BR 6 3 (a*x) = (1971329487186931 / 390625000000000000) := by
  change BR 6 (2+1) (a*x) = _
  rw [BR_succ, endpoint_2]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_4 : BR 6 4 (a*x) = (62261465177667457 / 1562500000000000000) := by
  change BR 6 (3+1) (a*x) = _
  rw [BR_succ, endpoint_3]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_5 : BR 6 5 (a*x) = (765311652637904293 / 3906250000000000000) := by
  change BR 6 (4+1) (a*x) = _
  rw [BR_succ, endpoint_4]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_6 : BR 6 6 (a*x) = (4568580067478491319 / 7812500000000000000) := by
  change BR 6 (5+1) (a*x) = _
  rw [BR_succ, endpoint_5]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_3 : term 6 3 x (a*x) ≤ (1 / 250) := by
  unfold term
  rw [endpoint_3]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_4 : term 6 4 x (a*x) ≤ (1 / 1000) := by
  unfold term
  rw [endpoint_4]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_5 : term 6 5 x (a*x) ≤ (1 / 1000) := by
  unfold term
  rw [endpoint_5]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_6 : term 6 6 x (a*x) ≤ (1 / 1000) := by
  unfold term
  rw [endpoint_6]
  rw [C_top]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem scalar_bound : scalarBudget 6 a x ≤ (65685551353840242581 / 9378906250000000000000) := by
  have h := scalarBudget_le 6 (by norm_num) a x (1 / 250) (1 / 1000) term_3 (by
    intro k hk
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hk
    interval_cases k
    · exact term_4
    · exact term_5
    · exact term_6)
  rw [endpoint_2] at h
  norm_num [a, x] at h ⊢
  exact h

theorem scalar_budget : scalarBudget 6 a x + (1-x^2)/(6-1)/x^2 < 1-a*x := by
  have h := scalar_bound
  norm_num [a, x] at h ⊢
  linarith

theorem pointwise : ∀ w ∈ q, ‖w‖ = 1 := norm_family _ _ (by norm_num [x])
theorem cardinality : q.card = 6 := by simp [q]
theorem mean : q.sum / q.card = (x : ℂ) := mean_family _ (by norm_num) _
theorem actual_variance : variance (q.map (fun w => w-(x : ℂ))) = 1-x^2 :=
  variance_family _ (by norm_num) _ (by norm_num [x])

theorem paper_budget :
    majorant_Efin (q.map (fun w => w-(x : ℂ))) (x : ℂ) ((a : ℂ)*x) +
      Gamma (q.map (fun w => w-(x : ℂ))) (x : ℂ) < 1-a*‖(x : ℂ)‖ := by
  rw [show q = family 3 x from rfl, budget_eq _ (by norm_num) _ _ (by norm_num [x]) (by norm_num [x])]
  rw [Gamma, variance_family 3 (by norm_num) x (by norm_num [x])]
  simpa [x, Complex.norm_real, Real.norm_eq_abs, div_mul_eq_div_div] using scalar_budget

theorem norm_J_gt_one : 1 < ‖J 3 a x‖ :=
  budget_implies_J _ (by norm_num) _ _ (by norm_num [a])
    (by norm_num [x]) (by norm_num [x]) scalar_budget

def pc : Fin 7 → ℝ := ![(531441 / 1000000), (164923857 / 250000000), (10750716819 / 31250000000), (1507058595189 / 15625000000000), (47913688539 / 3125000000000), (3275878977 / 2500000000000), (47045881 / 1000000000000)]
theorem expansion (t : ℝ) :
    (a^2+2*a*(1-a^2)*x*t+(1-a^2)^2*t^2)^3 =
      ∑ k : Fin 7, pc k*t^k.val := by
  norm_num [a, x, pc, Fin.sum_univ_succ]
  ring

theorem polar_integral : K 3 a x = ((21948665224007 / 21875000000000) : ℝ) := by
  rw [K_eq _ _ _ (by norm_num [x]), integral_coeffs _ pc _ expansion]
  norm_num [pc, Fin.sum_univ_succ]

theorem full_polar : 1 < ‖K 3 a x‖ := by
  rw [polar_integral]
  norm_num [Complex.norm_real, Real.norm_eq_abs]

#print axioms pointwise
#print axioms mean
#print axioms actual_variance
#print axioms paper_budget
#print axioms norm_J_gt_one
#print axioms full_polar
end Sendov.PaperConjugate.DI03
