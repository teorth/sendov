import Sendov.Analytic.PaperConjugate

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.style.whitespace false
open scoped BigOperators
namespace Sendov.PaperConjugate.DI04
open PaperCentered PaperCenteredBound
def a : ℝ := (99 / 100)
def x : ℝ := (497 / 500)
def q : Multiset ℂ := family 4 x

theorem endpoint_0 : BR 8 0 (a*x) = (129755236194000249690739517 / 1953125000000000000000000000000000000000000) := by
  norm_num [BR, a, x]

theorem endpoint_1 : BR 8 1 (a*x) = (9028001396067623395358316733 / 244140625000000000000000000000000000000000) := by
  change BR 8 (0+1) (a*x) = _
  rw [BR_succ, endpoint_0]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_2 : BR 8 2 (a*x) = (4468813436467503875509648389119 / 488281250000000000000000000000000000000000) := by
  change BR 8 (1+1) (a*x) = _
  rw [BR_succ, endpoint_1]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_3 : BR 8 3 (a*x) = (322797837513696767092920695004631 / 244140625000000000000000000000000000000000) := by
  change BR 8 (2+1) (a*x) = _
  rw [BR_succ, endpoint_2]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_4 : BR 8 4 (a*x) = (24006317294496528406918441461601619 / 195312500000000000000000000000000000000000) := by
  change BR 8 (3+1) (a*x) = _
  rw [BR_succ, endpoint_3]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_5 : BR 8 5 (a*x) = (1862625105278352074530902903881792131 / 244140625000000000000000000000000000000000) := by
  change BR 8 (4+1) (a*x) = _
  rw [BR_succ, endpoint_4]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_6 : BR 8 6 (a*x) = (154574709880501273390612630543274814119 / 488281250000000000000000000000000000000000) := by
  change BR 8 (5+1) (a*x) = _
  rw [BR_succ, endpoint_5]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_7 : BR 8 7 (a*x) = (2072872396383237544848745613388152654233 / 244140625000000000000000000000000000000000) := by
  change BR 8 (6+1) (a*x) = _
  rw [BR_succ, endpoint_6]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_8 : BR 8 8 (a*x) = (262978890825066615143918380930259298289517 / 1953125000000000000000000000000000000000000) := by
  change BR 8 (7+1) (a*x) = _
  rw [BR_succ, endpoint_7]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_3 : term 8 3 x (a*x) ≤ (1 / 2500) := by
  unfold term
  rw [endpoint_3]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_4 : term 8 4 x (a*x) ≤ (1 / 10000) := by
  unfold term
  rw [endpoint_4]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_5 : term 8 5 x (a*x) ≤ (1 / 10000) := by
  unfold term
  rw [endpoint_5]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_6 : term 8 6 x (a*x) ≤ (1 / 10000) := by
  unfold term
  rw [endpoint_6]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_7 : term 8 7 x (a*x) ≤ (1 / 10000) := by
  unfold term
  rw [endpoint_7]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_8 : term 8 8 x (a*x) ≤ (1 / 10000) := by
  unfold term
  rw [endpoint_8]
  rw [C_top]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem scalar_bound : scalarBudget 8 a x ≤ (3039368554741189238931856523020328452468902287 / 3377076171875000000000000000000000000000000000000) := by
  have h := scalarBudget_le 8 (by norm_num) a x (1 / 2500) (1 / 10000) term_3 (by
    intro k hk
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hk
    interval_cases k
    · exact term_4
    · exact term_5
    · exact term_6
    · exact term_7
    · exact term_8)
  rw [endpoint_2] at h
  norm_num [a, x] at h ⊢
  exact h

theorem scalar_budget : scalarBudget 8 a x + (1-x^2)/(8-1)/x^2 < 1-a*x := by
  have h := scalar_bound
  norm_num [a, x] at h ⊢
  linarith

theorem pointwise : ∀ w ∈ q, ‖w‖ = 1 := norm_family _ _ (by norm_num [x])
theorem cardinality : q.card = 8 := by simp [q]
theorem mean : q.sum / q.card = (x : ℂ) := mean_family _ (by norm_num) _
theorem actual_variance : variance (q.map (fun w => w-(x : ℂ))) = 1-x^2 :=
  variance_family _ (by norm_num) _ (by norm_num [x])

theorem paper_budget :
    majorant_Efin (q.map (fun w => w-(x : ℂ))) (x : ℂ) ((a : ℂ)*x) +
      Gamma (q.map (fun w => w-(x : ℂ))) (x : ℂ) < 1-a*‖(x : ℂ)‖ := by
  rw [show q = family 4 x from rfl, budget_eq _ (by norm_num) _ _ (by norm_num [x]) (by norm_num [x])]
  rw [Gamma, variance_family 4 (by norm_num) x (by norm_num [x])]
  simpa [x, Complex.norm_real, Real.norm_eq_abs, div_mul_eq_div_div] using scalar_budget

theorem norm_J_gt_one : 1 < ‖J 4 a x‖ :=
  budget_implies_J _ (by norm_num) _ _ (by norm_num [a])
    (by norm_num [x]) (by norm_num [x]) scalar_budget

def pc : Fin 9 → ℝ := ![(9227446944279201 / 10000000000000000), (9218405910404503197 / 62500000000000000000), (32288565629303218449027 / 3125000000000000000000000), (16184167604918085401840673 / 39062500000000000000000000000), (40629962660741150697562618881 / 3906250000000000000000000000000000), (65392227458663513926976073 / 390625000000000000000000000000000), (527133090672889027378227 / 312500000000000000000000000000000), (608083358527578314997 / 62500000000000000000000000000000), (2459374191553118401 / 100000000000000000000000000000000)]
theorem expansion (t : ℝ) :
    (a^2+2*a*(1-a^2)*x*t+(1-a^2)^2*t^2)^4 =
      ∑ k : Fin 9, pc k*t^k.val := by
  norm_num [a, x, pc, Fin.sum_univ_succ]
  ring

theorem polar_integral : K 4 a x = ((9844160902221705118371486810769458499 / 9843750000000000000000000000000000000) : ℝ) := by
  rw [K_eq _ _ _ (by norm_num [x]), integral_coeffs _ pc _ expansion]
  norm_num [pc, Fin.sum_univ_succ]

theorem full_polar : 1 < ‖K 4 a x‖ := by
  rw [polar_integral]
  norm_num [Complex.norm_real, Real.norm_eq_abs]

#print axioms pointwise
#print axioms mean
#print axioms actual_variance
#print axioms paper_budget
#print axioms norm_J_gt_one
#print axioms full_polar
end Sendov.PaperConjugate.DI04
