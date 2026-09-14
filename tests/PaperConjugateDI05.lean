import Sendov.Analytic.PaperConjugate

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.style.whitespace false
open scoped BigOperators
namespace Sendov.PaperConjugate.DI05
open PaperCentered PaperCenteredBound
def a : ℝ := (9 / 10)
def x : ℝ := (83 / 100)
def q : Multiset ℂ := family 10 x

theorem endpoint_0 : BR 20 0 (a*x) = (292099588188958046829728812997991907303491895333453 / 1000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [BR, a, x]

theorem endpoint_1 : BR 20 1 (a*x) = (920171429986559538827248474147824308778193836287597 / 50000000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (0+1) (a*x) = _
  rw [BR_succ, endpoint_0]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_2 : BR 20 2 (a*x) = (55315294526463426781596334025208673196174994266735707 / 100000000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (1+1) (a*x) = _
  rw [BR_succ, endpoint_1]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_3 : BR 20 3 (a*x) = (527637877172649985618760284030144888537701386060192729 / 50000000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (2+1) (a*x) = _
  rw [BR_succ, endpoint_2]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_4 : BR 20 4 (a*x) = (28682623332255967880724759023147655686087755546256926157 / 200000000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (3+1) (a*x) = _
  rw [BR_succ, endpoint_3]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_5 : BR 20 5 (a*x) = (92322692342579151881657605635286221403747119279055871293 / 62500000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (4+1) (a*x) = _
  rw [BR_succ, endpoint_4]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_6 : BR 20 6 (a*x) = (299461677920570523270466659540408144485095106646538331257 / 25000000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (5+1) (a*x) = _
  rw [BR_succ, endpoint_5]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_7 : BR 20 7 (a*x) = (980244050146212126263124219576223387494917988491460466193 / 12500000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (6+1) (a*x) = _
  rw [BR_succ, endpoint_6]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_8 : BR 20 8 (a*x) = (42172020237463859659427060656180340455332031698401820572641 / 100000000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (7+1) (a*x) = _
  rw [BR_succ, endpoint_7]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_9 : BR 20 9 (a*x) = (47145913355177626474756478785227522930480369709103693931403 / 25000000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (8+1) (a*x) = _
  rw [BR_succ, endpoint_8]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_10 : BR 20 10 (a*x) = (1768330556333024226103062941608320180247202713044740625076117 / 250000000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (9+1) (a*x) = _
  rw [BR_succ, endpoint_9]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_11 : BR 20 11 (a*x) = (559743313663971287089577883431885606306922668505034004509303 / 25000000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (10+1) (a*x) = _
  rw [BR_succ, endpoint_10]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_12 : BR 20 12 (a*x) = (6007536663732428518134541799675856396858852606942642957105241 / 100000000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (11+1) (a*x) = _
  rw [BR_succ, endpoint_11]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_13 : BR 20 13 (a*x) = (1713850710179293040101478567083627490139292638312266906250893 / 12500000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (12+1) (a*x) = _
  rw [BR_succ, endpoint_12]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_14 : BR 20 14 (a*x) = (6676906364584069482009808174559063649176863034483343943951657 / 25000000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (13+1) (a*x) = _
  rw [BR_succ, endpoint_13]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_15 : BR 20 15 (a*x) = (27884685314197362577256420364071419023909940455670624798845793 / 62500000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (14+1) (a*x) = _
  rw [BR_succ, endpoint_14]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_16 : BR 20 16 (a*x) = (128886663964378659476741000086636281490059321569553012365356757 / 200000000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (15+1) (a*x) = _
  rw [BR_succ, endpoint_15]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_17 : BR 20 17 (a*x) = (40830938894586144503122642438085768302740356882512944650790629 / 50000000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (16+1) (a*x) = _
  rw [BR_succ, endpoint_16]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_18 : BR 20 18 (a*x) = (92959421678338973743269847256620800292575080542580820517936507 / 100000000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (17+1) (a*x) = _
  rw [BR_succ, endpoint_17]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_19 : BR 20 19 (a*x) = (49113140822071769011813001878215413660202505524930996992466497 / 50000000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (18+1) (a*x) = _
  rw [BR_succ, endpoint_18]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem endpoint_20 : BR 20 20 (a*x) = (997813584798969014692489479877976613875152711640671467832912453 / 1000000000000000000000000000000000000000000000000000000000000000) := by
  change BR 20 (19+1) (a*x) = _
  rw [BR_succ, endpoint_19]
  norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_3 : term 20 3 x (a*x) ≤ (1 / 50) := by
  unfold term
  rw [endpoint_3]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_4 : term 20 4 x (a*x) ≤ (7 / 1000) := by
  unfold term
  rw [endpoint_4]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_5 : term 20 5 x (a*x) ≤ (7 / 1000) := by
  unfold term
  rw [endpoint_5]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_6 : term 20 6 x (a*x) ≤ (7 / 1000) := by
  unfold term
  rw [endpoint_6]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_7 : term 20 7 x (a*x) ≤ (7 / 1000) := by
  unfold term
  rw [endpoint_7]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_8 : term 20 8 x (a*x) ≤ (7 / 1000) := by
  unfold term
  rw [endpoint_8]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_9 : term 20 9 x (a*x) ≤ (7 / 1000) := by
  unfold term
  rw [endpoint_9]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_10 : term 20 10 x (a*x) ≤ (7 / 1000) := by
  unfold term
  rw [endpoint_10]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_11 : term 20 11 x (a*x) ≤ (7 / 1000) := by
  unfold term
  rw [endpoint_11]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_12 : term 20 12 x (a*x) ≤ (7 / 1000) := by
  unfold term
  rw [endpoint_12]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_13 : term 20 13 x (a*x) ≤ (7 / 1000) := by
  unfold term
  rw [endpoint_13]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_14 : term 20 14 x (a*x) ≤ (7 / 1000) := by
  unfold term
  rw [endpoint_14]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_15 : term 20 15 x (a*x) ≤ (7 / 1000) := by
  unfold term
  rw [endpoint_15]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_16 : term 20 16 x (a*x) ≤ (7 / 1000) := by
  unfold term
  rw [endpoint_16]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_17 : term 20 17 x (a*x) ≤ (7 / 1000) := by
  unfold term
  rw [endpoint_17]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_18 : term 20 18 x (a*x) ≤ (7 / 1000) := by
  unfold term
  rw [endpoint_18]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_19 : term 20 19 x (a*x) ≤ (7 / 1000) := by
  unfold term
  rw [endpoint_19]
  rw [C_interior _ _ _ (by norm_num) (by norm_num)]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem term_20 : term 20 20 x (a*x) ≤ (7 / 1000) := by
  unfold term
  rw [endpoint_20]
  rw [C_top]
  apply sqrt_term_le <;> norm_num [a, x, Nat.choose_eq_descFactorial_div_factorial]

theorem scalar_bound : scalarBudget 20 a x ≤ (18193849001759092019915918114883051985586361981871865429310238841393 / 130891000000000000000000000000000000000000000000000000000000000000000) := by
  have h := scalarBudget_le 20 (by norm_num) a x (1 / 50) (7 / 1000) term_3 (by
    intro k hk
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hk
    interval_cases k
    · exact term_4
    · exact term_5
    · exact term_6
    · exact term_7
    · exact term_8
    · exact term_9
    · exact term_10
    · exact term_11
    · exact term_12
    · exact term_13
    · exact term_14
    · exact term_15
    · exact term_16
    · exact term_17
    · exact term_18
    · exact term_19
    · exact term_20)
  rw [endpoint_2] at h
  norm_num [a, x] at h ⊢
  exact h

theorem scalar_budget : scalarBudget 20 a x + (1-x^2)/(20-1)/x^2 < 1-a*x := by
  have h := scalar_bound
  norm_num [a, x] at h ⊢
  linarith

theorem pointwise : ∀ w ∈ q, ‖w‖ = 1 := norm_family _ _ (by norm_num [x])
theorem cardinality : q.card = 20 := by simp [q]
theorem mean : q.sum / q.card = (x : ℂ) := mean_family _ (by norm_num) _
theorem actual_variance : variance (q.map (fun w => w-(x : ℂ))) = 1-x^2 :=
  variance_family _ (by norm_num) _ (by norm_num [x])

theorem paper_budget :
    majorant_Efin (q.map (fun w => w-(x : ℂ))) (x : ℂ) ((a : ℂ)*x) +
      Gamma (q.map (fun w => w-(x : ℂ))) (x : ℂ) < 1-a*‖(x : ℂ)‖ := by
  rw [show q = family 10 x from rfl, budget_eq _ (by norm_num) _ _ (by norm_num [x]) (by norm_num [x])]
  rw [Gamma, variance_family 10 (by norm_num) x (by norm_num [x])]
  simpa [x, Complex.norm_real, Real.norm_eq_abs, div_mul_eq_div_div] using scalar_budget

theorem norm_J_gt_one : 1 < ‖J 10 a x‖ :=
  budget_implies_J _ (by norm_num) _ _ (by norm_num [a])
    (by norm_num [x]) (by norm_num [x]) scalar_budget

def pc : Fin 21 → ℝ := ![(12157665459056928801 / 100000000000000000000), (2130293158770308524353 / 5000000000000000000000), (3630393128091859956309681 / 5000000000000000000000000), (62405833489723492505389989 / 78125000000000000000000000), (397188825899772937523374681101 / 625000000000000000000000000000), (303353024944630782431102935758759 / 781250000000000000000000000000000), (29519311958993848987503741418820109 / 156250000000000000000000000000000000), (1463195330075473757311721695309936161 / 19531250000000000000000000000000000000), (1920315069256239723479669645324688779049 / 78125000000000000000000000000000000000000), (131581328694644435975289506772275187759633 / 19531250000000000000000000000000000000000000), (151432591335625019536292532087062857758306249 / 97656250000000000000000000000000000000000000000), (586430366157612856630611258577670898533673 / 1953125000000000000000000000000000000000000000), (38143176366490232739459537852211365092889 / 781250000000000000000000000000000000000000000), (129529549617900123259421344575728095401 / 19531250000000000000000000000000000000000000), (11646487442853481016835261705761377389 / 15625000000000000000000000000000000000000000), (533407656322680347011077755894629359 / 7812500000000000000000000000000000000000000), (3112648786680566528459482616004381 / 625000000000000000000000000000000000000000), (2179618418460993575008088582829 / 7812500000000000000000000000000000000000), (565107564382138438609292267121 / 50000000000000000000000000000000000000000), (1477879482778254251075612313 / 5000000000000000000000000000000000000000), (37589973457545958193355601 / 10000000000000000000000000000000000000000)]
theorem expansion (t : ℝ) :
    (a^2+2*a*(1-a^2)*x*t+(1-a^2)^2*t^2)^10 =
      ∑ k : Fin 21, pc k*t^k.val := by
  norm_num [a, x, pc, Fin.sum_univ_succ]
  ring

theorem polar_integral : K 10 a x = ((1182519467309602248471006652606768554894193590679433 / 1173046875000000000000000000000000000000000000000000) : ℝ) := by
  rw [K_eq _ _ _ (by norm_num [x]), integral_coeffs _ pc _ expansion]
  norm_num [pc, Fin.sum_univ_succ]

theorem full_polar : 1 < ‖K 10 a x‖ := by
  rw [polar_integral]
  norm_num [Complex.norm_real, Real.norm_eq_abs]

#print axioms pointwise
#print axioms mean
#print axioms actual_variance
#print axioms paper_budget
#print axioms norm_J_gt_one
#print axioms full_polar
end Sendov.PaperConjugate.DI05
