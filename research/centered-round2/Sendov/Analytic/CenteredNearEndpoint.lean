import Sendov.Analytic.CenteredNearScalar
import Sendov.Analytic.PaperCenteredVarianceEndpoint

noncomputable section
open scoped BigOperators
namespace Sendov.CenteredNearScalar

lemma linear_decay (m : ℕ) (hm : 7 ≤ m) :
    (m : ℝ) * rho ^ (m - 1) ≤ 7 * rho ^ 6 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hnr : (7 : ℝ) ≤ n := by exact_mod_cast hn
    have he : n + 1 - 1 = (n - 1) + 1 := by omega
    rw [he, pow_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    calc
      ((n : ℝ) + 1) * (rho ^ (n - 1) * rho) =
          (((n : ℝ) + 1) * rho) * rho ^ (n - 1) := by ring
      _ ≤ (n : ℝ) * rho ^ (n - 1) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg rho_bounds.1.le _)
        dsimp [rho]
        linarith
      _ ≤ _ := ih

lemma quadratic_decay (m : ℕ) (hm : 7 ≤ m) :
    ((m : ℝ) + 1) ^ 2 * rho ^ (m - 1) ≤ 64 * rho ^ 6 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hnr : (7 : ℝ) ≤ n := by exact_mod_cast hn
    have he : n + 1 - 1 = (n - 1) + 1 := by omega
    rw [he, pow_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    calc
      ((n : ℝ) + 1 + 1) ^ 2 * (rho ^ (n - 1) * rho) =
          ((((n : ℝ) + 1 + 1) ^ 2) * rho) * rho ^ (n - 1) := by ring
      _ ≤ ((n : ℝ) + 1) ^ 2 * rho ^ (n - 1) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg rho_bounds.1.le _)
        dsimp [rho]
        nlinarith
      _ ≤ _ := ih

/-- The complete finite complex B2 endpoint has a uniform geometric envelope. -/
theorem norm_B_two_le (m : ℕ) (hm : 7 ≤ m) (z : ℂ)
    (hz : ‖z‖ ≤ 1) (hw : ‖1 - z‖ ≤ rho) :
    ‖PaperCentered.B m 2 z‖ ≤ ((m : ℝ) + 1) ^ 2 * rho ^ (m - 1) := by
  have hs : ‖PaperCentered.B m 2 z‖ ≤
      ∑ j ∈ Finset.range 3, ((m+1).choose j : ℝ) * rho ^ (m - 1) := by
    unfold PaperCentered.B
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro j hj
    have hj2 : j ≤ 2 := by have := Finset.mem_range.mp hj; omega
    have hpow : ‖1 - z‖ ^ (m+1-j) ≤ rho ^ (m-1) :=
      (pow_le_pow_left₀ (norm_nonneg _) hw _).trans
        (pow_le_pow_of_le_one rho_bounds.1.le rho_bounds.2.le (by omega))
    have hzpow := pow_le_one₀ (norm_nonneg z) hz (n := j)
    simp only [norm_mul, norm_pow, Complex.norm_natCast]
    calc
      ((m+1).choose j : ℝ) * ‖z‖^j * ‖1-z‖^(m+1-j) =
          ((m+1).choose j : ℝ) * (‖z‖^j * ‖1-z‖^(m+1-j)) := by ring
      _ ≤ ((m+1).choose j : ℝ) * (1 * rho^(m-1)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hzpow hpow (pow_nonneg (norm_nonneg _) _) (by norm_num))
          (Nat.cast_nonneg _)
      _ = _ := by ring
  have hc : ((m+1).choose 2 : ℝ) = (m : ℝ) * ((m : ℝ)+1) / 2 := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  have hsum : (∑ j ∈ Finset.range 3, ((m+1).choose j : ℝ) * rho ^ (m-1)) =
      (1 + ((m : ℝ)+1) + ((m+1).choose 2 : ℝ)) * rho ^ (m-1) := by
    norm_num [Finset.sum_range_succ, Nat.choose_one_right]
    ring
  rw [hsum] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg rho_bounds.1.le _)
  rw [hc]
  have hmr : (7 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

/-- The two finite endpoint terms consume less than one thousandth of h. -/
theorem endpoint_le (m : ℕ) (hm : 7 ≤ m) (h G : ℝ) (z : ℂ)
    (hh : 0 ≤ h) (hG0 : 0 ≤ G) (hG : G ≤ 7*h/18)
    (hz : ‖z‖ ≤ 1) (hw : ‖1-z‖ ≤ rho) (hwsq : ‖1-z‖^2 ≤ (m : ℝ)*h/3) :
    ‖1-z‖^(m+1) + G * ‖PaperCentered.B m 2 z‖ ≤ h/1000 := by
  have hwpow := pow_le_pow_left₀ (norm_nonneg (1-z)) hw (m-1)
  have he : ‖1-z‖^(m+1) = ‖1-z‖^2 * ‖1-z‖^(m-1) := by
    rw [← pow_add]
    congr 1
    omega
  have hzero : ‖1-z‖^(m+1) ≤ (7*h/3)*rho^6 := by
    rw [he]
    have h1 := mul_le_mul hwsq hwpow (pow_nonneg (norm_nonneg _) _) (by positivity)
    have h2 := mul_le_mul_of_nonneg_left (linear_decay m hm) (by positivity : 0 ≤ h/3)
    nlinarith only [h1, h2]
  have hB := (norm_B_two_le m hm z hz hw).trans (quadratic_decay m hm)
  have hsecond := mul_le_mul hG hB (norm_nonneg _) (by positivity : 0 ≤ 7*h/18)
  have hconstant : (7/3 : ℝ)*rho^6 + (7/18 : ℝ)*64*rho^6 ≤ 1/1000 := by norm_num [rho]
  have hfinal := mul_le_mul_of_nonneg_right hconstant hh
  nlinarith only [hzero, hsecond, hfinal]

lemma beta_le_lambda_third (m : ℕ) (hm : 7 ≤ m) (a x : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hp : PaperPolar.RawPolar m a x) :
    PaperPolar.b a x ≤ (m : ℝ) * (1-a) / 3 := by
  have hb := PaperPolar.endpoint_bounds hm ha0 ha1 hx0 hx1 hp
  have hl := PaperPolar.lambda_pos (by omega : 0 < m) ha1
  have hb0 := PaperPolar.b_pos ha0.le ha1 hx1
  have hh := (le_div_iff₀ (by positivity : 0 < 3 + PaperPolar.lambda m a)).mp (hb.1.trans hb.2)
  have hn := mul_nonneg hl.le hb0.le
  unfold PaperPolar.lambda at hh hn
  nlinarith only [hh, hn]

/-- Both actual finite endpoints are uniformly small throughout lambda≤4/39. -/
theorem actual_endpoint_le (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hmean : q.sum = q.card * μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1) (hx0 : -1 ≤ μ.re) (hx1 : μ.re ≤ 1)
    (hp : PaperPolar.RawPolar q.card a μ.re) (hl : PaperPolar.lambda q.card a ≤ 4/39) :
    ‖1 - (a : ℂ)*μ‖^(q.card+1) +
      PaperCentered.Gamma (q.map (fun z => z-μ)) μ * ‖PaperCentered.B q.card 2 ((a : ℂ)*μ)‖ ≤
      (1-a)/1000 := by
  have hu := (PaperConsequences.centered_variance_le q μ (by omega) hmean hq).2
  have hv0 : 0 ≤ PaperCentered.variance (q.map (fun z => z-μ)) :=
    PaperCoefficient.variance_nonneg _
  have hcouple := PaperCenteredVarianceEndpoint.actual_variance_endpoint q μ a (by omega) hmean hq
  have hw2 : ‖1 - (a : ℂ)*μ‖^2 ≤ PaperPolar.b a μ.re := by
    nlinarith only [hcouple, mul_nonneg (sq_nonneg a) hv0]
  have hbr := beta_le_rho_sq q.card hm a μ.re ha0 ha1 hx0 hx1 hp hl
  have hw : ‖1 - (a : ℂ)*μ‖ ≤ rho := by nlinarith [norm_nonneg (1-(a : ℂ)*μ), rho_bounds.1]
  have hz : ‖(a : ℂ)*μ‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
    exact (mul_le_of_le_one_right ha0.le hu).trans ha1.le
  have hg := PaperConsequences.Gamma_lt_seven_eighteenths q hm ha0 ha1 hmean hq hx0 hx1 rfl hp
  have hg0 : 0 ≤ PaperCentered.Gamma (q.map (fun z => z-μ)) μ := by
    unfold PaperCentered.Gamma
    simp only [Multiset.card_map]
    have hmr : (7 : ℝ) ≤ q.card := by exact_mod_cast hm
    have hden : 0 ≤ (q.card : ℝ) - 1 := by linarith
    exact div_nonneg hv0 (mul_nonneg hden (sq_nonneg _))
  exact endpoint_le q.card hm (1-a) _ ((a : ℂ)*μ) (by linarith) hg0 hg.le hz hw
    (hw2.trans (beta_le_lambda_third q.card hm a μ.re ha0 ha1 hx0 hx1 hp))

/-- Raw polar bounds the actual variance itself, not an independently chosen proxy. -/
theorem actual_variance_le_lambda_third (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hmean : q.sum = q.card * μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1) (hx0 : -1 ≤ μ.re) (hx1 : μ.re ≤ 1)
    (hp : PaperPolar.RawPolar q.card a μ.re) :
    PaperCentered.variance (q.map (fun z => z-μ)) ≤ (q.card : ℝ)*(1-a)/3 := by
  have hv := (PaperConsequences.centered_variance_le q μ (by omega) hmean hq).1
  have hn : 1 - PaperPolar.b a μ.re ≤ ‖μ‖^2 := by
    have hh := Complex.sq_norm_sub_sq_re μ
    unfold PaperPolar.b
    nlinarith only [hh, sq_nonneg μ.im, sq_nonneg (μ.re-a)]
  have hb := beta_le_lambda_third q.card hm a μ.re ha0 ha1 hx0 hx1 hp
  linarith

theorem actual_tailScalar_le (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hmean : q.sum = q.card * μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1) (hx0 : -1 ≤ μ.re) (hx1 : μ.re ≤ 1)
    (hp : PaperPolar.RawPolar q.card a μ.re) (hl : PaperPolar.lambda q.card a ≤ 4/39) :
    tailScalar q.card (PaperCentered.variance (q.map (fun z => z-μ))) ≤ 3*(1-a)/5 := by
  apply tailScalar_le (q.card : ℝ) (1-a) _ (by exact_mod_cast hm) (by linarith)
    (by simpa only [PaperPolar.lambda] using hl)
  · exact PaperCoefficient.variance_nonneg _
  · exact actual_variance_le_lambda_third q hm a μ ha0 ha1 hmean hq hx0 hx1 hp

end Sendov.CenteredNearScalar
