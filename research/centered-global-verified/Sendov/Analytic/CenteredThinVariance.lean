import Sendov.Analytic.CenteredQuarterTheorem

/-! A positive-variance strip valid for all lambda, not only near lambda zero. -/
noncomputable section
open scoped BigOperators
namespace Sendov.CenteredThinVariance
open PaperCentered PaperCenteredBound CenteredActualTail

def crudeTail (M v : ℝ) : ℝ :=
  (3/8)*(M+1)*Real.sqrt (M*(M-1)*(M-2))*Real.sqrt (v^3)

lemma crudeTail_le (M h v : ℝ) (hM : 7 ≤ M) (hh0 : 0 ≤ h) (hh1 : h ≤ 1/10)
    (hv0 : 0 ≤ v) (hv : M^2*v ≤ h) : crudeTail M v ≤ 3*h/56 := by
  let D := M*(M-1)*(M-2)
  have hM0 : 0 < M := by linarith
  have hM1 : 0 < M-1 := by linarith
  have hM2 : 0 < M-2 := by linarith
  have hD0 : 0 < D := by dsimp [D]; positivity
  have hD : D ≤ M^3 := by
    dsimp [D]
    nlinarith only [mul_nonneg hM0.le (show 0 ≤ 3*M-2 by linarith)]
  have hplus : (M+1)^2 ≤ (64/49)*M^2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hplus hD0.le
  have h2 := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ (64/49)*M^2)
  have hcoef : (M+1)^2*D ≤ (64/49)*M^5 := by nlinarith only [h1,h2]
  have he : (crudeTail M v)^2 = (9/64)*(M+1)^2*D*v^3 := by
    unfold crudeTail
    change ((3/8)*(M+1)*Real.sqrt D*Real.sqrt (v^3))^2 = _
    simp only [mul_pow, Real.sq_sqrt hD0.le, Real.sq_sqrt (pow_nonneg hv0 3)]
    ring
  have hs := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hv0 3)
  have hsq : (crudeTail M v)^2 ≤ (9/49)*M^5*v^3 := by nlinarith only [he,hs]
  have hc := pow_le_pow_left₀ (mul_nonneg (sq_nonneg M) hv0) hv 3
  have hhM : h ≤ M/64 := by linarith
  have hh3 := mul_le_mul_of_nonneg_right hhM (sq_nonneg h)
  have hcap : M^5*v^3 ≤ h^2/64 := by
    apply (mul_le_mul_iff_right₀ hM0).mp
    nlinarith only [hc,hh3]
  have hscaled := mul_le_mul_of_nonneg_left hcap (by norm_num : (0 : ℝ) ≤ 9/49)
  apply (sq_le_sq₀ (by unfold crudeTail; positivity) (by positivity : 0 ≤ 3*h/56)).mp
  nlinarith only [hsq,hscaled]

lemma norm_B_two_global (m : ℕ) (hm : 7 ≤ m) (z : ℂ)
    (hz : ‖z‖ ≤ 1) (hw : ‖1-z‖ ≤ 1) : 1+‖B m 2 z‖ ≤ (m : ℝ)^2 := by
  have hs : ‖B m 2 z‖ ≤ ∑ j ∈ Finset.range 3, ((m+1).choose j : ℝ) := by
    unfold B
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro j hj
    simp only [norm_mul,norm_pow,Complex.norm_natCast]
    have h1 := pow_le_one₀ (norm_nonneg z) hz (n := j)
    have h2 := pow_le_one₀ (norm_nonneg (1-z)) hw (n := m+1-j)
    calc
      _ = ((m+1).choose j : ℝ)*(‖z‖^j*‖1-z‖^(m+1-j)) := by ring
      _ ≤ ((m+1).choose j : ℝ)*(1*1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (by norm_num)) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hmR : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : ((m+1).choose 2 : ℝ) = (m : ℝ)*((m : ℝ)+1)/2 := by
    rw [Nat.cast_choose_two]; push_cast; ring
  norm_num [Finset.sum_range_succ,Nat.choose_one_right,hc] at hs
  nlinarith

lemma gamma_endpoint_le (M h u v Bv : ℝ) (hM : 7 ≤ M) (hh : 0 ≤ h)
    (hu : 81/400 ≤ u^2) (hv0 : 0 ≤ v) (hv : M^2*v ≤ h)
    (hB : 1+Bv ≤ M^2) : v/((M-1)*u^2)*(1+Bv) ≤ 6*h/7 := by
  have hm1 : 6 ≤ M-1 := by linarith
  have hden : 243/200 ≤ (M-1)*u^2 := by
    have ht := mul_le_mul hm1 hu (by norm_num : (0 : ℝ) ≤ 81/400) (by linarith : 0 ≤ M-1)
    nlinarith only [ht]
  have hd0 : 0 < (M-1)*u^2 := by linarith
  have hnum : v*(1+Bv) ≤ h := by nlinarith only [mul_le_mul_of_nonneg_left hB hv0,hv]
  calc
    _ = (v*(1+Bv))/((M-1)*u^2) := by ring
    _ ≤ h/((M-1)*u^2) := div_le_div_of_nonneg_right hnum hd0.le
    _ ≤ h/(243/200) := div_le_div_of_nonneg_left hh (by norm_num) hden
    _ ≤ 6*h/7 := by nlinarith

lemma cubic_integral_le (m : ℕ) (hm : 7 ≤ m) (a x : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hp : PaperPolar.RawPolar m a x) :
    (∫ t in (0 : ℝ)..1, t^3*(Real.sqrt (PaperPolar.beta a x t))^(m-3)) ≤ 1/4 := by
  have hc := (PaperPolar.geometry hm ha0 ha1 hx0 hx1 hp).2.le
  have hi : (∫ t in (0 : ℝ)..1, t^3*(Real.sqrt (PaperPolar.beta a x t))^(m-3)) ≤
      ∫ t in (0 : ℝ)..1, t^3 := by
    apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (Continuous.intervalIntegrable (by unfold PaperPolar.beta; fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    intro t ht
    have hb := PaperPolar.beta_le_chord (a := a) (x := x) ht.1 ht.2
    have hb1 : PaperPolar.beta a x t ≤ 1 := by nlinarith only [hb,mul_nonneg hc ht.1]
    have hs := pow_le_one₀ (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr hb1) (n := m-3)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (pow_nonneg ht.1 3)
  apply hi.trans_eq
  norm_num [integral_pow]

theorem majorantTail_le_crude (r : Multiset ℂ) (hm : 7 ≤ r.card) (μ : ℂ) (a : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (hμ : μ ≠ 0) (hu : ‖μ‖ ≤ 1)
    (hx0 : -1 ≤ μ.re) (hx1 : μ.re ≤ 1) (hv : variance r ≤ 1-‖μ‖^2)
    (hp : PaperPolar.RawPolar r.card a μ.re) :
    majorantTail r μ ((a : ℂ)*μ) ≤ crudeTail r.card (variance r) := by
  have ht := majorantTail_le_cubicIntegral r (by omega) μ a ha0.le hμ hv
  have hi := cubic_integral_le r.card hm a μ.re ha0 ha1 hx0 hx1 hp
  have hdesc := PaperFactorialTail.cast_descFactorial_three r.card (by omega)
  have hroot : Real.sqrt (9/4 : ℝ) = 3/2 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  rw [hdesc,Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9/4),hroot] at ht
  have his := mul_le_mul_of_nonneg_left hi
    (show 0 ≤ ((r.card : ℝ)+1)*a^4*‖μ‖*((3/2)*Real.sqrt ((r.card : ℝ)*((r.card : ℝ)-1)*((r.card : ℝ)-2)))*Real.sqrt ((variance r)^3) by positivity)
  have hau : a^4*‖μ‖ ≤ 1 := mul_le_one₀ (pow_le_one₀ ha0.le ha1.le) (norm_nonneg _) hu
  have haub := mul_le_mul_of_nonneg_right hau
    (show 0 ≤ (3/8)*((r.card : ℝ)+1)*Real.sqrt ((r.card : ℝ)*((r.card : ℝ)-1)*((r.card : ℝ)-2))*Real.sqrt ((variance r)^3) by positivity)
  unfold crudeTail
  nlinarith only [ht,his,haub]

/-- Original FULLpolar C-near in the positive-variance strip, with no lambda
restriction. The variance-strip restriction is explicit and actual. -/
theorem C_near_fullpolar_strip (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha : 9/10 ≤ a) (ha1 : a < 1) (hmean : q.sum = q.card*μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1)
    (hp : 1 ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun z => (a : ℂ)+(t : ℂ)*(1-(a : ℂ)^2)*z)).prod‖)
    (hstrip : variance (q.map (fun z => z-μ)) ≤ (1-a)/(q.card : ℝ)^2) :
    majorant_Efin (q.map (fun z => z-μ)) μ ((a : ℂ)*μ) + Gamma (q.map (fun z => z-μ)) μ ≤
      1-a*‖μ‖-19*(1-a)/840 ∧
    majorant_Efin (q.map (fun z => z-μ)) μ ((a : ℂ)*μ) + Gamma (q.map (fun z => z-μ)) μ <
      1-a*‖μ‖ := by
  let r := q.map (fun z => z-μ)
  have hM : (7 : ℝ) ≤ q.card := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < q.card := by linarith
  have ha0 : 0 < a := by linarith
  have hh0 : 0 ≤ 1-a := by linarith
  have hh1 : 1-a ≤ 1/10 := by linarith
  have hstats := PaperConsequences.centered_variance_le q μ (by omega) hmean hq
  obtain ⟨hx0,hx1⟩ := abs_le.mp ((Complex.abs_re_le_norm μ).trans hstats.2)
  have hraw := CenteredNearTheorem.raw_of_fullpolar q (by omega) a μ hmean hq hp
  have hμ := PaperConsequences.mean_ne_zero_of_rawPolar hm ha0 ha1 hx0 hx1 rfl hraw
  have hv0 : 0 ≤ variance r := PaperCoefficient.variance_nonneg _
  have hv : (q.card : ℝ)^2*variance r ≤ 1-a := by
    have h := (le_div_iff₀ (sq_pos_of_pos hM0)).mp hstrip
    simpa only [mul_comm] using h
  have ht1 := majorantTail_le_crude r (by simpa [r] using hm) μ a ha0 ha1 hμ hstats.2 hx0 hx1 hstats.1
    (by simpa [r] using hraw)
  have ht2 := crudeTail_le (q.card : ℝ) (1-a) (variance r) hM hh0 hh1 hv0 hv
  have ht : majorantTail r μ ((a : ℂ)*μ) ≤ 3*(1-a)/56 := ht1.trans (by simpa [r] using ht2)
  have hcouple := PaperCenteredVarianceEndpoint.actual_variance_endpoint q μ a (by omega) hmean hq
  have hb1 := PaperPolar.b_lt_one (by omega : 0 < q.card) ha0 ha1 hx0 hx1 hraw
  have hw : ‖1-(a : ℂ)*μ‖ ≤ 1 := by
    nlinarith only [hcouple,hb1,mul_nonneg (sq_nonneg a) hv0,norm_nonneg (1-(a : ℂ)*μ)]
  have hz : ‖(a : ℂ)*μ‖ ≤ 1 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha0]
    exact (mul_le_of_le_one_right ha0.le hstats.2).trans ha1.le
  have hB := norm_B_two_global q.card hm ((a : ℂ)*μ) hz hw
  have hmean2 : 81/400 ≤ ‖μ‖^2 := by
    have hx := (PaperPolar.geometry hm ha0 ha1 hx0 hx1 hraw).1
    nlinarith [Complex.re_le_norm μ]
  have hg := gamma_endpoint_le (q.card : ℝ) (1-a) ‖μ‖ (variance r) ‖B q.card 2 ((a : ℂ)*μ)‖
    hM hh0 hmean2 hv0 hv hB
  have hg' : Gamma r μ*(1+‖B q.card 2 ((a : ℂ)*μ)‖) ≤ 6*(1-a)/7 := by
    simpa only [Gamma,r,Multiset.card_map] using hg
  have he0 := CenteredQuarter.actual_endpoint_quadratic q hm a μ ha0 ha1 hmean hq hx0 hx1 hraw
  have he : ‖1-(a : ℂ)*μ‖^(q.card+1) ≤ (1-a)/15 := by
    have hs := mul_le_mul_of_nonneg_right hh1 hh0
    nlinarith only [he0,hs]
  have hsum : ‖1-(a : ℂ)*μ‖^(q.card+1)+Gamma r μ*‖B q.card 2 ((a : ℂ)*μ)‖+
      majorantTail r μ ((a : ℂ)*μ)+Gamma r μ ≤ (821/840 : ℝ)*(1-a) := by
    nlinarith only [he,hg',ht]
  have hE : majorant_Efin r μ ((a : ℂ)*μ)+Gamma r μ ≤ (821/840 : ℝ)*(1-a) := by
    simpa only [majorant_Efin,majorantTail,r,Multiset.card_map] using hsum
  have hu := mul_le_mul_of_nonneg_left hstats.2 ha0.le
  constructor <;> nlinarith

end Sendov.CenteredThinVariance
