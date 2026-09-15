import Sendov.Analytic.CenteredActualTail

noncomputable section
open scoped BigOperators
namespace Sendov.CenteredChordGeneral
open PaperCentered PaperCenteredBound CenteredActualTail

lemma beta_le_squared_chord (a x t R : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hR : 0 ≤ R) (hb : PaperPolar.b a x ≤ R^2) :
    PaperPolar.beta a x t ≤ (1-(1-R)*t)^2 := by
  have hx2 : x^2 ≤ 1 := by nlinarith
  have hnorm : (1-a*x)^2 ≤ PaperPolar.b a x := by
    unfold PaperPolar.b
    nlinarith only [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hx2)]
  have hleft : 0 ≤ 1-a*x := by nlinarith only [mul_le_mul_of_nonneg_left hx1 ha0, ha1]
  have hcross : 1-a*x ≤ R := by nlinarith
  have h1 := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hb)
  have h2 := mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1)) (sub_nonneg.mpr hcross)
  unfold PaperPolar.beta PaperPolar.b at *
  nlinarith only [h1, h2]

lemma cubic_chord_integral (m : ℕ) (hm : 3 ≤ m) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ((m : ℝ)+1)*(m : ℝ)*((m : ℝ)-1)*((m : ℝ)-2)*c^4 *
      (∫ t in (0 : ℝ)..1, t^3*(1-c*t)^(m-3)) ≤ 6 := by
  let I : ℝ := ∫ t in (0 : ℝ)..1, t^3*(1-c*t)^(m-3)
  have hcast : (∫ t in (0 : ℝ)..1, (t : ℂ)^3*(1-(c : ℂ)*t)^(m-3)) = (I : ℂ) := by
    change _ = ((∫ t in (0 : ℝ)..1, t^3*(1-c*t)^(m-3) : ℝ) : ℂ)
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro t ht
    push_cast
    ring
  have hf := congrArg norm (PaperCentered.finite_beta m 3 hm (c : ℂ))
  have hmnorm : ‖(m : ℂ)+1‖ = (m : ℝ)+1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (m+1)
  rw [hcast] at hf
  simp only [norm_mul, norm_pow, hmnorm, Complex.norm_natCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] at hf
  have hH := PaperCenteredCertificate.norm_H_ofReal_le_one m 3 c hm hc.le hc1
  have hweighted : ((m : ℝ)+1)*(m.choose 3 : ℝ)*c^4*I ≤ 1 := by
    calc
      _ ≤ ((m : ℝ)+1)*(m.choose 3 : ℝ)*c^4*|I| :=
        mul_le_mul_of_nonneg_left (le_abs_self I) (by positivity)
      _ = ‖PaperCentered.H m 3 (c : ℂ)‖ := hf
      _ ≤ 1 := hH
  have hchoose := CenteredNearScalar.choose_three_real m hm
  change ((m : ℝ)+1)*(m : ℝ)*((m : ℝ)-1)*((m : ℝ)-2)*c^4*I ≤ 6
  calc
    _ = ((m : ℝ)+1)*((m : ℝ)*((m : ℝ)-1)*((m : ℝ)-2))*c^4*I := by ring
    _ = 6*(((m : ℝ)+1)*(m.choose 3 : ℝ)*c^4*I) := by rw [← hchoose]; ring
    _ ≤ 6 := by linarith only [hweighted]

lemma cubic_beta_integral (m : ℕ) (hm : 7 ≤ m) (a x c : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hc : 0 < c) (hc1 : c ≤ 1) (hb : PaperPolar.b a x ≤ (1-c)^2) :
    ((m : ℝ)+1)*(m : ℝ)*((m : ℝ)-1)*((m : ℝ)-2)*c^4 *
      (∫ t in (0 : ℝ)..1, t^3*(Real.sqrt (PaperPolar.beta a x t))^(m-3)) ≤ 6 := by
  have hmR : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hi : (∫ t in (0 : ℝ)..1, t^3*(Real.sqrt (PaperPolar.beta a x t))^(m-3)) ≤
      ∫ t in (0 : ℝ)..1, t^3*(1-c*t)^(m-3) := by
    apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (Continuous.intervalIntegrable (by unfold PaperPolar.beta; fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    intro t ht
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht.1 _)
    apply pow_le_pow_left₀ (Real.sqrt_nonneg _)
    have hct : c*t ≤ 1 := (mul_le_of_le_one_right hc.le ht.2).trans hc1
    apply (Real.sqrt_le_left (sub_nonneg.mpr hct)).2
    simpa only [sub_sub_cancel] using
      beta_le_squared_chord a x t (1-c) ha0 ha1 hx0 hx1 ht.1 ht.2 (by linarith) hb
  have hc0 : 0 ≤ ((m : ℝ)+1)*(m : ℝ)*((m : ℝ)-1)*((m : ℝ)-2)*c^4 := by
    have h1 : 0 ≤ (m : ℝ)-1 := by linarith
    have h2 : 0 ≤ (m : ℝ)-2 := by linarith
    positivity
  exact (mul_le_mul_of_nonneg_left hi hc0).trans (cubic_chord_integral m (by omega) c hc hc1)

/-- A uniform, all-degree closed chord bound for the original majorant tail.
It retains a^4 and the actual norm of the mean. -/
theorem majorantTail_le_chordScalar (r : Multiset ℂ) (hm : 7 ≤ r.card) (μ : ℂ) (a c : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hμ : μ ≠ 0)
    (hx0 : -1 ≤ μ.re) (hx1 : μ.re ≤ 1) (hv : variance r ≤ 1 - ‖μ‖^2)
    (hc : 0 < c) (hc1 : c ≤ 1) (hb : PaperPolar.b a μ.re ≤ (1-c)^2) :
    majorantTail r μ ((a : ℂ)*μ) ≤
      9*a^4*‖μ‖*Real.sqrt ((variance r)^3) /
        (c^4*Real.sqrt ((r.card : ℝ)*((r.card : ℝ)-1)*((r.card : ℝ)-2))) := by
  let M : ℝ := r.card
  let D : ℝ := M*(M-1)*(M-2)
  let I : ℝ := ∫ t in (0 : ℝ)..1, t^3*(Real.sqrt (PaperPolar.beta a μ.re t))^(r.card-3)
  have hM : 7 ≤ M := by dsimp [M]; exact_mod_cast hm
  have hM0 : 0 < M := by linarith
  have hM1 : 0 < M-1 := by linarith
  have hM2 : 0 < M-2 := by linarith
  have hD0 : 0 < D := by dsimp [D]; positivity
  have hdesc : (r.card.descFactorial 3 : ℝ) = D :=
    PaperFactorialTail.cast_descFactorial_three r.card (by omega)
  have hs : Real.sqrt ((9/4)*(r.card.descFactorial 3 : ℝ)) = (3/2)*Real.sqrt D := by
    have hroot : Real.sqrt (9/4 : ℝ) = 3/2 :=
      (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
    rw [hdesc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9/4), hroot]
  have ht := majorantTail_le_cubicIntegral r (by omega) μ a ha0 hμ hv
  rw [hs] at ht
  have hib := cubic_beta_integral r.card hm a μ.re c ha0 ha1 hx0 hx1 hc hc1 hb
  have hden : 0 < (M+1)*D*c^4 := by positivity
  have hi : I ≤ 6/((M+1)*D*c^4) := by
    apply (le_div_iff₀ hden).2
    change (M+1)*M*(M-1)*(M-2)*c^4*I ≤ 6 at hib
    dsimp [D]
    nlinarith only [hib]
  have hmul := mul_le_mul_of_nonneg_left hi
    (show 0 ≤ (M+1)*a^4*‖μ‖*((3/2)*Real.sqrt D)*Real.sqrt ((variance r)^3) by positivity)
  apply ht.trans
  apply hmul.trans_eq
  change ((M+1)*a^4*‖μ‖*((3/2)*Real.sqrt D)*Real.sqrt ((variance r)^3)) *
      (6/((M+1)*D*c^4)) = 9*a^4*‖μ‖*Real.sqrt ((variance r)^3)/(c^4*Real.sqrt D)
  have hsn : Real.sqrt D ≠ 0 := (Real.sqrt_pos.mpr hD0).ne'
  have hmn : M+1 ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt hD0.le]
  ring

end Sendov.CenteredChordGeneral
