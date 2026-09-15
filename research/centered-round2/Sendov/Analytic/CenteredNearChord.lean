import Sendov.Analytic.CenteredNearScalar

noncomputable section
open scoped BigOperators
namespace Sendov.CenteredNearScalar

/-- Squared norm convexity retains a squared affine chord, not the weaker
chord of beta itself. -/
theorem beta_le_squared_chord (a x t : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hb : PaperPolar.b a x ≤ rho ^ 2) :
    PaperPolar.beta a x t ≤ (1 - (9/11 : ℝ) * t) ^ 2 := by
  have hx2 : x^2 ≤ 1 := by nlinarith
  have hnorm : (1-a*x)^2 ≤ PaperPolar.b a x := by
    unfold PaperPolar.b
    nlinarith only [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hx2)]
  have hleft : 0 ≤ 1-a*x := by nlinarith only [mul_le_mul_of_nonneg_left hx1 ha0, ha1]
  have hcross : 1-a*x ≤ rho := by nlinarith [rho_bounds.1]
  have h1 := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hb)
  have h2 := mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1)) (sub_nonneg.mpr hcross)
  unfold PaperPolar.beta PaperPolar.b rho at *
  nlinarith only [h1, h2]

lemma choose_three_real (m : ℕ) (hm : 3 ≤ m) :
    6 * (m.choose 3 : ℝ) = (m : ℝ) * ((m : ℝ)-1) * ((m : ℝ)-2) := by
  have hn := Nat.descFactorial_eq_factorial_mul_choose m 3
  norm_num [Nat.descFactorial, Nat.factorial] at hn
  have hr := congrArg (fun n : ℕ => (n : ℝ)) hn
  simp only [Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_sub (by omega : 2 ≤ m), Nat.cast_sub (by omega : 1 ≤ m),
    Nat.cast_one] at hr
  nlinarith only [hr]

/-- Exact finite beta control of the cubic affine-chord integral. -/
theorem cubic_chord_integral (m : ℕ) (hm : 3 ≤ m) :
    ((m : ℝ)+1) * (m : ℝ) * ((m : ℝ)-1) * ((m : ℝ)-2) * (9/11 : ℝ)^4 *
      (∫ t in (0 : ℝ)..1, t^3 * (1-(9/11 : ℝ)*t)^(m-3)) ≤ 6 := by
  let c : ℝ := 9/11
  let I : ℝ := ∫ t in (0 : ℝ)..1, t^3 * (1-c*t)^(m-3)
  have hc : 0 < c := by norm_num [c]
  have hcast : (∫ t in (0 : ℝ)..1, (t : ℂ)^3 * (1-(c : ℂ)*t)^(m-3)) = (I : ℂ) := by
    change _ = ((∫ t in (0 : ℝ)..1, t^3 * (1-c*t)^(m-3) : ℝ) : ℂ)
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
  have hH := PaperCenteredCertificate.norm_H_ofReal_le_one m 3 c hm hc.le (by norm_num [c])
  have hweighted : ((m : ℝ)+1) * (m.choose 3 : ℝ) * c^4 * I ≤ 1 := by
    calc
      _ ≤ ((m : ℝ)+1) * (m.choose 3 : ℝ) * c^4 * |I| :=
        mul_le_mul_of_nonneg_left (le_abs_self I) (by positivity)
      _ = ‖PaperCentered.H m 3 (c : ℂ)‖ := hf
      _ ≤ 1 := hH
  have hchoose := choose_three_real m hm
  change ((m : ℝ)+1) * (m : ℝ) * ((m : ℝ)-1) * ((m : ℝ)-2) * c^4 * I ≤ 6
  calc
    _ = ((m : ℝ)+1) * ((m : ℝ) * ((m : ℝ)-1) * ((m : ℝ)-2)) * c^4 * I := by ring
    _ = 6 * (((m : ℝ)+1) * (m.choose 3 : ℝ) * c^4 * I) := by rw [← hchoose]; ring
    _ ≤ 6 := by linarith only [hweighted]

/-- Uniform weighted integral estimate for the original quadratic beta.
The endpoint radius bound is supplied by raw polar and lambda≤4/39. -/
theorem cubic_beta_integral (m : ℕ) (hm : 7 ≤ m) (a x : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hb : PaperPolar.b a x ≤ rho ^ 2) :
    ((m : ℝ)+1) * (m : ℝ) * ((m : ℝ)-1) * ((m : ℝ)-2) * (9/11 : ℝ)^4 *
      (∫ t in (0 : ℝ)..1, t^3 * (Real.sqrt (PaperPolar.beta a x t))^(m-3)) ≤ 6 := by
  have hmR : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hi : (∫ t in (0 : ℝ)..1, t^3 * (Real.sqrt (PaperPolar.beta a x t))^(m-3)) ≤
      ∫ t in (0 : ℝ)..1, t^3 * (1-(9/11 : ℝ)*t)^(m-3) := by
    apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (Continuous.intervalIntegrable (by unfold PaperPolar.beta; fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    intro t ht
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht.1 _)
    apply pow_le_pow_left₀ (Real.sqrt_nonneg _)
    apply (Real.sqrt_le_left (by nlinarith [ht.2] : 0 ≤ 1-(9/11 : ℝ)*t)).2
    exact beta_le_squared_chord a x t ha0 ha1 hx0 hx1 ht.1 ht.2 hb
  have hc0 : 0 ≤ ((m : ℝ)+1) * (m : ℝ) * ((m : ℝ)-1) * ((m : ℝ)-2) * (9/11 : ℝ)^4 := by
    have h1 : 0 ≤ (m : ℝ)-1 := by linarith
    have h2 : 0 ≤ (m : ℝ)-2 := by linarith
    positivity
  exact (mul_le_mul_of_nonneg_left hi hc0).trans (cubic_chord_integral m (by omega))

end Sendov.CenteredNearScalar
