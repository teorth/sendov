import Sendov.Analytic.CenteredBandScalar

noncomputable section
namespace Sendov.CenteredBand
open PaperCentered PaperCenteredBound CenteredActualTail

lemma curved_quadratic_nonneg (X y : ℝ) (hX : X^2 ≤ 1) :
    0 ≤ 1-2*X*y+y^2 := by nlinarith [sq_nonneg (y-X)]

lemma curved_quadratic_le_one (X y : ℝ) (hX : 1/2 ≤ X)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 1-2*X*y+y^2 ≤ 1 := by
  have h := mul_nonneg hy0 (show 0 ≤ 2*X-y by linarith)
  nlinarith only [h]

lemma curvedIntegral_nonneg (p : ℕ) (X : ℝ) (hX : X^2 ≤ 1) :
    0 ≤ curvedIntegral p X := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro y hy
  exact mul_nonneg (pow_nonneg hy.1 _) (pow_nonneg (curved_quadratic_nonneg X y hX) _)

/-- The a^4 factor is cancelled exactly by y=a*t, before interval enlargement.
The lower endpoint is represented as L=2p+3 so the remaining integral is polynomial. -/
theorem cubicIntegral_le_curved (m p : ℕ) (a x X : ℝ)
    (hmp : 2*p+3 ≤ m) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : X ≤ x) (hX0 : 1/2 ≤ X) (hX1 : X^2 ≤ 1) :
    a^4*(∫ t in (0:ℝ)..1, t^3*(Real.sqrt (PaperPolar.beta a x t))^(m-3)) ≤
      curvedIntegral p X := by
  let f : ℝ → ℝ := fun y => y^3*(1-2*X*y+y^2)^p
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hpoint : (∫ t in (0:ℝ)..1, t^3*(Real.sqrt (PaperPolar.beta a x t))^(m-3)) ≤
      ∫ t in (0:ℝ)..1, t^3*(1-2*X*(a*t)+(a*t)^2)^p := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (Continuous.intervalIntegrable (by unfold PaperPolar.beta; fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    intro t ht
    have hy0 : 0 ≤ a*t := mul_nonneg ha0 ht.1
    have hy1 : a*t ≤ 1 := (mul_le_of_le_one_right ha0 ht.2).trans ha1
    have hq0 := curved_quadratic_nonneg X (a*t) hX1
    have hq1 := curved_quadratic_le_one X (a*t) hX0 hy0 hy1
    have hb : PaperPolar.beta a x t ≤ 1-2*X*(a*t)+(a*t)^2 := by
      have h := mul_le_mul_of_nonneg_right hx hy0
      unfold PaperPolar.beta
      nlinarith only [h]
    have hs := Real.sqrt_le_sqrt hb
    have hs1 : Real.sqrt (1-2*X*(a*t)+(a*t)^2) ≤ 1 := by
      exact (Real.sqrt_le_sqrt hq1).trans_eq (by norm_num)
    have hp1 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs (m-3)
    have hp2 := pow_le_pow_of_le_one (Real.sqrt_nonneg _) hs1 (show 2*p ≤ m-3 by omega)
    have hid : (Real.sqrt (1-2*X*(a*t)+(a*t)^2))^(2*p) =
        (1-2*X*(a*t)+(a*t)^2)^p := by rw [pow_mul, Real.sq_sqrt hq0]
    rw [hid] at hp2
    exact mul_le_mul_of_nonneg_left (hp1.trans hp2) (pow_nonneg ht.1 _)
  have hchange : a^4*(∫ t in (0:ℝ)..1, t^3*(1-2*X*(a*t)+(a*t)^2)^p) =
      ∫ y in (0:ℝ)..a, f y := by
    have h := intervalIntegral.smul_integral_comp_mul_left (a := (0:ℝ)) (b := 1) f a
    simp only [smul_eq_mul, mul_zero, mul_one] at h
    rw [← h, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [f]
    ring
  have hext : (∫ y in (0:ℝ)..a, f y) ≤ curvedIntegral p X := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hf.intervalIntegrable 0 a) (hf.intervalIntegrable a 1)
    have hnon : 0 ≤ ∫ y in a..1, f y := by
      apply intervalIntegral.integral_nonneg ha1
      intro y hy
      dsimp [f]
      exact mul_nonneg (pow_nonneg (ha0.trans hy.1) _) (pow_nonneg (curved_quadratic_nonneg X y hX1) _)
    change (∫ y in (0:ℝ)..a, f y) ≤ ∫ y in (0:ℝ)..1, f y
    linarith
  exact (mul_le_mul_of_nonneg_left hpoint (pow_nonneg ha0 _)).trans (hchange.le.trans hext)

def tailFactor (U : ℕ) : ℝ :=
  ((U:ℝ)+1)*Real.sqrt (CenteredThird.weightSum U*(U.descFactorial 3:ℝ))

def tailConstant (p U : ℕ) (X : ℝ) : ℝ :=
  tailFactor U * curvedIntegral p X * X * Real.sqrt (1-X^2)

lemma tailFactor_nonneg (U : ℕ) : 0 ≤ tailFactor U := by unfold tailFactor; positivity

lemma tailFactor_mono (m U : ℕ) (hm : 3 ≤ m) (hmU : m ≤ U) :
    tailFactor m ≤ tailFactor U := by
  have hdesc : (m.descFactorial 3:ℝ) ≤ (U.descFactorial 3:ℝ) := by
    exact_mod_cast Nat.descFactorial_le 3 hmU
  have hs := Real.sqrt_le_sqrt (mul_le_mul (weightSum_mono m U hm hmU) hdesc
    (Nat.cast_nonneg _) (CenteredThird.weightSum_nonneg U (by omega)))
  apply mul_le_mul (by exact_mod_cast Nat.add_le_add_right hmU 1) hs
    (Real.sqrt_nonneg _) (by positivity)

/-- The unchanged original square-root-C tail is controlled by one band integral.
No tail or final-budget inequality is assumed. All means may be complex. -/
theorem actual_tail_le (r : Multiset ℂ) (p U : ℕ) (μ : ℂ) (a X tau : ℝ)
    (hm : 2*p+3 ≤ r.card) (hmU : r.card ≤ U) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hX0 : 0 < X) (hhalf : 1/2 ≤ X^2) (hX1 : X^2 ≤ 1)
    (hx : X ≤ μ.re) (hv : variance r ≤ 1-‖μ‖^2)
    (htau : tailConstant p U X ≤ tau) :
    majorantTail r μ ((a:ℂ)*μ) ≤ tau * variance r := by
  have hXu : X ≤ ‖μ‖ := hx.trans (Complex.re_le_norm μ)
  have hμ : μ ≠ 0 := by
    intro he
    simpa [he] using (hX0.trans_le hXu)
  have hXhalf : 1/2 ≤ X := by nlinarith
  have hi := cubicIntegral_le_curved r.card p a μ.re X hm ha0 ha1 hx hXhalf hX1
  have hv0 : 0 ≤ variance r := PaperCoefficient.variance_nonneg r
  have hu := mean_sqrt_variance X ‖μ‖ (variance r) hX0.le hhalf hXu hv0 (by linarith)
  have hsqrt : Real.sqrt ((variance r)^3) = variance r*Real.sqrt (variance r) := by
    rw [show (variance r)^3 = (variance r)^2*variance r by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hv0]
  have htail := CenteredThird.majorantTail_le_cubicIntegral_finite r (by omega) μ a ha0 hμ hv
  rw [hsqrt] at htail
  have h1 := mul_le_mul_of_nonneg_left hi
    (show 0 ≤ tailFactor r.card*‖μ‖*variance r*Real.sqrt (variance r) by
      exact mul_nonneg (mul_nonneg (mul_nonneg (tailFactor_nonneg _) (norm_nonneg _)) hv0) (Real.sqrt_nonneg _))
  have h2 := mul_le_mul_of_nonneg_left hu
    (mul_nonneg (mul_nonneg (tailFactor_nonneg r.card) (curvedIntegral_nonneg p X hX1)) hv0)
  have h3 := mul_le_mul_of_nonneg_right (tailFactor_mono r.card U (by omega) hmU)
    (show 0 ≤ curvedIntegral p X*X*Real.sqrt (1-X^2)*variance r by
      exact mul_nonneg (mul_nonneg (mul_nonneg (curvedIntegral_nonneg p X hX1) hX0.le) (Real.sqrt_nonneg _)) hv0)
  have h4 := mul_le_mul_of_nonneg_right htau hv0
  simp only [tailConstant, tailFactor] at h1 h2 h3 h4
  nlinarith only [htail, h1, h2, h3, h4]

end Sendov.CenteredBand
