import Sendov.Analytic.CenteredBandTheorem

noncomputable section
namespace Sendov.CenteredBand
open PaperCentered PaperCenteredBound CenteredActualTail

/-- Exact radical-free quantity for a supplied polynomial-integral bound I. -/
def tailSquare (U : ℕ) (X I : ℝ) : ℝ :=
  CenteredThird.weightSum U * ((U : ℝ) + 1)^2 * (U.descFactorial 3 : ℝ) *
    I^2 * X^2 * (1 - X^2)

lemma tail_expression_sq (U : ℕ) (X I : ℝ) (hU : 3 ≤ U) (hX : X^2 ≤ 1) :
    (tailFactor U * I * X * Real.sqrt (1 - X^2))^2 = tailSquare U X I := by
  have hs : 0 ≤ CenteredThird.weightSum U * (U.descFactorial 3 : ℝ) :=
    mul_nonneg (CenteredThird.weightSum_nonneg U hU) (Nat.cast_nonneg _)
  simp only [tailFactor, tailSquare, mul_pow, Real.sq_sqrt hs,
    Real.sq_sqrt (sub_nonneg.mpr hX)]
  ring

/-- Named scalar certificate interface: a polynomial integral bound and an
exact squared scalar comparison suffice. This contains no C, H, E or Gamma. -/
theorem tailConstant_le_of_certificate (p U : ℕ) (X I tau : ℝ)
    (hU : 3 ≤ U) (hX0 : 0 ≤ X) (hX1 : X^2 ≤ 1) (htau0 : 0 ≤ tau)
    (hI : curvedIntegral p X ≤ I) (hsquare : tailSquare U X I ≤ tau^2) :
    tailConstant p U X ≤ tau := by
  have he := tail_expression_sq U X I hU hX1
  have hc : tailFactor U * I * X * Real.sqrt (1 - X^2) ≤ tau := by
    nlinarith only [he, hsquare, htau0]
  have hmul := mul_le_mul_of_nonneg_left hI
    (mul_nonneg (mul_nonneg (tailFactor_nonneg U) hX0) (Real.sqrt_nonneg (1 - X^2)))
  unfold tailConstant
  nlinarith only [hc, hmul]

/-- Original actual mean and variance wrapper: no free scalar variance proxy. -/
theorem original_tail_le_band (q : Multiset ℂ) (L U p : ℕ) (a : ℝ) (μ : ℂ) (X tau : ℝ)
    (hL : 7 ≤ L) (hLp : L = 2*p+3) (hLm : L ≤ q.card) (hmU : q.card ≤ U)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hmean : q.sum = q.card*μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1) (hX0 : 0 < X) (hhalf : 1/2 ≤ X^2)
    (hX1 : X ≤ 19/20) (hx : X ≤ μ.re) (htau : tailConstant p U X ≤ tau) :
    majorantTail (q.map (fun z => z-μ)) μ ((a : ℂ)*μ) ≤
      tau * variance (q.map (fun z => z-μ)) := by
  have hstats := PaperConsequences.centered_variance_le q μ (by omega) hmean hq
  exact actual_tail_le _ p U μ a X tau
    (by simpa only [Multiset.card_map, ← hLp] using hLm)
    (by simpa only [Multiset.card_map] using hmU) ha0 ha1 hX0 hhalf
    (by nlinarith) hx hstats.1 htau

/-- Single generic consumer for the scalar integral certificate and the proved
real-part lower bound. No per-degree theorem, table or coefficient certificate. -/
theorem C_near_fullpolar_band_of_certificate
    (q : Multiset ℂ) (L U p : ℕ) (a : ℝ) (μ : ℂ) (X I tau : ℝ)
    (hL : 7 ≤ L) (hLp : L = 2*p+3) (hLm : L ≤ q.card) (hmU : q.card ≤ U)
    (ha0 : 9/10 ≤ a) (ha1 : a < 1) (hmean : q.sum = q.card*μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1)
    (hp : 1 ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun z => (a : ℂ)+(t : ℂ)*(1-(a : ℂ)^2)*z)).prod‖)
    (hX0 : 0 < X) (hhalf : 1/2 ≤ X^2) (hX1 : X ≤ 19/20)
    (hx : X ≤ μ.re) (htau0 : 0 ≤ tau)
    (hI : curvedIntegral p X ≤ I) (hsquare : tailSquare U X I ≤ tau^2)
    (hdelta : 0 < margin L U X (BConstant p U X) tau) :
    majorantTail (q.map (fun z => z-μ)) μ ((a : ℂ)*μ) ≤
      tau * variance (q.map (fun z => z-μ)) ∧
    majorant_Efin (q.map (fun z => z-μ)) μ ((a : ℂ)*μ) +
      Gamma (q.map (fun z => z-μ)) μ ≤
      1-a*‖μ‖-margin L U X (BConstant p U X) tau*(1-a) ∧
    majorant_Efin (q.map (fun z => z-μ)) μ ((a : ℂ)*μ) +
      Gamma (q.map (fun z => z-μ)) μ < 1-a*‖μ‖ := by
  have htau := tailConstant_le_of_certificate p U X I tau (by omega) hX0.le
    (by nlinarith) htau0 hI hsquare
  exact ⟨original_tail_le_band q L U p a μ X tau hL hLp hLm hmU
      (by linarith) ha1.le hmean hq hX0 hhalf hX1 hx htau,
    C_near_fullpolar_band q L U p a μ X tau hL hLp hLm hmU ha0 ha1 hmean hq hp
      hX0 hhalf hX1 hx htau hdelta⟩

end Sendov.CenteredBand
