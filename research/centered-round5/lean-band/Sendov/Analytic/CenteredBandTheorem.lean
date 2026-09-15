import Sendov.Analytic.CenteredBandEndpoint

noncomputable section
open scoped BigOperators
namespace Sendov.CenteredBand
open PaperCentered PaperCenteredBound CenteredActualTail

/-- Quantitative degree-band criterion on the actual original complex data.
The mean lower bound is the outstanding endpoint-moment interface; htau is
one explicit scalar polynomial-integral certificate for the whole band.
Neither is the requested C budget. No real-mean or saturated-statistics premise occurs. -/
theorem C_near_raw_band (q : Multiset ℂ) (L U p : ℕ) (a : ℝ) (μ : ℂ) (X tau : ℝ)
    (hL : 7 ≤ L) (hLp : L = 2*p+3) (hLm : L ≤ q.card) (hmU : q.card ≤ U)
    (ha0 : 9/10 ≤ a) (ha1 : a < 1) (hmean : q.sum = q.card*μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1) (hp : PaperPolar.RawPolar q.card a μ.re)
    (hX0 : 0 < X) (hhalf : 1/2 ≤ X^2) (hX1 : X ≤ 19/20)
    (hx : X ≤ μ.re) (htau : tailConstant p U X ≤ tau) :
    majorant_Efin (q.map (fun z => z-μ)) μ ((a:ℂ)*μ) +
      Gamma (q.map (fun z => z-μ)) μ ≤
      1-a*‖μ‖-margin L U X (BConstant p U X) tau*(1-a) := by
  let r := q.map (fun z => z-μ)
  have hm : 7 ≤ q.card := hL.trans hLm
  have ha : 0 < a := by linarith
  have hstats := PaperConsequences.centered_variance_le q μ (by omega) hmean hq
  obtain ⟨hx0, hx1⟩ := abs_le.mp ((Complex.abs_re_le_norm μ).trans hstats.2)
  have hv0 : 0 ≤ variance r := PaperCoefficient.variance_nonneg r
  have hXu : X ≤ ‖μ‖ := hx.trans (Complex.re_le_norm μ)
  have hXsq : X^2 ≤ 1 := by nlinarith
  have hXhalf : 1/2 ≤ X := by nlinarith
  have htail := actual_tail_le r p U μ a X tau
    (by simpa [r, hLp] using hLm) (by simpa [r] using hmU)
    ha.le ha1.le hX0 hhalf hXsq hx hstats.1 htau
  have hvar := CenteredNearScalar.actual_variance_le_lambda_third q hm a μ ha ha1 hmean hq hx0 hx1 hp
  have hcap : variance r ≤ ((U:ℝ)/3)*(1-a) := by
    have hmU' : (q.card:ℝ) ≤ U := by exact_mod_cast hmU
    have ht := mul_le_mul_of_nonneg_right hmU' (show 0 ≤ 1-a by linarith)
    dsimp [r]
    linarith
  have he0 := CenteredQuarter.actual_endpoint_quadratic q hm a μ ha ha1 hmean hq hx0 hx1 hp
  have he : ‖1-(a:ℂ)*μ‖^(q.card+1) ≤ (1-a)/15 := by
    have ht := mul_nonneg (show 0 ≤ 1-a by linarith) (show 0 ≤ a-9/10 by linarith)
    nlinarith only [he0, ht]
  have hz : ‖(a:ℂ)*μ‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    exact (mul_le_of_le_one_right ha.le hstats.2).trans ha1.le
  have hw2 := PaperCenteredVarianceEndpoint.actual_variance_endpoint q μ a (by omega) hmean hq
  have hwb := endpoint_quadratic_le a μ.re X ha0 ha1.le hx hX1
  have hw : ‖1-(a:ℂ)*μ‖^2 ≤ 2*(1-X) := by
    have hn := mul_nonneg (sq_nonneg a) hv0
    change 0 ≤ a^2*variance (q.map (fun z => z-μ)) at hn
    linarith
  have hB := norm_B_two_le_band q.card p U hm (by omega) hmU ((a:ℂ)*μ) X hXhalf (by linarith) hz hw
  have hLr : (1:ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hLm' : (L:ℝ) ≤ q.card := by exact_mod_cast hLm
  have hs := scalar_budget L U q.card a X ‖μ‖ (variance r)
    (‖1-(a:ℂ)*μ‖^(q.card+1)) (‖B q.card 2 ((a:ℂ)*μ)‖)
    (BConstant p U X) (majorantTail r μ ((a:ℂ)*μ)) tau
    hLr hLm' ha1.le hX0 hstats.2 hXu hv0 (by linarith [hstats.1])
    hcap he (norm_nonneg _) hB htail
  simp only [majorant_Efin, Gamma, majorantTail] at hs ⊢
  simp only [r, Multiset.card_map] at hs ⊢
  convert hs using 1 <;> ring

/-- Original FULLpolar degree-band C-near, including variance zero and all
lambda values. Its only unproved analytic input is the stronger mean bound hx;
the band integral comparison and every original-C/B term are proved above. -/
theorem C_near_fullpolar_band (q : Multiset ℂ) (L U p : ℕ) (a : ℝ) (μ : ℂ) (X tau : ℝ)
    (hL : 7 ≤ L) (hLp : L = 2*p+3) (hLm : L ≤ q.card) (hmU : q.card ≤ U)
    (ha0 : 9/10 ≤ a) (ha1 : a < 1) (hmean : q.sum = q.card*μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1)
    (hp : 1 ≤ ‖∫ t in (0:ℝ)..1,
      (q.map (fun z => (a:ℂ)+(t:ℂ)*(1-(a:ℂ)^2)*z)).prod‖)
    (hX0 : 0 < X) (hhalf : 1/2 ≤ X^2) (hX1 : X ≤ 19/20)
    (hx : X ≤ μ.re) (htau : tailConstant p U X ≤ tau)
    (hdelta : 0 < margin L U X (BConstant p U X) tau) :
    majorant_Efin (q.map (fun z => z-μ)) μ ((a:ℂ)*μ) +
      Gamma (q.map (fun z => z-μ)) μ ≤
      1-a*‖μ‖-margin L U X (BConstant p U X) tau*(1-a) ∧
    majorant_Efin (q.map (fun z => z-μ)) μ ((a:ℂ)*μ) +
      Gamma (q.map (fun z => z-μ)) μ < 1-a*‖μ‖ := by
  have hraw := CenteredNearTheorem.raw_of_fullpolar q (by omega) a μ hmean hq hp
  have h := C_near_raw_band q L U p a μ X tau hL hLp hLm hmU ha0 ha1 hmean hq
    hraw hX0 hhalf hX1 hx htau
  have hpos := mul_pos hdelta (sub_pos.mpr ha1)
  exact ⟨h, by linarith⟩

end Sendov.CenteredBand
