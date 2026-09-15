import Sendov.Analytic.CenteredThirdActual
import Sendov.Analytic.CenteredThirdEndpoint

noncomputable section
open scoped BigOperators
namespace Sendov.CenteredThird
open PaperCentered PaperCenteredBound CenteredActualTail

/-- Original-C near extension on the closed interval [1/4,1/3].
All coefficient, endpoint, variance and tail bounds are discharged. -/
theorem C_near_raw_middle (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hmean : q.sum = q.card*μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1) (hp : PaperPolar.RawPolar q.card a μ.re)
    (hl0 : 1/4 ≤ PaperPolar.lambda q.card a) (hl1 : PaperPolar.lambda q.card a ≤ 1/3) :
    majorant_Efin (q.map (fun z => z-μ)) μ ((a:ℂ)*μ) +
      Gamma (q.map (fun z => z-μ)) μ ≤ 1-a*‖μ‖-37*(1-a)/819 := by
  let r := q.map (fun z => z-μ)
  have hstats := PaperConsequences.centered_variance_le q μ (by omega) hmean hq
  obtain ⟨hx0, hx1⟩ := abs_le.mp ((Complex.abs_re_le_norm μ).trans hstats.2)
  have hμ := PaperConsequences.mean_ne_zero_of_rawPolar hm ha0 ha1 hx0 hx1 rfl hp
  obtain ⟨hh, hu, hb, hv1, hv, hw⟩ := actual_third_facts q hm a μ ha0 ha1 hmean hq hx0 hx1 hp hl1
  have hz : ‖(a:ℂ)*μ‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
    exact (mul_le_of_le_one_right ha0.le hstats.2).trans ha1.le
  have hB := norm_B_two_le q.card hm ((a:ℂ)*μ) hz hw
  have he0 := CenteredQuarter.actual_endpoint_quadratic q hm a μ ha0 ha1 hmean hq hx0 hx1 hp
  have hbc : PaperPolar.b a μ.re ≤ (1-(41/60:ℝ))^2 := hb.trans (by norm_num)
  have htail := majorantTail_le_finiteChord r (by simpa [r] using hm) μ a (41/60)
    ha0.le ha1.le hμ hx0 hx1 hstats.1 (by norm_num) (by norm_num) hbc
  have ht : (∑ k ∈ Finset.Ico 3 (q.card+1),
      C q.card k (variance r)/((q.card.choose k:ℝ)*‖μ‖^k)*‖H q.card k ((a:ℂ)*μ)‖) ≤
      chordTail q.card a ‖μ‖ (variance r) := by
    simpa only [majorantTail, r, Multiset.card_map, chordTail] using htail
  have hs := scalar_budget q.card a (1-a) ‖μ‖ (variance r) _ _ _ hm
    (by linarith) hh (by ring) hl0 hl1 hu
    (by linarith [hstats.1]) (PaperCoefficient.variance_nonneg _) hv1 hv he0 hB ht
  unfold majorant_Efin Gamma
  simp only [Multiset.card_map]
  convert hs using 1 <;> ring

/-- Uniform quantitative C-near for lambda≤1/3, including the old quarter domain. -/
theorem C_near_raw_third (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hmean : q.sum = q.card*μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1) (hp : PaperPolar.RawPolar q.card a μ.re)
    (hl : PaperPolar.lambda q.card a ≤ 1/3) :
    majorant_Efin (q.map (fun z => z-μ)) μ ((a:ℂ)*μ) +
      Gamma (q.map (fun z => z-μ)) μ ≤ 1-a*‖μ‖-37*(1-a)/819 := by
  by_cases hqtr : PaperPolar.lambda q.card a ≤ 1/4
  · have h := CenteredQuarterTheorem.C_near_raw_quarter q hm a μ ha0 ha1 hmean hq hp hqtr
    linarith
  · exact C_near_raw_middle q hm a μ ha0 ha1 hmean hq hp (le_of_not_ge hqtr) hl

/-- FULLpolar original-C consumer, with no tail-budget premise and no extra
variance/real-mean/saturation premise. The margin includes v=0. -/
theorem C_near_fullpolar_third (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hmean : q.sum = q.card*μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1)
    (hp : 1 ≤ ‖∫ t in (0:ℝ)..1,
      (q.map (fun z => (a:ℂ)+(t:ℂ)*(1-(a:ℂ)^2)*z)).prod‖)
    (hl : PaperPolar.lambda q.card a ≤ 1/3) :
    majorant_Efin (q.map (fun z => z-μ)) μ ((a:ℂ)*μ) + Gamma (q.map (fun z => z-μ)) μ ≤
      1-a*‖μ‖-37*(1-a)/819 ∧
    majorant_Efin (q.map (fun z => z-μ)) μ ((a:ℂ)*μ) + Gamma (q.map (fun z => z-μ)) μ <
      1-a*‖μ‖ := by
  have hraw := CenteredNearTheorem.raw_of_fullpolar q (by omega) a μ hmean hq hp
  have h := C_near_raw_third q hm a μ ha0 ha1 hmean hq hraw hl
  exact ⟨h, by linarith⟩

/-- Direct norm obstruction for the original full complex product integral. -/
theorem norm_J_gt_one_fullpolar_third (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hmean : q.sum = q.card*μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1)
    (hp : 1 ≤ ‖∫ t in (0:ℝ)..1,
      (q.map (fun z => (a:ℂ)+(t:ℂ)*(1-(a:ℂ)^2)*z)).prod‖)
    (hl : PaperPolar.lambda q.card a ≤ 1/3) :
    1 < ‖(q.card+1:ℂ)*(∫ t in (0:ℝ)..1, (q.map (fun z => 1-(a:ℂ)*t*z)).prod)‖ := by
  have hraw := CenteredNearTheorem.raw_of_fullpolar q (by omega) a μ hmean hq hp
  have hu := (PaperConsequences.centered_variance_le q μ (by omega) hmean hq).2
  obtain ⟨hx0, hx1⟩ := abs_le.mp ((Complex.abs_re_le_norm μ).trans hu)
  have hμ := PaperConsequences.mean_ne_zero_of_rawPolar hm ha0 ha1 hx0 hx1 rfl hraw
  exact PaperCenteredBound.C_budget q a μ (by omega) ha0.le hmean hμ
    (C_near_fullpolar_third q hm a μ ha0 ha1 hmean hq hp hl).2

end Sendov.CenteredThird
