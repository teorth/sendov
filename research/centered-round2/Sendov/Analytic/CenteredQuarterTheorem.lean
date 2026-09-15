import Sendov.Analytic.CenteredQuarterActual
import Sendov.Analytic.CenteredChordGeneral
import Sendov.Analytic.CenteredNearTheorem

/-! Original-C quarter-lambda budget, with the analytic tail fully discharged. -/
noncomputable section
open scoped BigOperators
namespace Sendov.CenteredQuarterTheorem
open PaperCentered PaperCenteredBound CenteredActualTail

/-- Quantitative C-near on actual raw-polar data for every m≥7, lambda≤1/4. -/
theorem C_near_raw_quarter (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hmean : q.sum = q.card * μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1) (hp : PaperPolar.RawPolar q.card a μ.re)
    (hl : PaperPolar.lambda q.card a ≤ 1 / 4) :
    majorant_Efin (q.map (fun z => z-μ)) μ ((a : ℂ)*μ) + Gamma (q.map (fun z => z-μ)) μ ≤
      1-a*‖μ‖-79*(1-a)/504 := by
  let r := q.map (fun z => z-μ)
  have hstats := PaperConsequences.centered_variance_le q μ (by omega) hmean hq
  obtain ⟨hx0, hx1⟩ := abs_le.mp ((Complex.abs_re_le_norm μ).trans hstats.2)
  have hμ := PaperConsequences.mean_ne_zero_of_rawPolar hm ha0 ha1 hx0 hx1 rfl hp
  have hf := CenteredQuarter.actual_quarter_facts q hm a μ ha0 ha1 hmean hq hx0 hx1 hp hl
  have hb : PaperPolar.b a μ.re ≤ (1-(13/18 : ℝ))^2 :=
    hf.2.2.1.trans (by norm_num)
  have ht := CenteredChordGeneral.majorantTail_le_chordScalar r (by simpa [r] using hm) μ a (13/18)
    ha0.le ha1.le hμ hx0 hx1 hstats.1 (by norm_num) (by norm_num) hb
  apply CenteredQuarter.actual_C_quarter_budget q hm a μ ha0 ha1 hmean hq hx0 hx1 hp hl
  simpa only [majorantTail, r, Multiset.card_map, CenteredQuarter.chordTail] using ht

/-- The original FULLpolar and pointwise hypotheses, with no tail/variance
budget premise. Positive variance and nonreal means are unrestricted. -/
theorem C_near_fullpolar_quarter (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hmean : q.sum = q.card * μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1)
    (hp : 1 ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun z => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ)^2) * z)).prod‖)
    (hl : PaperPolar.lambda q.card a ≤ 1 / 4) :
    majorant_Efin (q.map (fun z => z-μ)) μ ((a : ℂ)*μ) + Gamma (q.map (fun z => z-μ)) μ ≤
      1-a*‖μ‖-79*(1-a)/504 ∧
    majorant_Efin (q.map (fun z => z-μ)) μ ((a : ℂ)*μ) + Gamma (q.map (fun z => z-μ)) μ <
      1-a*‖μ‖ := by
  have hraw := CenteredNearTheorem.raw_of_fullpolar q (by omega) a μ hmean hq hp
  have h := C_near_raw_quarter q hm a μ ha0 ha1 hmean hq hraw hl
  exact ⟨h, by linarith⟩

/-- Direct first-origin norm obstruction throughout the larger near region. -/
theorem norm_J_gt_one_fullpolar_quarter (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hmean : q.sum = q.card * μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1)
    (hp : 1 ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun z => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ)^2) * z)).prod‖)
    (hl : PaperPolar.lambda q.card a ≤ 1 / 4) :
    1 < ‖(q.card+1 : ℂ) *
      (∫ t in (0 : ℝ)..1, (q.map (fun z => 1-(a : ℂ)*t*z)).prod)‖ := by
  have hraw := CenteredNearTheorem.raw_of_fullpolar q (by omega) a μ hmean hq hp
  have hu := (PaperConsequences.centered_variance_le q μ (by omega) hmean hq).2
  obtain ⟨hx0, hx1⟩ := abs_le.mp ((Complex.abs_re_le_norm μ).trans hu)
  have hμ := PaperConsequences.mean_ne_zero_of_rawPolar hm ha0 ha1 hx0 hx1 rfl hraw
  exact PaperCenteredBound.C_budget q a μ (by omega) ha0.le hmean hμ
    (C_near_fullpolar_quarter q hm a μ ha0 ha1 hmean hq hp hl).2

end Sendov.CenteredQuarterTheorem
