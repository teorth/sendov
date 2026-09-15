import Sendov.Analytic.CenteredQuarterScalar
import Sendov.Analytic.PaperCenteredVarianceEndpoint

noncomputable section
open scoped BigOperators
namespace Sendov.CenteredQuarter

/-- Raw-polar slope, without discarding its factor (1-b). -/
lemma rawPolar_slope (m : ℕ) (hm : 7 ≤ m) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ μ.re) (hx1 : μ.re ≤ 1)
    (hp : PaperPolar.RawPolar m a μ.re) :
    3*PaperPolar.b a μ.re ≤ (m:ℝ)*(1-a)*(1-PaperPolar.b a μ.re) := by
  have hb := PaperPolar.endpoint_bounds hm ha0 ha1 hx0 hx1 hp
  have hl := PaperPolar.lambda_pos (by omega : 0 < m) ha1
  have hs := (le_div_iff₀ (by positivity : 0 < 3+PaperPolar.lambda m a)).mp
    (hb.1.trans hb.2)
  unfold PaperPolar.lambda at hs
  nlinarith only [hs]

/-- All scalar facts needed in the quarter regime, on the actual complex mean
and actual centered variance. In particular no s=1 or real-mean premise occurs. -/
theorem actual_quarter_facts (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hmean : q.sum = q.card*μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1) (hx0 : -1 ≤ μ.re) (hx1 : μ.re ≤ 1)
    (hp : PaperPolar.RawPolar q.card a μ.re)
    (hl : PaperPolar.lambda q.card a ≤ 1/4) :
    1-a ≤ 1/28 ∧ 155/162 ≤ ‖μ‖ ∧
      PaperPolar.b a μ.re ≤ 1/13 ∧
      PaperCentered.variance (q.map (fun z => z-μ)) ≤ 1/13 ∧
      PaperCentered.variance (q.map (fun z => z-μ)) ≤ (q.card:ℝ)*(1-a)/3 ∧
      ‖1-(a:ℂ)*μ‖ ≤ 5/18 := by
  have hm7 : (7:ℝ) ≤ q.card := by exact_mod_cast hm
  have hh0 : 0 ≤ 1-a := by linarith
  have hL : (q.card:ℝ)*(1-a) ≤ 1/4 := hl
  have hh : 1-a ≤ 1/28 := by
    have ht := mul_le_mul_of_nonneg_right hm7 hh0
    linarith
  have ha : 27/28 ≤ a := by linarith
  have hstats := PaperConsequences.centered_variance_le q μ (by omega) hmean hq
  have hu1 := hstats.2
  have hv0 : 0 ≤ PaperCentered.variance (q.map (fun z => z-μ)) :=
    PaperCoefficient.variance_nonneg _
  have hb0 := (PaperPolar.b_pos ha0.le ha1 hx1).le
  have hb1 := (PaperPolar.b_lt_one (by omega) ha0 ha1 hx0 hx1 hp).le
  have hs := rawPolar_slope q.card hm a μ ha0 ha1 hx0 hx1 hp
  have hb : PaperPolar.b a μ.re ≤ 1/13 := by
    have ht := mul_le_mul_of_nonneg_right hL (sub_nonneg.mpr hb1)
    nlinarith only [hs, ht]
  have hbl : PaperPolar.b a μ.re ≤ (q.card:ℝ)*(1-a)/3 := by
    have ht := mul_nonneg (mul_nonneg (Nat.cast_nonneg q.card) hh0) hb0
    nlinarith only [hs, ht]
  have hmu : 155/162 ≤ ‖μ‖ := by
    have hx := Complex.re_le_norm μ
    have ht := mul_le_mul_of_nonneg_left hx ha0.le
    have hsl : 6*a*(1-‖μ‖) ≤ (q.card:ℝ)*(1-a) := by
      unfold PaperPolar.b at hbl
      nlinarith only [hbl, ht, sq_nonneg (1-a)]
    have ht' := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hu1)
    nlinarith only [hsl, ht', hL]
  have hvb : PaperCentered.variance (q.map (fun z => z-μ)) ≤ PaperPolar.b a μ.re := by
    have hn : 1-PaperPolar.b a μ.re ≤ ‖μ‖^2 := by
      have hnorm := Complex.sq_norm_sub_sq_re μ
      unfold PaperPolar.b
      nlinarith only [hnorm, sq_nonneg μ.im, sq_nonneg (μ.re-a)]
    linarith [hstats.1]
  have hw2 := PaperCenteredVarianceEndpoint.actual_variance_endpoint q μ a (by omega) hmean hq
  have hw : ‖1-(a:ℂ)*μ‖ ≤ 5/18 := by
    have ht := mul_nonneg (sq_nonneg a) hv0
    nlinarith only [hw2, hb, ht, norm_nonneg (1-(a:ℂ)*μ)]
  exact ⟨hh, hmu, hb, hvb.trans hb, hvb.trans hbl, hw⟩

/-- Generic fourth-order endpoint instantiated with actual raw-polar statistics. -/
theorem actual_endpoint_quadratic (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hmean : q.sum = q.card*μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1) (hx0 : -1 ≤ μ.re) (hx1 : μ.re ≤ 1)
    (hp : PaperPolar.RawPolar q.card a μ.re) :
    ‖1-(a:ℂ)*μ‖^(q.card+1) ≤ 2*(1-a)^2/3 := by
  have hv0 : 0 ≤ PaperCentered.variance (q.map (fun z => z-μ)) :=
    PaperCoefficient.variance_nonneg _
  have hw2 := PaperCenteredVarianceEndpoint.actual_variance_endpoint q μ a (by omega) hmean hq
  exact endpoint_quadratic q.card hm ‖1-(a:ℂ)*μ‖ (PaperPolar.b a μ.re) (1-a)
    (norm_nonneg _) (PaperPolar.b_pos ha0.le ha1 hx1).le
    (PaperPolar.b_lt_one (by omega) ha0 ha1 hx0 hx1 hp).le (by linarith)
    (rawPolar_slope q.card hm a μ ha0 ha1 hx0 hx1 hp)
    (by nlinarith only [hw2, mul_nonneg (sq_nonneg a) hv0])

/-- Original-C majorant assembly. The sole remaining analytic input is the
explicit chord-tail inequality for the unchanged original finite C sum. -/
theorem actual_C_quarter_budget (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hmean : q.sum = q.card*μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1) (hx0 : -1 ≤ μ.re) (hx1 : μ.re ≤ 1)
    (hp : PaperPolar.RawPolar q.card a μ.re)
    (hl : PaperPolar.lambda q.card a ≤ 1/4)
    (htail : (∑ k ∈ Finset.Ico 3 (q.card+1),
      (PaperCenteredBound.C q.card k (PaperCentered.variance (q.map (fun z => z-μ))) /
        ((q.card.choose k:ℝ)*‖μ‖^k))*‖PaperCentered.H q.card k ((a:ℂ)*μ)‖) ≤
      chordTail q.card a ‖μ‖ (PaperCentered.variance (q.map (fun z => z-μ)))) :
    PaperCenteredBound.majorant_Efin (q.map (fun z => z-μ)) μ ((a:ℂ)*μ) +
      PaperCentered.Gamma (q.map (fun z => z-μ)) μ ≤ 1-a*‖μ‖-79*(1-a)/504 := by
  obtain ⟨hh, hu, hb, hv1, hv, hw⟩ := actual_quarter_facts q hm a μ ha0 ha1 hmean hq hx0 hx1 hp hl
  have hstats := PaperConsequences.centered_variance_le q μ (by omega) hmean hq
  have hz : ‖(a:ℂ)*μ‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
    exact (mul_le_of_le_one_right ha0.le hstats.2).trans ha1.le
  have hB := norm_B_two_le q.card hm ((a:ℂ)*μ) hz hw
  have he0 := actual_endpoint_quadratic q hm a μ ha0 ha1 hmean hq hx0 hx1 hp
  have hs := scalar_budget (q.card:ℝ) a (1-a) ‖μ‖
    (PaperCentered.variance (q.map (fun z => z-μ))) _ _ _
    (by exact_mod_cast hm) (by linarith) hh (by ring) (by linarith)
    (by linarith [hstats.1]) (PaperCoefficient.variance_nonneg _) hv1 hv he0 hB htail
  unfold PaperCenteredBound.majorant_Efin PaperCentered.Gamma
  simp only [Multiset.card_map]
  convert hs using 1 <;> ring

end Sendov.CenteredQuarter
