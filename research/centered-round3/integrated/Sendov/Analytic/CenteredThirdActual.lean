import Sendov.Analytic.CenteredThirdScalar

noncomputable section
open scoped BigOperators
namespace Sendov.CenteredThird

/-- All scalar facts needed in the third regime, on the actual complex mean
and actual centered variance. In particular no s=1 or real-mean premise occurs. -/
theorem actual_third_facts (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hmean : q.sum = q.card*μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1) (hx0 : -1 ≤ μ.re) (hx1 : μ.re ≤ 1)
    (hp : PaperPolar.RawPolar q.card a μ.re)
    (hl : PaperPolar.lambda q.card a ≤ 1/3) :
    1-a ≤ 1/21 ∧ 113/120 ≤ ‖μ‖ ∧
      PaperPolar.b a μ.re ≤ 1/10 ∧
      PaperCentered.variance (q.map (fun z => z-μ)) ≤ 1/10 ∧
      PaperCentered.variance (q.map (fun z => z-μ))*(3+(q.card:ℝ)*(1-a)) ≤ (q.card:ℝ)*(1-a) ∧
      ‖1-(a:ℂ)*μ‖ ≤ 19/60 := by
  have hm7 : (7:ℝ) ≤ q.card := by exact_mod_cast hm
  have hh0 : 0 ≤ 1-a := by linarith
  have hL : (q.card:ℝ)*(1-a) ≤ 1/3 := hl
  have hh : 1-a ≤ 1/21 := by
    have ht := mul_le_mul_of_nonneg_right hm7 hh0
    linarith
  have ha : 20/21 ≤ a := by linarith
  have hstats := PaperConsequences.centered_variance_le q μ (by omega) hmean hq
  have hu1 := hstats.2
  have hv0 : 0 ≤ PaperCentered.variance (q.map (fun z => z-μ)) :=
    PaperCoefficient.variance_nonneg _
  have hb0 := (PaperPolar.b_pos ha0.le ha1 hx1).le
  have hb1 := (PaperPolar.b_lt_one (by omega) ha0 ha1 hx0 hx1 hp).le
  have hs := CenteredQuarter.rawPolar_slope q.card hm a μ ha0 ha1 hx0 hx1 hp
  have hb : PaperPolar.b a μ.re ≤ 1/10 := by
    have ht := mul_le_mul_of_nonneg_right hL (sub_nonneg.mpr hb1)
    nlinarith only [hs, ht]
  have hbl : PaperPolar.b a μ.re ≤ (q.card:ℝ)*(1-a)/3 := by
    have ht := mul_nonneg (mul_nonneg (Nat.cast_nonneg q.card) hh0) hb0
    nlinarith only [hs, ht]
  have hmu : 113/120 ≤ ‖μ‖ := by
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
  have hvsl : PaperCentered.variance (q.map (fun z => z-μ))*(3+(q.card:ℝ)*(1-a)) ≤ (q.card:ℝ)*(1-a) := by
    have ht := mul_le_mul_of_nonneg_right hvb (show 0 ≤ 3+(q.card:ℝ)*(1-a) by positivity)
    nlinarith only [ht, hs]
  have hw2 := PaperCenteredVarianceEndpoint.actual_variance_endpoint q μ a (by omega) hmean hq
  have hw : ‖1-(a:ℂ)*μ‖ ≤ 19/60 := by
    have ht := mul_nonneg (sq_nonneg a) hv0
    nlinarith only [hw2, hb, ht, norm_nonneg (1-(a:ℂ)*μ)]
  exact ⟨hh, hmu, hb, hvb.trans hb, hvsl, hw⟩


end Sendov.CenteredThird
