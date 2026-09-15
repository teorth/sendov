import Sendov.Analytic.CenteredActualTail
import Sendov.Analytic.Polar

/-! Positive-variance C-near on a uniform all-degree small-lambda domain.
All tail hypotheses are discharged for the actual square-root majorant. -/
noncomputable section
open scoped BigOperators
namespace Sendov.CenteredNearTheorem
open PaperCentered PaperCenteredBound CenteredActualTail

/-- No error-budget premise remains: raw polar and actual pointwise moments
prove the strict original C-budget throughout m(1-a)≤4/39. -/
theorem C_near_raw_small (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hmean : q.sum = q.card * μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1) (hp : PaperPolar.RawPolar q.card a μ.re)
    (hl : PaperPolar.lambda q.card a ≤ 4/39) :
    majorant_Efin (q.map (fun z => z-μ)) μ ((a : ℂ)*μ) + Gamma (q.map (fun z => z-μ)) μ <
      (99/100 : ℝ)*(1-a) ∧
    majorant_Efin (q.map (fun z => z-μ)) μ ((a : ℂ)*μ) + Gamma (q.map (fun z => z-μ)) μ <
      1-a*‖μ‖ := by
  let r := q.map (fun z => z-μ)
  have hcard : r.card = q.card := by simp [r]
  have hstats := PaperConsequences.centered_variance_le q μ (by omega) hmean hq
  have hreal : |μ.re| ≤ 1 := (Complex.abs_re_le_norm μ).trans hstats.2
  obtain ⟨hx0, hx1⟩ := abs_le.mp hreal
  have hμ := PaperConsequences.mean_ne_zero_of_rawPolar hm ha0 ha1 hx0 hx1 rfl hp
  have hb := CenteredNearScalar.beta_le_rho_sq q.card hm a μ.re ha0 ha1 hx0 hx1 hp hl
  have ht1 := majorantTail_le_tailScalar r (by simpa [r] using hm) μ a ha0.le ha1.le hμ
    hstats.2 hx0 hx1 hstats.1 hb
  have ht2 := CenteredNearScalar.actual_tailScalar_le q hm a μ ha0 ha1 hmean hq hx0 hx1 hp hl
  have ht : majorantTail r μ ((a : ℂ)*μ) ≤ 3*(1-a)/5 :=
    ht1.trans (by simpa only [hcard] using ht2)
  have he := CenteredNearScalar.actual_endpoint_le q hm a μ ha0 ha1 hmean hq hx0 hx1 hp hl
  have hg := PaperConsequences.Gamma_lt_seven_eighteenths q hm ha0 ha1 hmean hq hx0 hx1 rfl hp
  have hs := CenteredNearScalar.budget_close (1-a)
    (‖1-(a : ℂ)*μ‖^(q.card+1)+Gamma r μ*‖B q.card 2 ((a : ℂ)*μ)‖)
    (majorantTail r μ ((a : ℂ)*μ)) (Gamma r μ) ‖μ‖ a (by linarith) ha0.le hstats.2 rfl he ht hg.le
  simpa only [majorant_Efin, majorantTail, r, Multiset.card_map] using hs

/-- Exact complex polar feasibility implies the raw integral on the actual mean. -/
theorem raw_of_fullpolar (q : Multiset ℂ) (hm : 1 ≤ q.card) (a : ℝ) (μ : ℂ)
    (hmean : q.sum = q.card * μ) (hq : ∀ z ∈ q, ‖z‖ ≤ 1)
    (hp : 1 ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun z => (a : ℂ)+(t : ℂ)*(1-(a : ℂ)^2)*z)).prod‖) :
    PaperPolar.RawPolar q.card a μ.re := by
  have hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun z => ‖(a : ℂ)+(t : ℂ)*(1-(a : ℂ)^2)*z‖)).prod := by
    apply hp.trans
    apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans_eq
    apply intervalIntegral.integral_congr
    intro t ht
    exact norm_prod_map q _
  have hx : (q.map (fun z => z.re)).sum = (((q.card+1 : ℕ) : ℝ)-1)*μ.re := by
    have hre : (q.map (fun z => z.re)).sum = q.sum.re :=
      (map_multiset_sum Complex.reAddGroupHom q).symm
    rw [hre, hmean]
    simp
  apply (PaperPolar.rawPolar_iff q.card a μ.re).2
  have h := one_le_integral_Ppolar (n := q.card+1) (by omega) (by simp) hq hx hstar
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using h

/-- The requested original pointwise + FULLpolar domain, with positive variance
allowed. This is a uniform subdomain result, not an all-a theorem. -/
theorem C_near_fullpolar_small (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hmean : q.sum = q.card * μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1)
    (hp : 1 ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun z => (a : ℂ)+(t : ℂ)*(1-(a : ℂ)^2)*z)).prod‖)
    (hl : PaperPolar.lambda q.card a ≤ 4/39) :
    majorant_Efin (q.map (fun z => z-μ)) μ ((a : ℂ)*μ) + Gamma (q.map (fun z => z-μ)) μ <
      (99/100 : ℝ)*(1-a) ∧
    majorant_Efin (q.map (fun z => z-μ)) μ ((a : ℂ)*μ) + Gamma (q.map (fun z => z-μ)) μ <
      1-a*‖μ‖ :=
  C_near_raw_small q hm a μ ha0 ha1 hmean hq (raw_of_fullpolar q (by omega) a μ hmean hq hp) hl

/-- Direct first-origin obstruction from the newly proved centered budget.
No first-origin or centroid identity is assumed in this theorem. -/
theorem norm_J_gt_one_fullpolar_small (q : Multiset ℂ) (hm : 7 ≤ q.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hmean : q.sum = q.card * μ)
    (hq : ∀ z ∈ q, ‖z‖ ≤ 1)
    (hp : 1 ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun z => (a : ℂ)+(t : ℂ)*(1-(a : ℂ)^2)*z)).prod‖)
    (hl : PaperPolar.lambda q.card a ≤ 4 / 39) :
    1 < ‖(q.card+1 : ℂ) *
      (∫ t in (0 : ℝ)..1, (q.map (fun z => 1-(a : ℂ)*t*z)).prod)‖ := by
  have hraw := raw_of_fullpolar q (by omega) a μ hmean hq hp
  have hu := (PaperConsequences.centered_variance_le q μ (by omega) hmean hq).2
  obtain ⟨hx0, hx1⟩ := abs_le.mp ((Complex.abs_re_le_norm μ).trans hu)
  have hμ := PaperConsequences.mean_ne_zero_of_rawPolar hm ha0 ha1 hx0 hx1 rfl hraw
  exact PaperCenteredBound.C_budget q a μ (by omega) ha0.le hmean hμ
    (C_near_fullpolar_small q hm a μ ha0 ha1 hmean hq hp hl).2

end Sendov.CenteredNearTheorem
