import Sendov.Analytic.CenteredQuarterTheorem

/-! Retained complex mean geometry; no restriction to real means. -/
noncomputable section
namespace Sendov.CenteredMeanBudget
open PaperCentered PaperCenteredBound

/-- Exact endpoint/mean identity. The extra square must not be discarded early. -/
theorem norm_sq_add_b (a : ℝ) (μ : ℂ) :
    ‖μ‖^2 + PaperPolar.b a μ.re = 1 + ‖μ-(a : ℂ)‖^2 := by
  simp only [PaperPolar.b, Complex.sq_norm, Complex.normSq_apply,
    Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
  ring

theorem norm_sq_ge_one_sub_b (a : ℝ) (μ : ℂ) :
    1-PaperPolar.b a μ.re ≤ ‖μ‖^2 := by
  have h := norm_sq_add_b a μ
  nlinarith only [h, sq_nonneg ‖μ-(a : ℂ)‖]

/-- Gamma retains its actual variance numerator. -/
theorem Gamma_le_endpoint (r : Multiset ℂ) (μ : ℂ) (a : ℝ)
    (hm : 2 ≤ r.card) (hb : PaperPolar.b a μ.re < 1) :
    Gamma r μ ≤ variance r / (((r.card : ℝ)-1)*(1-PaperPolar.b a μ.re)) := by
  have hm' : (2 : ℝ) ≤ r.card := by exact_mod_cast hm
  have hden : 0 < ((r.card : ℝ)-1)*(1-PaperPolar.b a μ.re) :=
    mul_pos (by linarith) (by linarith)
  unfold Gamma
  exact div_le_div_of_nonneg_left (PaperCoefficient.variance_nonneg r) hden
    (mul_le_mul_of_nonneg_left (norm_sq_ge_one_sub_b a μ) (by linarith))

/-- A generic rational endpoint budget, without any degree table. -/
theorem Gamma_le_rational (r : Multiset ℂ) (μ : ℂ) (a L : ℝ)
    (hm : 2 ≤ r.card) (hL : 0 ≤ L)
    (hb : PaperPolar.b a μ.re ≤ L/(3+L)) :
    Gamma r μ ≤ (3+L)*variance r/(3*((r.card : ℝ)-1)) := by
  have hm' : (2 : ℝ) ≤ r.card := by exact_mod_cast hm
  have hp : 0 < 3+L := by linarith
  have hbr : L/(3+L) < 1 := (div_lt_one hp).2 (by linarith)
  have hden : 0 < ((r.card : ℝ)-1)*(1-L/(3+L)) :=
    mul_pos (by linarith) (by linarith)
  have h := Gamma_le_endpoint r μ a hm (hb.trans_lt hbr)
  have h2 : variance r / (((r.card : ℝ)-1)*(1-PaperPolar.b a μ.re)) ≤
      variance r / (((r.card : ℝ)-1)*(1-L/(3+L))) := by
    apply div_le_div_of_nonneg_left (PaperCoefficient.variance_nonneg r) hden
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  apply h.trans (h2.trans_eq _)
  have hm0 : (r.card : ℝ)-1 ≠ 0 := by linarith
  field_simp
  <;> ring

/-- Raw polar supplies the rational parameter; there is no external Gamma budget. -/
theorem Gamma_le_raw_lambda (r : Multiset ℂ) (μ : ℂ) (a : ℝ)
    (hm : 7 ≤ r.card) (ha0 : 0 < a) (ha1 : a < 1)
    (hu : ‖μ‖ ≤ 1) (hp : PaperPolar.RawPolar r.card a μ.re) :
    Gamma r μ ≤ (3+PaperPolar.lambda r.card a)*variance r/(3*((r.card : ℝ)-1)) := by
  obtain ⟨hx0,hx1⟩ := abs_le.mp ((Complex.abs_re_le_norm μ).trans hu)
  have he := PaperPolar.endpoint_bounds hm ha0 ha1 hx0 hx1 hp
  exact Gamma_le_rational r μ a _ (by omega)
    (PaperPolar.lambda_pos (by omega) ha1).le (he.1.trans he.2)

/-- Uniform original-a-domain consequence, stronger than the a/2 mean estimate. -/
theorem Gamma_le_raw_degree (r : Multiset ℂ) (μ : ℂ) (a : ℝ)
    (hm : 7 ≤ r.card) (ha0 : 9/10 ≤ a) (ha1 : a < 1)
    (hu : ‖μ‖ ≤ 1) (hp : PaperPolar.RawPolar r.card a μ.re) :
    Gamma r μ ≤ ((r.card : ℝ)+30)*variance r/(30*((r.card : ℝ)-1)) := by
  have ha : 0 < a := by linarith
  have hm' : (7 : ℝ) ≤ r.card := by exact_mod_cast hm
  have hL : PaperPolar.lambda r.card a ≤ (r.card : ℝ)/10 := by
    unfold PaperPolar.lambda
    nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) r.card) (show 0 ≤ a-9/10 by linarith)]
  have h := Gamma_le_raw_lambda r μ a hm ha ha1 hu hp
  apply h.trans
  have hv : 0 ≤ variance r := PaperCoefficient.variance_nonneg r
  have hd : 0 < 3*((r.card : ℝ)-1) := by linarith
  have hd' : 0 < 30*((r.card : ℝ)-1) := by linarith
  apply (div_le_div_iff₀ hd hd').2
  nlinarith only [mul_nonneg (show 0 ≤ (r.card : ℝ)/10-PaperPolar.lambda r.card a by linarith)
    (mul_nonneg hv (show 0 ≤ (r.card : ℝ)-1 by linarith))]

/-- The sharper Gamma budget under the unchanged original FULLpolar hypotheses. -/
theorem Gamma_le_fullpolar_degree (q : Multiset ℂ) (μ : ℂ) (a : ℝ)
    (hm : 7 ≤ q.card) (ha0 : 9 / 10 ≤ a) (ha1 : a < 1)
    (hmean : q.sum = q.card * μ) (hq : ∀ z ∈ q, ‖z‖ ≤ 1)
    (hp : 1 ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun z => (a : ℂ)+(t : ℂ)*(1-(a : ℂ)^2)*z)).prod‖) :
    Gamma (q.map (fun z => z-μ)) μ ≤
      ((q.card : ℝ)+30)*variance (q.map (fun z => z-μ))/(30*((q.card : ℝ)-1)) := by
  have hu := (PaperConsequences.centered_variance_le q μ (by omega) hmean hq).2
  have hr := CenteredNearTheorem.raw_of_fullpolar q (by omega) a μ hmean hq hp
  simpa only [Multiset.card_map] using
    Gamma_le_raw_degree (q.map (fun z => z-μ)) μ a (by simpa using hm)
      ha0 ha1 hu (by simpa using hr)

end Sendov.CenteredMeanBudget
