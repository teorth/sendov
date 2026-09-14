import Sendov.Analytic.PaperConsequences
import Sendov.Analytic.PaperGlobalPolar
import Sendov.Analytic.FirstOriginBounds

/-! # Exported finite-moment and raw-polar paper corollaries

The identifiers FO05, FO06, PO01, PO07, PO09, EX01, EX02 refer to the
paper acceptance ledger. All moments are actual finite multiset moments.
The remainder premise in EX02 is deliberately retained.
-/
noncomputable section
open scoped BigOperators
namespace Sendov.PaperMomentCorollaries
open PaperPolar PaperCentered

/-- Actual arithmetic mean (only used below for nonempty multisets). -/
def mean (q : Multiset ℂ) : ℂ := q.sum / (q.card : ℂ)
/-- Actual second absolute moment. -/
def secondMoment (q : Multiset ℂ) : ℝ :=
  (q.map (fun z => ‖z‖ ^ 2)).sum / (q.card : ℝ)

lemma mean_spec (q : Multiset ℂ) (hm : 0 < q.card) : q.sum = q.card * mean q := by
  have hc : (q.card : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  unfold mean
  field_simp

/-- FO05: finite mean/variance identities, including the centered square moment. -/
theorem FO05 (q : Multiset ℂ) (hm : 0 < q.card) (hq : ∀ z ∈ q, ‖z‖ ≤ 1) :
    ‖mean q‖ ≤ 1 ∧ secondMoment q ≤ 1 ∧
    variance (q.map (fun z => z - mean q)) = secondMoment q - ‖mean q‖ ^ 2 ∧
    ‖kappa (q.map (fun z => z - mean q))‖ ≤ variance (q.map (fun z => z - mean q)) := by
  have hc : (0 : ℝ) < q.card := by exact_mod_cast hm
  have hn := (PaperConsequences.centered_variance_le q (mean q) hm (mean_spec q hm) hq).2
  have hs := PaperCoefficient.sum_norm_add_sq (q.map (fun z => z - mean q)) (mean q)
  rw [centered_sum q (mean q) (mean_spec q hm)] at hs
  have hmap : (q.map (fun z => z - mean q)).map (fun w => ‖mean q + w‖ ^ 2) =
      q.map (fun z => ‖z‖ ^ 2) := by
    simp only [Multiset.map_map, Function.comp_def]
    congr 1
    funext z
    congr 2
    ring
  rw [hmap] at hs
  simp only [Multiset.card_map, map_zero, mul_zero, Complex.zero_re, add_zero] at hs
  refine ⟨hn, ?_, ?_, norm_kappa_le_variance _⟩
  · unfold secondMoment
    exact (div_le_one hc).mpr (Sendov.sum_norm_sq_le_card q hq)
  · unfold variance secondMoment
    rw [Multiset.card_map]
    apply (div_eq_iff hc.ne').mpr
    have hid : (q.map (fun z => ‖z‖ ^ 2)).sum / (q.card : ℝ) * q.card =
        (q.map (fun z => ‖z‖ ^ 2)).sum := div_mul_cancel₀ _ hc.ne'
    nlinarith only [hs, hid]

/-- FO06, cubic half-mean deficit, extended monotonically to x below half-mean. -/
theorem FO06_six {a x : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hx0 : -1 ≤ x) (hx : x ≤ (1 + a) / 2) :
    (∫ t in (0 : ℝ)..1, Ppolar a x t ^ (3 : ℕ)) ≤ 1 - 23 * (1 - a) ^ 2 / 35 := by
  have hid := FirstOriginSmall.polar_cube_integral a
  have hQ := FirstOriginSmall.Q_lower ha ha1
  have hi := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (by norm_num : (0 : ℝ) ≤ 1)
    (((continuous_Ppolar a x).pow 3).intervalIntegrable 0 1)
    (((continuous_Ppolar a ((1+a)/2)).pow 3).intervalIntegrable 0 1)
    (show ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Ppolar a x t ^ (3 : ℕ) ≤ Ppolar a ((1+a)/2) t ^ (3 : ℕ) from by
      intro t ht
      exact pow_le_pow_left₀ (FirstOriginSmall.Ppolar_nonneg_small ha ha1 hx0 ht.1)
        (FirstOriginSmall.Ppolar_le_half ha ha1 hx ht.1) 3)
  have hp := mul_nonneg (sq_nonneg (1-a)) (sub_nonneg.mpr hQ)
  dsimp only [Pi.pow_apply] at hi
  nlinarith only [hid, hp, hi]

/-- FO06, fifth-power square-root deficit with the exact 23/42 constant. -/
theorem FO06_five {a x : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hx0 : -1 ≤ x) (hx : x ≤ (1 + a) / 2) :
    (∫ t in (0 : ℝ)..1, Ppolar a x t ^ (5 / 2 : ℝ)) ≤ 1 - 23 * (1 - a) ^ 2 / 42 := by
  have hcube := FO06_six ha ha1 (by linarith : -1 ≤ (1+a)/2) (le_refl ((1+a)/2))
  have hcp : Continuous (fun t => Ppolar a ((1 + a) / 2) t ^ (3 : ℕ)) :=
    (continuous_Ppolar _ _).pow 3
  have hcont : Continuous (fun t => Ppolar a x t ^ (5 / 2 : ℝ)) :=
    (continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 5 / 2)).comp (continuous_Ppolar a x)
  have hi := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (by norm_num : (0 : ℝ) ≤ 1)
    (hcont.intervalIntegrable 0 1)
    ((continuous_const.add (continuous_const.mul hcp)).intervalIntegrable 0 1)
    (show ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Ppolar a x t ^ (5 / 2 : ℝ) ≤
        (1 / 6 : ℝ) + (5 / 6 : ℝ) * Ppolar a ((1 + a) / 2) t ^ (3 : ℕ) from by
      intro t ht
      have hp0 := FirstOriginSmall.Ppolar_nonneg_small ha ha1 hx0 ht.1
      have hp1 := FirstOriginSmall.Ppolar_le_half ha ha1 hx ht.1
      have hz := hp0.trans hp1
      have hmono := Real.rpow_le_rpow hp0 hp1 (by norm_num : (0 : ℝ) ≤ 5 / 2)
      have hf := FirstOriginSmall.fifth_sixth_majorant (Real.sqrt_nonneg (Ppolar a ((1+a)/2) t))
      rw [FirstOriginSmall.sqrt_pow_eq_rpow hz 5, FirstOriginSmall.sqrt_pow_eq_rpow hz 6] at hf
      norm_num [Real.rpow_natCast] at hf
      linarith)
  dsimp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] at hi
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _)
    only [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const] at hi
  norm_num at hi
  linarith

/-- FO06: the natural degree is exactly five or six, not an extrapolation. -/
theorem FO06 {m : ℕ} (hm : m = 5 ∨ m = 6) {a x : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hr : RawPolar m a x) :
    (1 + a) / 2 < x := by
  apply FirstOriginSmall.polar_mean_gt_half_add_one (n := m+1) (by omega) ha ha1 hx0
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using (rawPolar_iff m a x).mp hr

/-- PO01: raw-polar geometry for every natural m ≥ 1, including m < 7. -/
theorem PO01 {m : ℕ} {a x : ℝ} (hm : 1 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hr : RawPolar m a x) :
    a / 2 < x ∧ 0 < c a x ∧ c a x < 1 ∧ 0 < b a x ∧ b a x < 1 := by
  have hb := b_lt_one (by omega : 0 < m) ha ha1 hx0 hx1 hr
  have hp := b_pos ha.le ha1 hx1
  refine ⟨?_, ?_, ?_, hp, hb⟩
  · unfold b at hb
    nlinarith
  · unfold c
    linarith
  · unfold c
    linarith

/-- PO07: y=(1+c)/2 and the two exact Gaussian consequences of rational polar. -/
theorem PO07 {m : ℕ} {a x : ℝ} (hm : 1 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hr : RawPolar m a x) :
    let y := (1 + c a x) / 2
    1 - y ≤ alpha m a * y ^ 2 / 6 ∧
    alpha m a * y ^ 2 / 6 ≤ lambda m a * y ^ 2 / 6 ∧
    1 - x ≤ lambda m a / (6 * a) := by
  dsimp only
  have hA := PaperPolar.alpha_pos (by omega : 0 < m) ha ha1
  have hL := alpha_le_lambda m a
  have hb := (le_div_iff₀ (by positivity : 0 < 3 + alpha m a)).mp
    (b_le_alpha (by omega : 0 < m) ha ha1 hx0 hx1 hr)
  obtain ⟨_, hc0, hc1, _, _⟩ := PO01 hm ha ha1 hx0 hx1 hr
  have hy0 : 0 ≤ (1 + c a x) / 2 := by linarith
  have hy1 : (1 + c a x) / 2 ≤ 1 := by linarith
  have hysq := pow_le_one₀ hy0 hy1 (n := 2)
  have hfirst : 1 - (1 + c a x) / 2 ≤ alpha m a * ((1 + c a x) / 2) ^ 2 / 6 := by
    have hp := mul_nonneg hA.le (sq_nonneg (b a x))
    unfold c
    nlinarith only [hb, hp]
  have hsecond : alpha m a * ((1 + c a x) / 2) ^ 2 / 6 ≤
      lambda m a * ((1 + c a x) / 2) ^ 2 / 6 := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hL (sq_nonneg _)) (by norm_num)
  refine ⟨hfirst, hsecond, ?_⟩
  apply (le_div_iff₀ (by positivity : 0 < 6 * a)).mpr
  have hl := mul_le_mul_of_nonneg_left hysq (lambda_pos (by omega : 0 < m) ha1).le
  have hid : 1 - (1 + c a x) / 2 = a * (1-x) + (1-a)^2/2 := by unfold c b; ring
  nlinarith only [hfirst.trans hsecond, hl, hid, sq_nonneg (1-a)]

/-- The rational bound evaluates strictly positively in the Gaussian quadratic. -/
lemma rational_quadratic {A : ℝ} (hA : 0 < A) :
    A * ((A+6)/(2*(A+3)))^2 + 6*((A+6)/(2*(A+3))) - 6 = A^3/(4*(A+3)^2) := by
  have hd : A+3 ≠ 0 := by positivity
  field_simp
  ring

/-- PO09: strict comparison, with the explicit positive Gaussian root. -/
theorem PO09 {m : ℕ} {a x : ℝ} (hm : 1 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hr : RawPolar m a x) :
    (Real.sqrt (36 + 24 * alpha m a) - 6) / (2 * alpha m a) <
      (alpha m a + 6) / (2 * (alpha m a + 3)) ∧
    (alpha m a + 6) / (2 * (alpha m a + 3)) ≤ (1 + c a x) / 2 := by
  let A := alpha m a
  have hA : 0 < A := PaperPolar.alpha_pos (by omega : 0 < m) ha ha1
  have hd : 0 < A+3 := by positivity
  have hb := (le_div_iff₀ (by positivity : 0 < 3 + A)).mp
    (b_le_alpha (by omega : 0 < m) ha ha1 hx0 hx1 hr)
  have hy : (A+6)/(2*(A+3)) ≤ (1+c a x)/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*(A+3))).mpr
    unfold c
    nlinarith only [hb]
  refine ⟨?_, hy⟩
  change (Real.sqrt (36+24*A)-6)/(2*A) < (A+6)/(2*(A+3))
  let g := (Real.sqrt (36+24*A)-6)/(2*A)
  let y := (A+6)/(2*(A+3))
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 36+24*A)
  have hs0 := Real.sqrt_nonneg (36+24*A)
  have hg0 : 0 ≤ g := by
    dsimp [g]
    apply div_nonneg _ (by positivity)
    nlinarith only [hs, hs0, hA]
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hg : A*g^2+6*g-6 = 0 := by
    dsimp [g]
    field_simp
    simp only [mul_comm A 24]
    nlinarith only [hs]
  have hypos : 0 < A*y^2+6*y-6 := by
    dsimp [y]
    rw [rational_quadratic hA]
    positivity
  change g < y
  by_contra h
  have hle : y ≤ g := le_of_not_gt h
  have hp := mul_nonneg hA.le (mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hg0 hy0))
  nlinarith only [hg, hypos, hp, hle]

/-- EX01: the complete actual variance/mean-square and Gamma chains. -/
theorem EX01 (q : Multiset ℂ) {μ : ℂ} {a x : ℝ}
    (hm : 7 ≤ q.card) (ha : 0 < a) (ha1 : a < 1)
    (hmean : q.sum = q.card * μ) (hq : ∀ z ∈ q, ‖z‖ ≤ 1)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hx : μ.re = x) (hr : RawPolar q.card a x) :
    variance (q.map (fun z => z-μ)) / ‖μ‖^2 ≤ b a x / (1-b a x) ∧
    b a x / (1-b a x) ≤ alpha q.card a / 3 ∧
    Gamma (q.map (fun z => z-μ)) μ ≤ alpha q.card a / (3*((q.card : ℝ)-1)) ∧
    alpha q.card a / (3*((q.card : ℝ)-1)) < 7*(1-a)/18 := by
  have hc : 0 < 1-b a x := by
    have := b_lt_one (by omega : 0 < q.card) ha ha1 hx0 hx1 hr
    linarith
  have hs : 0 < ‖μ‖^2 := sq_pos_of_pos (norm_pos_iff.mpr
    (PaperConsequences.mean_ne_zero_of_rawPolar hm ha ha1 hx0 hx1 hx hr))
  have hv := (PaperConsequences.centered_variance_le q μ (by omega) hmean hq).1
  have hn : 1-b a x ≤ ‖μ‖^2 := by
    have hh := Complex.sq_norm_sub_sq_re μ
    rw [hx] at hh
    unfold b
    nlinarith only [hh, sq_nonneg μ.im, sq_nonneg (x-a)]
  have hratio : variance (q.map (fun z => z-μ)) / ‖μ‖^2 ≤ b a x / (1-b a x) := by
    apply (div_le_div_iff₀ hs hc).mpr
    have hh := mul_le_mul_of_nonneg_right hv hc.le
    nlinarith only [hh, hn]
  have hA := PaperPolar.alpha_pos (by omega : 0 < q.card) ha ha1
  have hb := (le_div_iff₀ (by positivity : 0 < 3+alpha q.card a)).mp
    (b_le_alpha (by omega : 0 < q.card) ha ha1 hx0 hx1 hr)
  have hbound : b a x / (1-b a x) ≤ alpha q.card a / 3 := by
    apply (div_le_iff₀ hc).mpr
    nlinarith only [hb]
  have hm' : (7 : ℝ) ≤ q.card := by exact_mod_cast hm
  have hd : 0 < (q.card : ℝ)-1 := by linarith
  refine ⟨hratio, hbound, ?_, ?_⟩
  · unfold Gamma
    rw [Multiset.card_map, mul_comm ((q.card : ℝ)-1), ← div_div]
    exact (div_le_div_of_nonneg_right (hratio.trans hbound) hd.le).trans_eq (div_div _ _ _)
  · apply (div_lt_iff₀ (by positivity : 0 < 3*((q.card : ℝ)-1))).mpr
    unfold alpha
    have hstrict : (q.card : ℝ)*(1-a^2) < 2*q.card*(1-a) := by
      nlinarith only [mul_pos (show (0 : ℝ) < q.card by linarith) (sq_pos_of_pos (sub_pos.mpr ha1))]
    have hscale := mul_nonneg (show 0 ≤ (q.card : ℝ)-7 by linarith) (sub_pos.mpr ha1).le
    nlinarith only [hstrict, hscale]

/-- EX02: conditional finite remainder closure; no assertion of the premise globally. -/
theorem EX02 (q : Multiset ℂ) {μ : ℂ} {a x : ℝ}
    (hm : 7 ≤ q.card) (ha : 0 < a) (ha1 : a < 1)
    (hmean : q.sum = q.card * μ) (hq : ∀ z ∈ q, ‖z‖ ≤ 1)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hx : μ.re = x) (hr : RawPolar q.card a x)
    (hfin : PaperCenteredBound.majorant_Efin (q.map (fun z => z - μ)) μ (a * μ) ≤
      (1 - a) / 2) :
    Gamma (q.map (fun z => z-μ)) μ +
      PaperCenteredBound.majorant_Efin (q.map (fun z => z-μ)) μ (a*μ) < 8*(1-a)/9 ∧
    8*(1-a)/9 < 1-a ∧ 1-a ≤ 1-a*‖μ‖ ∧
    1 < ‖(q.card+1 : ℂ) *
      (∫ t in (0 : ℝ)..1, (q.map (fun z => 1-(a : ℂ)*t*z)).prod)‖ := by
  have hg := PaperConsequences.Gamma_lt_seven_eighteenths q hm ha ha1 hmean hq hx0 hx1 hx hr
  have hn := (PaperConsequences.centered_variance_le q μ (by omega) hmean hq).2
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · nlinarith only [mul_le_mul_of_nonneg_left hn ha.le]
  · exact PaperConsequences.norm_J_gt_one_of_majorant_half q hm ha ha1 hmean hq hx0 hx1 hx hr hfin

end Sendov.PaperMomentCorollaries
