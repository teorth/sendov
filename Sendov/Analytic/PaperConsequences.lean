import Sendov.Analytic.PaperSecant
import Sendov.Analytic.PaperCenteredBound
import Sendov.Analytic.PaperUniform
import Sendov.Counterexample.Identities

/-!
# Finite and limiting-model consequences

AS03 concerns fixed natural degree only. EX03 retains the additional root-distance
product hypothesis and the actual polynomial factorizations. EX01/02 retain the
unproved finite-majorant hypothesis. AS05 is a theorem about the exponential
model, not an assertion of convergence to it. Historical cutoffs are restrictions
of the proved degree-256 theorem.
-/

noncomputable section
open scoped BigOperators
open Polynomial Filter
namespace Sendov.PaperConsequences

/-- AS03: the exact finite endpoint has its stated value at zero. -/
theorem U1_zero (m : ℕ) : PaperSecant.U1 m 0 = 1 / ((m : ℝ) + 1) := by
  simp [PaperSecant.U1]

/-- AS03: two-sided continuity gives, in particular, the fixed-degree right limit. -/
theorem tendsto_U1_zero (m : ℕ) :
    Tendsto (PaperSecant.U1 m) (nhds 0) (nhds (1 / ((m : ℝ) + 1))) := by
  have hc : ContinuousAt (PaperSecant.U1 m) 0 := by
    unfold PaperSecant.U1
    apply ContinuousAt.div <;> first | fun_prop | positivity
  simpa only [U1_zero] using hc.tendsto

/-- The paper's one-sided limit, with fixed m (not uniform in degree). -/
theorem tendsto_U1_zero_right (m : ℕ) :
    Tendsto (PaperSecant.U1 m) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (1 / ((m : ℝ) + 1))) :=
  (tendsto_U1_zero m).mono_left nhdsWithin_le_nhds

theorem U1_limit_lt_one {m : ℕ} (hm : 1 ≤ m) : 1 / ((m : ℝ) + 1) < 1 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  exact (div_lt_one (by positivity)).mpr (by linarith)

/-- AS03: one epsilon excludes all real means simultaneously, at fixed degree. -/
theorem exists_small_radius_not_rawPolar {m : ℕ} (hm : 1 ≤ m) :
    ∃ ε > (0 : ℝ), ∀ a : ℝ, 0 < a → a < ε →
      ∀ x : ℝ, -1 ≤ x → x ≤ 1 → ¬ PaperPolar.RawPolar m a x := by
  have he : ∀ᶠ a in nhds (0 : ℝ), PaperSecant.U1 m a < 1 :=
    (tendsto_U1_zero m).eventually (gt_mem_nhds (U1_limit_lt_one hm))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min ε 1, lt_min hε (by norm_num), ?_⟩
  intro a ha haε x hx0 hx1 hr
  have ha1 : a < 1 := haε.trans_le (min_le_right _ _)
  have hdist : dist a 0 < ε := by
    simpa [Real.dist_eq, abs_of_pos ha] using haε.trans_le (min_le_left ε 1)
  exact (not_lt_of_ge (PaperSecant.one_le_U1 ha ha1 hx0 hx1 hr)) (he hdist)

private lemma prod_norm (q : Multiset ℂ) : (q.map norm).prod = ‖q.prod‖ := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v q ih => simp [ih]

private lemma prod_norm_rpow (q : Multiset ℂ) (r : ℝ) :
    (q.map (fun v => ‖v‖ ^ r)).prod = ‖q.prod‖ ^ r := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v q ih => simp [ih, Real.mul_rpow (norm_nonneg v) (norm_nonneg q.prod)]

/-- The AM–GM step, for every positive real moment (repeated roots allowed). -/
theorem moment_ge_card_of_one_le_norm_prod (q : Multiset ℂ) {r : ℝ}
    (hr : 0 < r) (hp : 1 ≤ ‖q.prod‖) :
    (q.card : ℝ) ≤ (q.map (fun v => ‖v‖ ^ r)).sum := by
  by_cases hcard : q.card = 0
  · have hq := Multiset.card_eq_zero.mp hcard
    subst q
    simp
  have hc : (0 : ℝ) < q.card := by exact_mod_cast (Nat.pos_of_ne_zero hcard)
  have h := Sendov.Multiset.prod_le_mean_pow (q.map (fun v => ‖v‖ ^ r)) (by
    intro v hv
    obtain ⟨w, _, rfl⟩ := Multiset.mem_map.mp hv
    exact Real.rpow_nonneg (norm_nonneg _) _)
  rw [prod_norm_rpow, Multiset.card_map] at h
  have hp' : 1 ≤ ‖q.prod‖ ^ r := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hp hr.le
  have hs : 0 ≤ (q.map (fun v => ‖v‖ ^ r)).sum := by
    apply Multiset.sum_nonneg
    intro v hv
    obtain ⟨w, _, rfl⟩ := Multiset.mem_map.mp hv
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hmean : 1 ≤ (q.map (fun v => ‖v‖ ^ r)).sum / q.card := by
    by_contra hn
    have hh := pow_lt_one₀ (div_nonneg hs hc.le) (lt_of_not_ge hn) hcard
    exact (not_lt_of_ge (hp'.trans h)) hh
  simpa only [one_mul] using (le_div_iff₀ hc).mp hmean

/-- EX03: p'(a) evaluated through the actual root and inverse-critical-root
factorizations. The positive root-distance product is deduced, not assumed. -/
theorem root_distance_product_identity {m : ℕ} {p : ℂ[X]} {c a : ℂ}
    {q z : Multiset ℂ} (hc : c ≠ 0) (hq : ∀ v ∈ q, v ≠ 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p = C (((m + 1 : ℕ) : ℂ) * c) *
      ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    0 < (z.map (fun w => ‖a - w‖)).prod ∧
    (q.map norm).prod = ((m : ℝ) + 1) / (z.map (fun w => ‖a - w‖)).prod := by
  have hid := congrArg norm (Sendov.prod_sub_mul_prod hc hq hpz hpq)
  have hz : (z.map (fun w => ‖a - w‖)).prod = ‖(z.map (fun w => a - w)).prod‖ := by
    simpa only [Multiset.map_map, Function.comp_def] using prod_norm (z.map (fun w => a - w))
  have hncast : ‖(m : ℂ) + 1‖ = (m : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (m + 1)
  simp only [norm_mul, Nat.cast_add, Nat.cast_one, hncast] at hid
  have hpos : 0 < ‖(z.map (fun w => a - w)).prod‖ := by
    have hn := norm_nonneg (z.map (fun w => a - w)).prod
    have hm : (0 : ℝ) < m + 1 := by positivity
    by_contra h
    have hz0 : ‖(z.map (fun w => a - w)).prod‖ = 0 := le_antisymm (le_of_not_gt h) hn
    rw [hz0, mul_zero] at hid
    linarith
  refine ⟨hz.symm ▸ hpos, ?_⟩
  rw [prod_norm, hz, eq_div_iff hpos.ne']
  exact hid

/-- EX03: the extra root-product region forces every positive real moment.
No pointwise unit-disk hypothesis is needed for this separate obstruction. -/
theorem moment_ge_degree_of_root_distance_product {m : ℕ} {p : ℂ[X]} {c a : ℂ}
    {q z : Multiset ℂ} (_hm : 1 ≤ m) (hqcard : q.card = m)
    (_hzcard : z.card = m) (hc : c ≠ 0) (hq : ∀ v ∈ q, v ≠ 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p = C (((m + 1 : ℕ) : ℂ) * c) *
      ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod)
    (hprod : (z.map (fun w => ‖a - w‖)).prod ≤ (m : ℝ) + 1)
    {r : ℝ} (hr : 0 < r) : (m : ℝ) ≤ (q.map (fun v => ‖v‖ ^ r)).sum := by
  obtain ⟨hpos, hid⟩ := root_distance_product_identity hc hq hpz hpq
  have hp : 1 ≤ ‖q.prod‖ := by
    rw [← prod_norm, hid]
    exact (le_div_iff₀ hpos).mpr (by simpa using hprod)
  simpa only [hqcard] using moment_ge_card_of_one_le_norm_prod q hr hp

/-- The actual centered variance, not an independent scalar surrogate. -/
theorem centered_variance_le (q : Multiset ℂ) (μ : ℂ) (hm : 0 < q.card)
    (hmean : q.sum = q.card * μ) (hq : ∀ v ∈ q, ‖v‖ ≤ 1) :
    PaperCentered.variance (q.map (fun v => v - μ)) ≤ 1 - ‖μ‖ ^ 2 ∧ ‖μ‖ ≤ 1 := by
  have hc : (0 : ℝ) < q.card := by exact_mod_cast hm
  have hs := PaperCoefficient.sum_norm_add_sq (q.map (fun v => v - μ)) μ
  rw [PaperCentered.centered_sum q μ hmean] at hs
  have hmap : (q.map (fun v => v - μ)).map (fun w => ‖μ + w‖ ^ 2) =
      q.map (fun v => ‖v‖ ^ 2) := by
    simp only [Multiset.map_map, Function.comp_def]
    congr 1
    funext v
    congr 2
    ring
  rw [hmap] at hs
  simp only [Multiset.card_map, map_zero, mul_zero, Complex.zero_re, add_zero] at hs
  have hsum : (q.map (fun v => ‖v‖ ^ 2)).sum ≤ (q.card : ℝ) := by
    simpa using Multiset.sum_map_le_sum_map (fun v : ℂ => ‖v‖ ^ 2) (fun _ => (1 : ℝ))
      (fun v hv => pow_le_one₀ (norm_nonneg v) (hq v hv))
  have hv0 : 0 ≤ ((q.map (fun v => v - μ)).map (fun v => ‖v‖ ^ 2)).sum := by
    apply Multiset.sum_nonneg
    intro v hv
    obtain ⟨w, _, rfl⟩ := Multiset.mem_map.mp hv
    exact sq_nonneg _
  have hv : PaperCentered.variance (q.map (fun v => v - μ)) ≤ 1 - ‖μ‖ ^ 2 := by
    unfold PaperCentered.variance
    rw [Multiset.card_map, div_le_iff₀ hc]
    nlinarith only [hs, hsum]
  refine ⟨hv, ?_⟩
  have hsq : ‖μ‖ ^ 2 ≤ 1 := by nlinarith only [hs, hsum, hv0, hc]
  nlinarith only [hsq, norm_nonneg μ]

/-- Raw polar and the actual real part make the complex mean nonzero. -/
theorem mean_ne_zero_of_rawPolar {m : ℕ} {a x : ℝ} {μ : ℂ}
    (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hx : μ.re = x) (hr : PaperPolar.RawPolar m a x) : μ ≠ 0 := by
  have hg := (PaperPolar.geometry hm ha ha1 hx0 hx1 hr).1
  intro hz
  simp only [hz, Complex.zero_re] at hx
  linarith

/-- EX01: the factor-three bound on the actual variance-to-mean-square ratio. -/
theorem variance_ratio_le_alpha (q : Multiset ℂ) {μ : ℂ} {a x : ℝ}
    (hm : 7 ≤ q.card) (ha : 0 < a) (ha1 : a < 1)
    (hmean : q.sum = q.card * μ) (hq : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hx : μ.re = x)
    (hr : PaperPolar.RawPolar q.card a x) :
    PaperCentered.variance (q.map (fun v => v - μ)) / ‖μ‖ ^ 2 ≤
      PaperPolar.alpha q.card a / 3 := by
  have hμ := mean_ne_zero_of_rawPolar hm ha ha1 hx0 hx1 hx hr
  have hs : 0 < ‖μ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hμ)
  have hv := (centered_variance_le q μ (by omega) hmean hq).1
  have hb := PaperPolar.b_le_alpha (by omega : 0 < q.card) ha ha1 hx0 hx1 hr
  have hα := PaperPolar.alpha_pos (by omega : 0 < q.card) ha ha1
  have hprod := (le_div_iff₀ (by positivity : 0 < 3 + PaperPolar.alpha q.card a)).mp hb
  have hnorm : 1 - PaperPolar.b a x ≤ ‖μ‖ ^ 2 := by
    have hh := Complex.sq_norm_sub_sq_re μ
    rw [hx] at hh
    unfold PaperPolar.b
    nlinarith only [hh, sq_nonneg (μ.im), sq_nonneg (x - a)]
  have hh := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 3 + PaperPolar.alpha q.card a by positivity)
  apply (div_le_iff₀ hs).mpr
  nlinarith only [hv, hprod, hh]

/-- EX01: the finite centered correction is strictly less than 7h/18, h=1-a. -/
theorem Gamma_lt_seven_eighteenths (q : Multiset ℂ) {μ : ℂ} {a x : ℝ}
    (hm : 7 ≤ q.card) (ha : 0 < a) (ha1 : a < 1)
    (hmean : q.sum = q.card * μ) (hq : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hx : μ.re = x)
    (hr : PaperPolar.RawPolar q.card a x) :
    PaperCentered.Gamma (q.map (fun v => v - μ)) μ < 7 * (1 - a) / 18 := by
  have hm' : (7 : ℝ) ≤ q.card := by exact_mod_cast hm
  have hd : 0 < (q.card : ℝ) - 1 := by linarith
  have hv := variance_ratio_le_alpha q hm ha ha1 hmean hq hx0 hx1 hx hr
  have hg : PaperCentered.Gamma (q.map (fun v => v - μ)) μ ≤
      PaperPolar.alpha q.card a / (3 * ((q.card : ℝ) - 1)) := by
    unfold PaperCentered.Gamma
    rw [Multiset.card_map, mul_comm ((q.card : ℝ) - 1), ← div_div]
    exact (div_le_div_of_nonneg_right hv hd.le).trans_eq (div_div _ _ _)
  apply hg.trans_lt
  apply (div_lt_iff₀ (by positivity : 0 < 3 * ((q.card : ℝ) - 1))).mpr
  unfold PaperPolar.alpha
  have hstrict : (q.card : ℝ) * (1 - a ^ 2) < 2 * q.card * (1 - a) := by
    nlinarith only [mul_pos (show (0 : ℝ) < q.card by linarith) (sq_pos_of_pos (sub_pos.mpr ha1))]
  have hscale := mul_nonneg (show 0 ≤ (q.card : ℝ) - 7 by linarith) (sub_pos.mpr ha1).le
  nlinarith only [hstrict, hscale]

/-- EX02: conditional closure. The finite square-root majorant estimate remains
an explicit hypothesis, so this does not assert a global centered-budget theorem. -/
theorem norm_J_gt_one_of_majorant_half (q : Multiset ℂ) {μ : ℂ} {a x : ℝ}
    (hm : 7 ≤ q.card) (ha : 0 < a) (ha1 : a < 1)
    (hmean : q.sum = q.card * μ) (hq : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hx : μ.re = x)
    (hr : PaperPolar.RawPolar q.card a x)
    (hfin : PaperCenteredBound.majorant_Efin (q.map (fun v => v - μ)) μ (a * μ) ≤
      (1 - a) / 2) :
    1 < ‖(q.card + 1 : ℂ) *
      (∫ t in (0 : ℝ)..1, (q.map (fun v => 1 - (a : ℂ) * t * v)).prod)‖ := by
  have hg := Gamma_lt_seven_eighteenths q hm ha ha1 hmean hq hx0 hx1 hx hr
  have hn := (centered_variance_le q μ (by omega) hmean hq).2
  apply PaperCenteredBound.C_budget q a μ (by omega) ha.le hmean
    (mean_ne_zero_of_rawPolar hm ha ha1 hx0 hx1 hx hr)
  have hh := mul_le_mul_of_nonneg_left hn ha.le
  nlinarith only [hg, hfin, hh, ha1]

/-- AS05: the entire feasible exponential-model family has positive budget.
This is not a finite-degree convergence claim. The endpoint x=1 is included. -/
theorem limiting_exponential_model {ℓ x : ℝ} (hℓ : 0 < ℓ)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hG : 1 ≤ ∫ t in (0 : ℝ)..1, Real.exp (ℓ * (2 * x * t - 1))) :
    1 / 2 < x ∧ 1 - x ≤ ℓ * x ^ 2 / 6 ∧
      (1 - x) * (5 - x) ≤ (1 + ℓ) * x ^ 2 - 1 ∧
      0 < (1 + ℓ) * x ^ 2 - 1 := by
  have hG' : 1 ≤ ∫ t in (0 : ℝ)..1,
      Real.exp (ℓ * (-1 + (2 - 2 * (1 - x)) * t)) := by
    convert hG using 1
    congr 1
    funext t
    congr 1
    ring
  have hb := Sendov.beta_le hℓ (by linarith : 0 ≤ 2 * (1 - x)) hG'
  have hb' := (le_div_iff₀ (by positivity : 0 < 3 + ℓ)).mp hb
  have hhalf : 1 / 2 < x := by nlinarith only [hb', hℓ]
  have hsq := mul_nonneg hℓ.le (sq_nonneg (1 - x))
  have hmodel : 1 - x ≤ ℓ * x ^ 2 / 6 := by nlinarith only [hb', hsq]
  have hbudget : (1 - x) * (5 - x) ≤ (1 + ℓ) * x ^ 2 - 1 := by
    nlinarith only [hmodel]
  refine ⟨hhalf, hmodel, hbudget, ?_⟩
  rcases hx1.eq_or_lt with he | he
  · subst x
    nlinarith only [hℓ]
  · have hp := mul_pos (sub_pos.mpr he) (show 0 < 5 - x by linarith)
    linarith only [hp, hbudget]

/-- UN: every old all-a cutoff is an explicit restriction of uniform D.
In particular M=512,10000,100000,1000000 are covered with identical assumptions. -/
theorem old_all_a_cutoff {M m : ℕ} {a x : ℝ} (hM : 256 ≤ M) (hm : M ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : PaperPolar.RawPolar m a x) :
    PaperTaylor.budget (m : ℝ) a x < 1 - (m : ℝ) * a / ((m : ℝ) + 1) :=
  PaperUniform.uniform_D (hM.trans hm) ha ha1 hx0 hx1 hr

end Sendov.PaperConsequences
