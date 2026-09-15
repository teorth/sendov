import Sendov.Analytic.PaperGlobalPolar
import Sendov.Analytic.PaperTwoEnd
import Sendov.Analytic.PaperTail

/-!
# Retained historical bounds on the actual origin integral

Round 4, §§3–4: these are quantitative bounds on `T`, not merely the later
weaker domain conclusion `T < B`. They are independent of `PaperUniform`.
The logarithmic certificate uses `log 256 = 8 log 2`; the tail certificates
are finite rational Taylor lower bounds, checked by the kernel.
-/
namespace Sendov.PaperHistoricalBounds

open PaperPolar

lemma log_257_gt : (27 : ℝ) / 5 < Real.log 257 := by
  have h := Real.log_two_gt_d9
  have he : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
  have hmono : Real.log 256 ≤ Real.log 257 := Real.log_le_log (by norm_num) (by norm_num)
  rw [he] at hmono
  linarith

/-- Historical scale bound, strictly stronger than the degree-256 scale bound. -/
theorem degree_mul_sq_gt {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) : (32 : ℝ) / 3 < (m : ℝ) * x ^ 2 := by
  have hm' : (512 : ℝ) ≤ m := by exact_mod_cast hm
  have hN : (257 : ℝ) ≤ ((m : ℝ) + 2) / 2 := by linarith
  have hN0 : 0 < ((m : ℝ) + 2) / 2 := by positivity
  have hlog : (27 : ℝ) / 5 < Real.log (((m : ℝ) + 2) / 2) :=
    log_257_gt.trans_le (Real.log_le_log (by norm_num) hN)
  have hc := (div_le_iff₀ hN0).mp
    (PaperGlobalPolar.log_degree_le_c (by omega) ha ha1 hx0 hx1 hr)
  have hcx : c a x ≤ x ^ 2 := by unfold c b; nlinarith [sq_nonneg (x - a)]
  have hmul := mul_le_mul_of_nonneg_right hcx hN0.le
  have hscaled : (27 : ℝ) / 5 < (((m : ℝ) + 2) / 2) * x ^ 2 := by nlinarith
  have hfactor : (m : ℝ) + 2 ≤ (257 : ℝ) / 256 * m := by linarith
  have hlast := mul_le_mul_of_nonneg_right hfactor (sq_nonneg x)
  nlinarith

/-- The original, weaker exponent `exp(-k/3)` is valid for every real `m ≥ 9`. -/
theorem budget_lt_middle {m a x : ℝ} (hm : 9 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx : 0 < x) (hx1 : x ≤ 1) (hxa : x < a) (hax : a < 3 * x / 2) :
    PaperTaylor.budget m a x < 4 / (m * x ^ 2) +
      (1 + 5 * m * x ^ 2 / 8) * Real.exp (-(m * x ^ 2) / 3) := by
  apply (PaperTwoEnd.budget_lt_middle (by linarith) ha ha1 hx hx1 hxa hax).trans_le
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_nonneg (show 0 ≤ m - 9 by linarith) (sq_nonneg x)]

/-- Monotonicity for the historical correction, without stronger later exponents. -/
lemma middle_antitone : AntitoneOn
    (fun k : ℝ => (1 + 5 * k / 8) * Real.exp (-k / 3)) (Set.Ici 3) := by
  have hd (k : ℝ) : HasDerivAt
      (fun k : ℝ => (1 + 5 * k / 8) * Real.exp (-k / 3))
      ((5 / 8 - (1 + 5 * k / 8) / 3) * Real.exp (-k / 3)) k := by
    convert! (((((hasDerivAt_id k).const_mul 5).div_const 8).const_add 1).mul
      (((hasDerivAt_id k).neg.div_const 3).exp)) using 1
    dsimp
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) (by fun_prop)
  · intro k hk; exact (hd k).differentiableAt.differentiableWithinAt
  · intro k hk
    rw [(hd k).deriv]
    have hk' : 3 ≤ k := interior_subset hk
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le

lemma middle_base : (1 + 5 * ((32 : ℝ) / 3) / 8) * Real.exp (-(32 / 3) / 3) < 9 / 40 := by
  have he : (920 : ℝ) / 27 < Real.exp (32 / 9) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 32 / 9) 16
    norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
    linarith
  rw [show (-(32 / 3) / 3 : ℝ) = -(32 / 9) by ring, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_lt_iff₀ (Real.exp_pos _)).mpr
  linarith

lemma chord_eq (a x : ℝ) : PaperTaylor.chord a x = c a x := by
  unfold PaperTaylor.chord c b
  ring

lemma beta_one_eq (a x : ℝ) : PaperTaylor.beta a x 1 = b a x := by
  unfold PaperTaylor.beta b
  ring

/-- The actual `t`-coordinate integral is less than `3/5`, for every `m ≥ 512`. -/
theorem budget_lt_three_fifths {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) : PaperTaylor.budget m a x < 3 / 5 := by
  have hm' : (512 : ℝ) ≤ m := by exact_mod_cast hm
  have hg := geometry (by omega : 7 ≤ m) ha ha1 hx0 hx1 hr
  have hx : 0 < x := by linarith [hg.1]
  have hc : 0 < PaperTaylor.chord a x := by rw [chord_eq]; exact hg.2
  have hk := degree_mul_sq_gt hm ha ha1 hx0 hx1 hr
  have hleft : 4 / ((m : ℝ) * x ^ 2) < 3 / 8 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith
  by_cases hsep : a ≤ x ∨ 3 * x / 2 ≤ a
  · have h := PaperTwoEnd.budget_lt_separated (m := (m : ℝ)) (by linarith) ha ha1 hx hx1 hc hsep
    have he := PaperGlobalPolar.endpoint_le (by omega) ha ha1 hx0 hx1 hr
    rw [beta_one_eq] at h
    have he' : 4 / ((m : ℝ) + 2) ≤ 4 / 514 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
      linarith
    linarith
  · push Not at hsep
    have h := budget_lt_middle (m := (m : ℝ)) (by linarith) ha ha1 hx hx1 hsep.1 hsep.2
    have hmono := middle_antitone (by norm_num : (32 / 3 : ℝ) ∈ Set.Ici 3)
      (show (m : ℝ) * x ^ 2 ∈ Set.Ici 3 by apply Set.mem_Ici.mpr; linarith) hk.le
    dsimp at hmono
    nlinarith only [h, hleft, hmono, middle_base]

/-- Independent real-degree tail certificate for the retained-`a` bulk bound. -/
lemma middle_tail {m : ℝ} (hm : 512 ≤ m) :
    m * (1 + m / 40) * Real.exp (-m / 75) < 24 := by
  have h1 := PaperTail.power_exp_antitone (n := 1) (c := 1 / 75) (d := 0)
    (by norm_num) (by norm_num : (0 : ℝ) < 512) (by norm_num) (by norm_num)
    (show (512 : ℝ) ∈ Set.Ici 512 by simp) hm hm
  have h2 := PaperTail.power_exp_antitone (n := 2) (c := 1 / 75) (d := 0)
    (by norm_num) (by norm_num : (0 : ℝ) < 512) (by norm_num) (by norm_num)
    (show (512 : ℝ) ∈ Set.Ici 512 by simp) hm hm
  have he : (512 : ℝ) * (1 + 512 / 40) < 24 * Real.exp (512 / 75) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 512 / 75) 16
    norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
    linarith
  have hb : (512 : ℝ) * (1 + 512 / 40) * Real.exp (-512 / 75) < 24 := by
    rw [show (-512 / 75 : ℝ) = -(512 / 75) by ring, Real.exp_neg, ← div_eq_mul_inv]
    exact (div_lt_iff₀ (Real.exp_pos _)).mpr he
  dsimp at h1 h2
  simp only [sub_zero, pow_one] at h1 h2
  have heq (t : ℝ) : -(1 / 75 : ℝ) * t = -t / 75 := by ring
  simp only [heq] at h1 h2
  nlinarith only [h1, h2, hb]

/-- Retaining `a`: the real integral satisfies `T < 40/(m*a²)` on the historical bulk domain. -/
theorem budget_lt_forty {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (ha2 : 2 / 5 ≤ a)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hr : RawPolar m a x) :
    PaperTaylor.budget m a x < 40 / ((m : ℝ) * a ^ 2) := by
  have hm' : (512 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by positivity
  have hg := geometry (by omega : 7 ≤ m) ha ha1 hx0 hx1 hr
  have hx : 0 < x := by linarith [hg.1]
  have hc : 0 < PaperTaylor.chord a x := by rw [chord_eq]; exact hg.2
  have hsq : a ^ 2 / 4 < x ^ 2 := by nlinarith [hg.1]
  have hx25 : 1 / 25 ≤ x ^ 2 := by nlinarith
  have hk : (m : ℝ) / 25 ≤ (m : ℝ) * x ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hx25 hm0.le]
  have hleft : 4 / ((m : ℝ) * x ^ 2) < 16 / ((m : ℝ) * a ^ 2) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_pos hm0 (sub_pos.mpr hsq)]
  have htotal : PaperTaylor.budget m a x < 4 / ((m : ℝ) * x ^ 2) + 24 / m := by
    by_cases hsep : a ≤ x ∨ 3 * x / 2 ≤ a
    · have h := PaperTwoEnd.budget_lt_separated (m := (m : ℝ)) (by linarith) ha ha1 hx hx1 hc hsep
      have he := PaperGlobalPolar.endpoint_le (by omega) ha ha1 hx0 hx1 hr
      rw [beta_one_eq] at h
      have he' : 4 / ((m : ℝ) + 2) ≤ 4 / m := by
        apply (div_le_div_iff₀ (by positivity) hm0).mpr
        linarith
      have he24 : 6 * (4 / (m : ℝ)) = 24 / m := by ring
      linarith
    · push Not at hsep
      have h := budget_lt_middle (m := (m : ℝ)) (by linarith) ha ha1 hx hx1 hsep.1 hsep.2
      have hmono := middle_antitone
        (show (m : ℝ) / 25 ∈ Set.Ici 3 by apply Set.mem_Ici.mpr; linarith)
        (show (m : ℝ) * x ^ 2 ∈ Set.Ici 3 by apply Set.mem_Ici.mpr; linarith) hk
      dsimp at hmono
      have heq : (1 + 5 * ((m : ℝ) / 25) / 8) * Real.exp (-((m : ℝ) / 25) / 3) =
          (1 + (m : ℝ) / 40) * Real.exp (-(m : ℝ) / 75) := by
        congr 1
        · ring
        · congr 1
          ring
      rw [heq] at hmono
      have ht := (lt_div_iff₀ hm0).mpr (show
        (1 + (m : ℝ) / 40) * Real.exp (-(m : ℝ) / 75) * m < 24 by
          nlinarith only [middle_tail hm'])
      nlinarith only [h, hmono, ht]
  have hrest : 24 / (m : ℝ) ≤ 24 / ((m : ℝ) * a ^ 2) := by
    apply (div_le_div_iff₀ hm0 (by positivity)).mpr
    nlinarith only [mul_nonneg hm0.le (show 0 ≤ 1 - a ^ 2 by nlinarith)]
  have heq : 16 / ((m : ℝ) * a ^ 2) + 24 / ((m : ℝ) * a ^ 2) =
      40 / ((m : ℝ) * a ^ 2) := by ring
  linarith

/-- A general chord majorant, integrated to its zero (never the growing quadratic). -/
lemma integral_chord_le {p a x s : ℝ} (hp : 0 < p) (ha : 0 < a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hs : 0 < s) (hsa : s ≤ 2 * x - a) :
    (∫ u in (0 : ℝ)..a, u * PaperTwoEnd.Q x u ^ p) ≤
      1 / (s ^ 2 * ((p + 1) * (p + 2))) := by
  have hc : Continuous (fun u : ℝ => u * (1 - s * u) ^ p) :=
    continuous_id.mul ((continuous_rpow_const hp.le).comp (by fun_prop))
  have hzero : a ≤ 1 / s := by
    apply (le_div_iff₀ hs).mpr
    have hq := PaperTwoEnd.Q_nonneg hx hx1 a
    unfold PaperTwoEnd.Q at hq
    nlinarith [mul_le_mul_of_nonneg_right hsa ha.le]
  have hle : (∫ u in (0 : ℝ)..a, u * PaperTwoEnd.Q x u ^ p) ≤
      ∫ u in (0 : ℝ)..a, u * (1 - s * u) ^ p := by
    apply intervalIntegral.integral_mono_on ha.le
      ((PaperTwoEnd.continuous_weight hp.le x).intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)
    intro u hu
    apply mul_le_mul_of_nonneg_left _ hu.1
    apply Real.rpow_le_rpow (PaperTwoEnd.Q_nonneg hx hx1 u) _ hp.le
    unfold PaperTwoEnd.Q
    nlinarith only [mul_nonneg hu.1 (show 0 ≤ 2 * x - s - u by linarith [hu.2])]
  have hrest : 0 ≤ ∫ u in a..1 / s, u * (1 - s * u) ^ p := by
    apply intervalIntegral.integral_nonneg hzero
    intro u hu
    have hz := (le_div_iff₀ hs).mp hu.2
    exact mul_nonneg (ha.le.trans hu.1) (Real.rpow_nonneg (by linarith) _)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a (1 / s))
  rw [integral_chord_lin hp hs] at hadd
  linarith

/-- Exact rational contribution of the chord, with a retained slope parameter. -/
lemma total_le_chord {m a x s : ℝ} (hm : 7 ≤ m) (ha : 0 < a)
    (hx : 0 < x) (hx1 : x ≤ 1) (hs : 0 < s) (hsa : s ≤ 2 * x - a) :
    PaperTwoEnd.total m a x ≤
      4 * m / ((m + 1) * (m + 3) * s ^ 2) + PaperTwoEnd.endpoint m a x := by
  have h := mul_le_mul_of_nonneg_left
    (integral_chord_le (p := (m - 1) / 2) (by linarith) ha hx.le hx1 hs hsa)
    (show 0 ≤ m by linarith)
  have heq : m * (1 / (s ^ 2 * (((m - 1) / 2 + 1) * ((m - 1) / 2 + 2)))) =
      4 * m / ((m + 1) * (m + 3) * s ^ 2) := by
    rw [show ((m - 1) / 2 + 1) * ((m - 1) / 2 + 2) = (m + 1) * (m + 3) / 4 by ring]
    field_simp
  rw [heq] at h
  unfold PaperTwoEnd.total
  linarith

/-- The same sharp rising-secant integral at the historical split `a ≥ 7*x/5`. -/
lemma right_le_six_endpoint {m a x : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx : 0 < x) (hx1 : x ≤ 1) (hc : 0 < PaperTaylor.chord a x)
    (hsep : 7 * x / 5 ≤ a) :
    m * (∫ u in x..a, u * PaperTwoEnd.Q x u ^ ((m - 1) / 2)) ≤
      6 * PaperTwoEnd.endpoint m a x := by
  let p := (m - 1) / 2
  let D := PaperTwoEnd.Q x a ^ (p + 1) - PaperTwoEnd.Q x x ^ (p + 1)
  have hp : 0 ≤ p := by dsimp [p]; linarith
  have hp1 : 0 < p + 1 := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hxa : x < a := by linarith
  have hl : 0 < a - x := sub_pos.mpr hxa
  have hb := PaperTwoEnd.Q_pos ha1 hx1 ⟨ha.le, le_rfl⟩
  have hb1 : PaperTwoEnd.Q x a ≤ 1 := by
    unfold PaperTaylor.chord at hc
    unfold PaperTwoEnd.Q
    nlinarith
  have hE : 0 ≤ PaperTwoEnd.endpoint m a x := Real.rpow_nonneg hb.le _
  have hD : D ≤ PaperTwoEnd.endpoint m a x := by
    have hv := Real.rpow_nonneg (PaperTwoEnd.Q_nonneg hx.le hx1 x) (p + 1)
    have hbE : PaperTwoEnd.Q x a ^ (p + 1) ≤ PaperTwoEnd.endpoint m a x :=
      Real.rpow_le_rpow_of_exponent_ge hb hb1 (by dsimp [p]; linarith)
    dsimp [D]
    linarith
  have hw : m * (∫ u in x..a, (u - x) * PaperTwoEnd.Q x u ^ p) ≤
      PaperTwoEnd.endpoint m a x := by
    rw [PaperTwoEnd.integral_right_weight hp, ← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 2 * (p + 1) by positivity)).mpr
    have h := mul_le_mul_of_nonneg_left hD hm0
    change m * D ≤ PaperTwoEnd.endpoint m a x * (2 * (p + 1))
    dsimp [p] at *
    nlinarith
  have hc5 : m * x ≤ 5 * ((a - x) * (p + 1)) := by
    have h := mul_nonneg (show 0 ≤ 5 * (a - x) - 2 * x by linarith)
      (show 0 ≤ m + 1 by linarith)
    dsimp [p]
    nlinarith
  have hu : m * x * (∫ u in x..a, PaperTwoEnd.Q x u ^ p) ≤
      5 * PaperTwoEnd.endpoint m a x := by
    have h := mul_le_mul_of_nonneg_left (PaperTwoEnd.integral_right_unweighted hp hx.le hx1 hxa)
      (show 0 ≤ m * x by positivity)
    apply h.trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (mul_pos hl hp1)).mpr
    have h1 := mul_le_mul_of_nonneg_left hD (show 0 ≤ m * x by positivity)
    have h2 := mul_le_mul_of_nonneg_right hc5 hE
    change m * x * D ≤ 5 * PaperTwoEnd.endpoint m a x * ((a - x) * (p + 1))
    nlinarith
  have hcq : Continuous (fun u : ℝ => PaperTwoEnd.Q x u ^ p) :=
    (continuous_rpow_const hp).comp (by unfold PaperTwoEnd.Q; fun_prop)
  have hiw : IntervalIntegrable (fun u : ℝ => (u - x) * PaperTwoEnd.Q x u ^ p)
      MeasureTheory.volume x a :=
    ((continuous_id.sub continuous_const).mul hcq).intervalIntegrable x a
  have hiu := (hcq.intervalIntegrable x a (μ := MeasureTheory.volume)).const_mul x
  have hsplit : (∫ u in x..a, u * PaperTwoEnd.Q x u ^ p) =
      (∫ u in x..a, (u - x) * PaperTwoEnd.Q x u ^ p) +
        x * ∫ u in x..a, PaperTwoEnd.Q x u ^ p := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hiw hiu]
    apply intervalIntegral.integral_congr
    intro u _
    ring
  change m * (∫ u in x..a, u * PaperTwoEnd.Q x u ^ p) ≤ _
  rw [hsplit]
  nlinarith

/-- Historical A5 on the actual integral, before endpoint suppression. -/
theorem total_le_A5 {m a x : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx : 0 < x) (hx1 : x ≤ 1) (hc : 0 < PaperTaylor.chord a x) :
    PaperTwoEnd.total m a x ≤ 100 * m / (9 * (m + 1) * (m + 3) * x ^ 2) +
      29 * PaperTwoEnd.endpoint m a x := by
  have hm0 : 0 < m := by linarith
  have hE : 0 ≤ PaperTwoEnd.endpoint m a x :=
    Real.rpow_nonneg (PaperTwoEnd.Q_nonneg hx.le hx1 a) _
  by_cases hsep : 7 * x / 5 ≤ a
  · have hr := right_le_six_endpoint hm ha ha1 hx hx1 hc hsep
    have hl := PaperTwoEnd.left_le hm ha hx hx1
    rw [min_eq_right (by linarith : x ≤ a)] at hl
    have hcoeff : 4 * m / ((m + 1) * (m + 3) * x ^ 2) ≤
        100 * m / (9 * (m + 1) * (m + 3) * x ^ 2) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [mul_nonneg hm0.le (mul_nonneg
        (mul_nonneg (show 0 ≤ m + 1 by linarith) (show 0 ≤ m + 3 by linarith)) (sq_nonneg x))]
    rw [PaperTwoEnd.total_split hm]
    linarith
  · have h := total_le_chord hm ha hx hx1 (show 0 < 3 * x / 5 by positivity)
      (show 3 * x / 5 ≤ 2 * x - a by linarith)
    have heq : 4 * m / ((m + 1) * (m + 3) * (3 * x / 5) ^ 2) =
        100 * m / (9 * (m + 1) * (m + 3) * x ^ 2) := by field_simp; ring
    rw [heq] at h
    linarith

/-- Historical A5b, retaining its exact rational degree factor. -/
theorem total_le_A5b {m a x : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx : 0 < x) (hx1 : x ≤ 1) (hc : 0 < PaperTaylor.chord a x) :
    PaperTwoEnd.total m a x ≤ 16 * m / ((m + 1) * (m + 3) * x ^ 2) +
      13 * PaperTwoEnd.endpoint m a x := by
  have hm0 : 0 < m := by linarith
  have hE : 0 ≤ PaperTwoEnd.endpoint m a x :=
    Real.rpow_nonneg (PaperTwoEnd.Q_nonneg hx.le hx1 a) _
  by_cases hsep : 3 * x / 2 ≤ a
  · have hr := PaperTwoEnd.right_le_five_endpoint hm ha ha1 hx hx1 hc hsep
    have hl := PaperTwoEnd.left_le hm ha hx hx1
    rw [min_eq_right (by linarith : x ≤ a)] at hl
    have hcoeff : 4 * m / ((m + 1) * (m + 3) * x ^ 2) ≤
        16 * m / ((m + 1) * (m + 3) * x ^ 2) := by
      apply div_le_div_of_nonneg_right (by linarith) (by positivity)
    rw [PaperTwoEnd.total_split hm]
    linarith
  · have h := total_le_chord hm ha hx hx1 (show 0 < x / 2 by positivity)
      (show x / 2 ≤ 2 * x - a by linarith)
    have heq : 4 * m / ((m + 1) * (m + 3) * (x / 2) ^ 2) =
        16 * m / ((m + 1) * (m + 3) * x ^ 2) := by field_simp; ring
    rw [heq] at h
    linarith

/-- A5 with raw polar, all degrees `m ≥ 7`, on the actual `t`-coordinate integral. -/
theorem budget_le_A5 {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) : PaperTaylor.budget m a x ≤
      100 * m / (9 * ((m : ℝ) + 1) * (m + 3) * x ^ 2) + 116 / ((m : ℝ) + 2) := by
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hg := geometry hm ha ha1 hx0 hx1 hr
  have hx : 0 < x := by linarith [hg.1]
  have hc : 0 < PaperTaylor.chord a x := by rw [chord_eq]; exact hg.2
  have h := total_le_A5 hm' ha ha1 hx hx1 hc
  have he := PaperGlobalPolar.endpoint_le hm ha ha1 hx0 hx1 hr
  rw [PaperTwoEnd.total_eq_budget ha] at h
  have hendpoint : PaperTwoEnd.endpoint m a x = b a x ^ ((m : ℝ) / 2) := by
    unfold PaperTwoEnd.endpoint PaperTwoEnd.Q b
    congr 1
    ring
  rw [hendpoint] at h
  have heq : 29 * (4 / ((m : ℝ) + 2)) = 116 / ((m : ℝ) + 2) := by ring
  linarith

/-- A5b with raw polar, including the odd degree `7` and even degree `8`. -/
theorem budget_le_A5b {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) : PaperTaylor.budget m a x ≤
      16 * m / (((m : ℝ) + 1) * (m + 3) * x ^ 2) + 52 / ((m : ℝ) + 2) := by
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hg := geometry hm ha ha1 hx0 hx1 hr
  have hx : 0 < x := by linarith [hg.1]
  have hc : 0 < PaperTaylor.chord a x := by rw [chord_eq]; exact hg.2
  have h := total_le_A5b hm' ha ha1 hx hx1 hc
  have he := PaperGlobalPolar.endpoint_le hm ha ha1 hx0 hx1 hr
  rw [PaperTwoEnd.total_eq_budget ha] at h
  have hendpoint : PaperTwoEnd.endpoint m a x = b a x ^ ((m : ℝ) / 2) := by
    unfold PaperTwoEnd.endpoint PaperTwoEnd.Q b
    congr 1
    ring
  rw [hendpoint] at h
  have heq : 13 * (4 / ((m : ℝ) + 2)) = 52 / ((m : ℝ) + 2) := by ring
  linarith

/-- The historical bulk constant, with no degree-512 or lower-radius assumption. -/
theorem budget_lt_bulk116 {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) : PaperTaylor.budget m a x < 116 / ((m : ℝ) * a ^ 2) := by
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by linarith
  have hg := geometry hm ha ha1 hx0 hx1 hr
  have hx : 0 < x := by linarith [hg.1]
  have hsq : a ^ 2 < 4 * x ^ 2 := by nlinarith [hg.1]
  have h := budget_le_A5b hm ha ha1 hx0 hx1 hr
  have hleft : 16 * m / (((m : ℝ) + 1) * (m + 3) * x ^ 2) < 16 / ((m : ℝ) * x ^ 2) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_pos (sq_pos_of_pos hx) (show 0 < 4 * (m : ℝ) + 3 by linarith)]
  have hleft' : 16 / ((m : ℝ) * x ^ 2) < 64 / ((m : ℝ) * a ^ 2) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_pos hm0 (sub_pos.mpr hsq)]
  have htail : 52 / ((m : ℝ) + 2) ≤ 52 / ((m : ℝ) * a ^ 2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_nonneg hm0.le (show 0 ≤ 1 - a ^ 2 by nlinarith)]
  have heq : 64 / ((m : ℝ) * a ^ 2) + 52 / ((m : ℝ) * a ^ 2) =
      116 / ((m : ℝ) * a ^ 2) := by ring
  linarith

/-- The old bulk cutoff follows from a stronger `T` estimate, not from a uniform D theorem. -/
theorem budget_lt_one_sub_of_bulk116 {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : RawPolar m a x) (hbulk : 116 ≤ (m : ℝ) * a ^ 2 * (1 - a)) :
    PaperTaylor.budget m a x < 1 - a := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  apply (budget_lt_bulk116 hm ha ha1 hx0 hx1 hr).trans_le
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hbulk]

/-- The historical improved bulk cutoff retains the strict margin to `1-a`. -/
theorem budget_lt_one_sub_of_bulk40 {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (ha2 : 2 / 5 ≤ a)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hr : RawPolar m a x)
    (hbulk : 40 ≤ (m : ℝ) * a ^ 2 * (1 - a)) :
    PaperTaylor.budget m a x < 1 - a := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  apply (budget_lt_forty hm ha ha1 ha2 hx0 hx1 hr).trans_le
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hbulk]

/-- All small radii are closed with the stronger historical bound, independently of D. -/
theorem budget_lt_one_sub_of_small {m : ℕ} {a x : ℝ} (hm : 512 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (ha2 : a ≤ 2 / 5)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hr : RawPolar m a x) :
    PaperTaylor.budget m a x < 1 - a :=
  (budget_lt_three_fifths hm ha ha1 hx0 hx1 hr).trans_le (by linarith)

end Sendov.PaperHistoricalBounds
