import Sendov.Analytic.PaperTaylor

/-!
# Scale-adapted two-endpoint bounds for the actual origin integral

The exponent is always `(m - 1) / 2`, including in the middle-interval
exponential bound. Parameters are real; no integrality assumption is needed.
Source: first-origin-uniform/round4/REPORT.md §2 and round5/REPORT.md §3.
-/

namespace Sendov.PaperTwoEnd

open MeasureTheory

noncomputable def Q (x u : ℝ) : ℝ := 1 - 2 * x * u + u ^ 2
noncomputable def endpoint (m a x : ℝ) : ℝ := Q x a ^ (m / 2)
noncomputable def total (m a x : ℝ) : ℝ :=
  endpoint m a x + m * ∫ u in (0 : ℝ)..a, u * Q x u ^ ((m - 1) / 2)

lemma Q_beta (a x t : ℝ) : Q x (a * t) = PaperTaylor.beta a x t := by
  unfold Q PaperTaylor.beta
  ring

/-- Actual affine substitution `u = a*t`, including the Jacobian and weight. -/
theorem total_eq_budget {m a x : ℝ} (ha : 0 < a) :
    total m a x = PaperTaylor.budget m a x := by
  have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun u : ℝ => u * Q x u ^ ((m - 1) / 2)) ha.ne'
  simp only [mul_zero, mul_one, smul_eq_mul] at h
  have heq : (fun t : ℝ => a * t * Q x (a * t) ^ ((m - 1) / 2)) =
      (fun t : ℝ => a * (t * PaperTaylor.beta a x t ^ ((m - 1) / 2))) := by
    funext t
    rw [Q_beta]
    ring
  rw [heq, intervalIntegral.integral_const_mul] at h
  have h' : (∫ u in (0 : ℝ)..a, u * Q x u ^ ((m - 1) / 2)) =
      a ^ 2 * ∫ t in (0 : ℝ)..1, t * PaperTaylor.beta a x t ^ ((m - 1) / 2) := by
    calc
      _ = a * (a⁻¹ * ∫ u in (0 : ℝ)..a, u * Q x u ^ ((m - 1) / 2)) := by
        rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
      _ = _ := by rw [← h]; ring
  unfold total endpoint PaperTaylor.budget
  rw [h', ← Q_beta]
  simp only [mul_one]
  ring

lemma Q_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (u : ℝ) : 0 ≤ Q x u := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  unfold Q
  nlinarith [sq_nonneg (u - x)]

lemma Q_pos {a x u : ℝ} (ha1 : a < 1) (hx1 : x ≤ 1)
    (hu : u ∈ Set.Icc (0 : ℝ) a) : 0 < Q x u := by
  have : 0 ≤ 2 * u * (1 - x) := mul_nonneg (mul_nonneg (by norm_num) hu.1)
    (sub_nonneg.mpr hx1)
  unfold Q
  nlinarith [sq_pos_of_pos (show 0 < 1 - u by linarith [hu.2])]

lemma continuous_weight {p : ℝ} (hp : 0 ≤ p) (x : ℝ) :
    Continuous (fun u : ℝ => u * Q x u ^ p) :=
  continuous_id.mul ((continuous_rpow_const hp).comp (by unfold Q; fun_prop))

/-- The left quadratic is dominated by a linear chord, extended only to its zero. -/
lemma integral_left_le {p x s : ℝ} (hp : 0 < p) (hx : 0 < x) (hx1 : x ≤ 1)
    (hs : 0 ≤ s) (hsx : s ≤ x) :
    (∫ u in (0 : ℝ)..s, u * Q x u ^ p) ≤
      1 / (x ^ 2 * ((p + 1) * (p + 2))) := by
  have hc : Continuous (fun u : ℝ => u * (1 - x * u) ^ p) :=
    continuous_id.mul ((continuous_rpow_const hp.le).comp (by fun_prop))
  have hsz : s ≤ 1 / x := by
    apply (le_div_iff₀ hx).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsx hx.le]
  have hle : (∫ u in (0 : ℝ)..s, u * Q x u ^ p) ≤
      ∫ u in (0 : ℝ)..s, u * (1 - x * u) ^ p := by
    apply intervalIntegral.integral_mono_on hs ((continuous_weight hp.le x).intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)
    intro u hu
    apply mul_le_mul_of_nonneg_left _ hu.1
    apply Real.rpow_le_rpow (Q_nonneg hx.le hx1 u) _ hp.le
    have := mul_nonneg hu.1 (show 0 ≤ x - u by linarith [hu.2])
    unfold Q
    nlinarith
  have hrest : 0 ≤ ∫ u in s..1 / x, u * (1 - x * u) ^ p := by
    apply intervalIntegral.integral_nonneg hsz
    intro u hu
    have := (le_div_iff₀ hx).mp hu.2
    exact mul_nonneg (by linarith [hu.1]) (Real.rpow_nonneg (by nlinarith) _)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 s) (hc.intervalIntegrable s (1 / x))
  rw [integral_chord_lin hp hx] at hadd
  linarith

/-- The sharp rational left bound, before the strict `4/(m*x²)` simplification. -/
theorem left_le {m a x : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (hx : 0 < x) (hx1 : x ≤ 1) :
    m * (∫ u in (0 : ℝ)..min a x, u * Q x u ^ ((m - 1) / 2)) ≤
      4 * m / ((m + 1) * (m + 3) * x ^ 2) := by
  have h := mul_le_mul_of_nonneg_left
    (integral_left_le (p := (m - 1) / 2) (by linarith) hx hx1
      (le_min ha.le hx.le) (min_le_right a x)) (show 0 ≤ m by linarith)
  have heq : 4 * m / ((m + 1) * (m + 3) * x ^ 2) =
      m * (1 / (x ^ 2 * (((m - 1) / 2 + 1) * ((m - 1) / 2 + 2)))) := by
    rw [show ((m - 1) / 2 + 1) * ((m - 1) / 2 + 2) = (m + 1) * (m + 3) / 4 by ring]
    field_simp
  rw [heq]
  exact h

theorem left_lt {m a x : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (hx : 0 < x) (hx1 : x ≤ 1) :
    m * (∫ u in (0 : ℝ)..min a x, u * Q x u ^ ((m - 1) / 2)) <
      4 / (m * x ^ 2) := by
  apply (left_le hm ha hx hx1).trans_lt
  have hm0 : 0 < m := by linarith
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [sq_pos_of_pos hx, mul_pos (sq_pos_of_pos hx) (show 0 < 4 * m + 3 by linarith)]

/-- If the vertex is outside the integration interval there is no right tail. -/
theorem total_lt_left_endpoint {m a x : ℝ} (hm : 7 ≤ m) (ha : 0 < a)
    (hx : 0 < x) (hx1 : x ≤ 1) (hax : a ≤ x) :
    total m a x < 4 / (m * x ^ 2) + endpoint m a x := by
  have h := left_lt hm ha hx hx1
  rw [min_eq_left hax] at h
  unfold total
  linarith

/-- Exact split at the quadratic's vertex. -/
lemma total_split {m a x : ℝ} (hm : 7 ≤ m) :
    total m a x = endpoint m a x +
      m * (∫ u in (0 : ℝ)..x, u * Q x u ^ ((m - 1) / 2)) +
      m * (∫ u in x..a, u * Q x u ^ ((m - 1) / 2)) := by
  have hc := continuous_weight (x := x) (show 0 ≤ (m - 1) / 2 by linarith)
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 x) (hc.intervalIntegrable x a)
  unfold total
  rw [← h]
  ring

/-- On the right side of the vertex the quadratic is bounded by its right endpoint. -/
lemma Q_le_endpoint {a x u : ℝ} (hxa : x ≤ a) (hu : u ∈ Set.Icc x a) :
    Q x u ≤ Q x a := by
  have := mul_nonneg (sub_nonneg.mpr hu.2) (show 0 ≤ a + u - 2 * x by linarith [hu.1])
  unfold Q
  nlinarith

lemma integral_right_le_endpoint {p a x : ℝ} (hp : 0 ≤ p) (hx : 0 ≤ x)
    (hx1 : x ≤ 1) (hxa : x ≤ a) :
    (∫ u in x..a, u * Q x u ^ p) ≤ Q x a ^ p * ((a ^ 2 - x ^ 2) / 2) := by
  have hle : (∫ u in x..a, u * Q x u ^ p) ≤ ∫ u in x..a, Q x a ^ p * u := by
    apply intervalIntegral.integral_mono_on hxa ((continuous_weight hp x).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun u : ℝ => Q x a ^ p * u)).intervalIntegrable _ _)
    intro u hu
    rw [mul_comm (Q x a ^ p) u]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Q_nonneg hx hx1 u) (Q_le_endpoint hxa hu) hp)
      (show 0 ≤ u by linarith [hu.1])
  rw [intervalIntegral.integral_const_mul, integral_id] at hle
  exact hle

lemma endpoint_le_power {m a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx1 : x ≤ 1)
    (hc : 0 < PaperTaylor.chord a x) : endpoint m a x ≤ Q x a ^ ((m - 1) / 2) := by
  apply Real.rpow_le_rpow_of_exponent_ge (Q_pos ha1 hx1 ⟨ha.le, le_rfl⟩)
  · unfold PaperTaylor.chord at hc
    unfold Q
    nlinarith
  · linarith

/-- Unrelaxed exponent: this statement also applies at `m = 7,8`. -/
theorem total_lt_middle {m a x : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx : 0 < x) (hx1 : x ≤ 1) (hxa : x < a) (hax : a < 3 * x / 2) :
    total m a x < 4 / (m * x ^ 2) +
      (1 + 5 * m * x ^ 2 / 8) * Real.exp (-3 * (m - 1) * x ^ 2 / 8) := by
  have hp : 0 ≤ (m - 1) / 2 := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hb : 0 < Q x a := Q_pos ha1 hx1 ⟨ha.le, le_rfl⟩
  have hbnd : Q x a ≤ 1 - 3 * x ^ 2 / 4 := by
    have := mul_nonneg (show 0 ≤ a - x by linarith) (show 0 ≤ 3 * x / 2 - a by linarith)
    have := sq_nonneg (a - x)
    unfold Q
    nlinarith [sq_nonneg x]
  have hc : 0 < PaperTaylor.chord a x := by
    unfold PaperTaylor.chord
    apply mul_pos ha
    linarith
  have hexp : Q x a ^ ((m - 1) / 2) ≤ Real.exp (-3 * (m - 1) * x ^ 2 / 8) := by
    rw [Real.rpow_def_of_pos hb]
    apply Real.exp_le_exp.mpr
    have hlog := Real.log_le_sub_one_of_pos hb
    have := mul_le_mul_of_nonneg_right (hlog.trans (by linarith : Q x a - 1 ≤ -3 * x ^ 2 / 4)) hp
    nlinarith
  have hmass : (a ^ 2 - x ^ 2) / 2 ≤ 5 * x ^ 2 / 8 := by
    nlinarith [mul_nonneg (show 0 ≤ 3 * x / 2 - a by linarith)
      (show 0 ≤ 3 * x / 2 + a by positivity)]
  have hr := integral_right_le_endpoint hp hx.le hx1 hxa.le
  have hr' : m * (∫ u in x..a, u * Q x u ^ ((m - 1) / 2)) ≤
      (5 * m * x ^ 2 / 8) * Real.exp (-3 * (m - 1) * x ^ 2 / 8) := by
    have h1 := mul_le_mul_of_nonneg_right hexp (show 0 ≤ (a ^ 2 - x ^ 2) / 2 by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxa.le) (show 0 ≤ a + x by positivity)])
    have h2 := mul_le_mul_of_nonneg_left hmass (Real.exp_pos (-3 * (m - 1) * x ^ 2 / 8)).le
    have h3 := mul_le_mul_of_nonneg_left (hr.trans (h1.trans h2)) hm0
    calc
      _ ≤ m * (Real.exp (-3 * (m - 1) * x ^ 2 / 8) * (5 * x ^ 2 / 8)) := h3
      _ = _ := by ring
  have he := (endpoint_le_power ha ha1 hx1 hc).trans hexp
  have hl := left_lt hm ha hx hx1
  rw [min_eq_right hxa.le] at hl
  rw [total_split hm]
  nlinarith

/-- The weighted half of the right-tail integral, evaluated by a genuine primitive. -/
lemma integral_right_weight {p a x : ℝ} (hp : 0 ≤ p) :
    (∫ u in x..a, (u - x) * Q x u ^ p) =
      (Q x a ^ (p + 1) - Q x x ^ (p + 1)) / (2 * (p + 1)) := by
  have hp1 : p + 1 ≠ 0 := by linarith
  have hd : ∀ u : ℝ, HasDerivAt (fun u : ℝ => Q x u ^ (p + 1) / (2 * (p + 1)))
      ((u - x) * Q x u ^ p) u := by
    intro u
    have hq : HasDerivAt (fun u : ℝ => Q x u) (2 * (u - x)) u := by
      unfold Q
      convert! ((hasDerivAt_const u 1).sub ((hasDerivAt_id u).const_mul (2 * x))).add
        ((hasDerivAt_id u).pow 2) using 1
      simp only [id_eq]
      ring
    have h := (hq.rpow_const (p := p + 1) (Or.inr (by linarith))).div_const (2 * (p + 1))
    convert! h using 1
    rw [show p + 1 - 1 = p by ring]
    field_simp
  have hc : Continuous (fun u : ℝ => (u - x) * Q x u ^ p) :=
    (continuous_id.sub continuous_const).mul
      ((continuous_rpow_const hp).comp (by unfold Q; fun_prop))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (hc.intervalIntegrable x a)
  rw [h]
  ring

/-- Exact affine-power integral used for the secant majorant on the right. -/
lemma integral_affine_power {p v l : ℝ} (hp : 0 ≤ p) (hl : 0 < l) :
    (∫ w in (0 : ℝ)..l, (v + l * w) ^ p) =
      ((v + l ^ 2) ^ (p + 1) - v ^ (p + 1)) / (l * (p + 1)) := by
  have hp1 : p + 1 ≠ 0 := by linarith
  have hd : ∀ w : ℝ, HasDerivAt (fun w : ℝ => (v + l * w) ^ (p + 1) / (l * (p + 1)))
      ((v + l * w) ^ p) w := by
    intro w
    have h := (((hasDerivAt_id w).const_mul l).const_add v).rpow_const
      (p := p + 1) (Or.inr (by linarith))
    convert! h.div_const (l * (p + 1)) using 1
    rw [show p + 1 - 1 = p by ring]
    simp only [id_eq, mul_one]
    field_simp
  have hc : Continuous (fun w : ℝ => (v + l * w) ^ p) :=
    (continuous_rpow_const hp).comp (by fun_prop)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun w _ => hd w)
    (hc.intervalIntegrable 0 l)
  rw [h]
  simp only [mul_zero, add_zero, ← pow_two]
  ring

/-- The unweighted half of the right tail is controlled by its rising secant. -/
lemma integral_right_unweighted {p a x : ℝ} (hp : 0 ≤ p) (hx : 0 ≤ x)
    (hx1 : x ≤ 1) (hxa : x < a) :
    (∫ u in x..a, Q x u ^ p) ≤
      (Q x a ^ (p + 1) - Q x x ^ (p + 1)) / ((a - x) * (p + 1)) := by
  have hshift := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := a - x)
    (fun u : ℝ => Q x u ^ p) x
  simp only [add_zero, add_sub_cancel] at hshift
  rw [← hshift]
  have hq : (fun w : ℝ => Q x (x + w) ^ p) = (fun w : ℝ => (1 - x ^ 2 + w ^ 2) ^ p) := by
    funext w
    congr 1
    unfold Q
    ring
  rw [hq]
  have hcq : Continuous (fun w : ℝ => (1 - x ^ 2 + w ^ 2) ^ p) :=
    (continuous_rpow_const hp).comp (by fun_prop)
  have hcl : Continuous (fun w : ℝ => (1 - x ^ 2 + (a - x) * w) ^ p) :=
    (continuous_rpow_const hp).comp (by fun_prop)
  have hle : (∫ w in (0 : ℝ)..a - x, (1 - x ^ 2 + w ^ 2) ^ p) ≤
      ∫ w in (0 : ℝ)..a - x, (1 - x ^ 2 + (a - x) * w) ^ p := by
    apply intervalIntegral.integral_mono_on (sub_nonneg.mpr hxa.le)
      (hcq.intervalIntegrable _ _) (hcl.intervalIntegrable _ _)
    intro w hw
    apply Real.rpow_le_rpow _ _ hp
    · nlinarith [sq_nonneg w]
    · nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
  rw [integral_affine_power hp (sub_pos.mpr hxa)] at hle
  have hqa : 1 - x ^ 2 + (a - x) ^ 2 = Q x a := by unfold Q; ring
  have hqx : 1 - x ^ 2 = Q x x := by unfold Q; ring
  rw [hqa, hqx] at hle
  rw [hqx]
  exact hle

/-- Scale-adapted right-tail estimate: the weight and offset cost at most `E` and `4E`.
Both terms are actual integrals, not assumed error budgets. -/
lemma right_le_five_endpoint {m a x : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx : 0 < x) (hx1 : x ≤ 1) (hc : 0 < PaperTaylor.chord a x)
    (hsep : 3 * x / 2 ≤ a) :
    m * (∫ u in x..a, u * Q x u ^ ((m - 1) / 2)) ≤ 5 * endpoint m a x := by
  let p := (m - 1) / 2
  let D := Q x a ^ (p + 1) - Q x x ^ (p + 1)
  have hp : 0 ≤ p := by dsimp [p]; linarith
  have hp1 : 0 < p + 1 := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hxa : x < a := by linarith
  have hl : 0 < a - x := sub_pos.mpr hxa
  have hb : 0 < Q x a := Q_pos ha1 hx1 ⟨ha.le, le_rfl⟩
  have hb1 : Q x a ≤ 1 := by unfold PaperTaylor.chord at hc; unfold Q; nlinarith
  have hE : 0 ≤ endpoint m a x := Real.rpow_nonneg hb.le _
  have hD : D ≤ endpoint m a x := by
    have hv := Real.rpow_nonneg (Q_nonneg hx.le hx1 x) (p + 1)
    have hbE : Q x a ^ (p + 1) ≤ endpoint m a x :=
      Real.rpow_le_rpow_of_exponent_ge hb hb1 (by dsimp [p]; linarith)
    dsimp [D]
    linarith
  have hw : m * (∫ u in x..a, (u - x) * Q x u ^ p) ≤ endpoint m a x := by
    rw [integral_right_weight hp, ← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 2 * (p + 1) by positivity)).mpr
    have h := mul_le_mul_of_nonneg_left hD hm0
    change m * D ≤ endpoint m a x * (2 * (p + 1))
    dsimp [p] at *
    nlinarith
  have hc4 : m * x ≤ 4 * ((a - x) * (p + 1)) := by
    have h := mul_nonneg (show 0 ≤ 2 * (a - x) - x by linarith) (show 0 ≤ m + 1 by linarith)
    dsimp [p]
    nlinarith
  have hu : m * x * (∫ u in x..a, Q x u ^ p) ≤ 4 * endpoint m a x := by
    have h := mul_le_mul_of_nonneg_left (integral_right_unweighted hp hx.le hx1 hxa)
      (show 0 ≤ m * x by positivity)
    apply h.trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (mul_pos hl hp1)).mpr
    have h1 := mul_le_mul_of_nonneg_left hD (show 0 ≤ m * x by positivity)
    have h2 := mul_le_mul_of_nonneg_right hc4 hE
    change m * x * D ≤ 4 * endpoint m a x * ((a - x) * (p + 1))
    nlinarith
  have hcq : Continuous (fun u : ℝ => Q x u ^ p) :=
    (continuous_rpow_const hp).comp (by unfold Q; fun_prop)
  have hiw : IntervalIntegrable (fun u : ℝ => (u - x) * Q x u ^ p) volume x a :=
    ((continuous_id.sub continuous_const).mul hcq).intervalIntegrable x a
  have hiu := (hcq.intervalIntegrable x a (μ := volume)).const_mul x
  have hsplit : (∫ u in x..a, u * Q x u ^ p) =
      (∫ u in x..a, (u - x) * Q x u ^ p) + x * ∫ u in x..a, Q x u ^ p := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hiw hiu]
    apply intervalIntegral.integral_congr
    intro u _
    ring
  change m * (∫ u in x..a, u * Q x u ^ p) ≤ _
  rw [hsplit]
  nlinarith

/-- The separated two-endpoint estimate, including the boundary `a = 3*x/2`. -/
theorem total_lt_separated {m a x : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx : 0 < x) (hx1 : x ≤ 1) (hc : 0 < PaperTaylor.chord a x)
    (hsep : a ≤ x ∨ 3 * x / 2 ≤ a) :
    total m a x < 4 / (m * x ^ 2) + 6 * endpoint m a x := by
  rcases hsep with hax | hax
  · have h := total_lt_left_endpoint hm ha hx hx1 hax
    have hE : 0 ≤ endpoint m a x := Real.rpow_nonneg (Q_nonneg hx.le hx1 a) _
    linarith
  · have hxa : x ≤ a := by linarith
    have hr := right_le_five_endpoint hm ha ha1 hx hx1 hc hax
    have hl := left_lt hm ha hx hx1
    rw [min_eq_right hxa] at hl
    rw [total_split hm]
    linarith

/-- Separated estimate directly on the original `t`-coordinate budget. -/
theorem budget_lt_separated {m a x : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx : 0 < x) (hx1 : x ≤ 1) (hc : 0 < PaperTaylor.chord a x)
    (hsep : a ≤ x ∨ 3 * x / 2 ≤ a) :
    PaperTaylor.budget m a x < 4 / (m * x ^ 2) +
      6 * PaperTaylor.beta a x 1 ^ (m / 2) := by
  rw [← total_eq_budget ha]
  simpa only [endpoint, ← Q_beta, mul_one] using total_lt_separated hm ha ha1 hx hx1 hc hsep

/-- Middle estimate directly on the original budget, with the unrelaxed exponent. -/
theorem budget_lt_middle {m a x : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx : 0 < x) (hx1 : x ≤ 1) (hxa : x < a) (hax : a < 3 * x / 2) :
    PaperTaylor.budget m a x < 4 / (m * x ^ 2) +
      (1 + 5 * m * x ^ 2 / 8) * Real.exp (-3 * (m - 1) * x ^ 2 / 8) := by
  rw [← total_eq_budget ha]
  exact total_lt_middle hm ha ha1 hx hx1 hxa hax

end Sendov.PaperTwoEnd
