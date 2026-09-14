import Sendov.Common.Chord
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Finite Taylor budget for the actual origin integral

Source: first-origin-uniform/REPORT.md §4.2 (R3), inherited unchanged in
round3/REPORT.md §1 and round4/REPORT.md. The analytic bound requires only
`7 ≤ m`, `0 < a < 1`, `x ≤ 1`, and `0 < c = a(2x-a)`.
In particular raw polar, the lower bound `-1 ≤ x`, integrality of `m`, and
any smallness assumption on `m(1-a)` are not needed for the Taylor estimate.
-/

namespace Sendov.PaperTaylor

open MeasureTheory

noncomputable def beta (a x t : ℝ) : ℝ := 1 - 2 * a * x * t + a ^ 2 * t ^ 2
noncomputable def defect (a x : ℝ) : ℝ := 2 * a * (1 - x)
noncomputable def chord (a x : ℝ) : ℝ := a * (2 * x - a)
noncomputable def budget (m a x : ℝ) : ℝ :=
  beta a x 1 ^ (m / 2) + m * a ^ 2 *
    ∫ t in (0 : ℝ)..1, t * beta a x t ^ ((m - 1) / 2)

lemma beta_decomposition (a x t : ℝ) :
    beta a x t = (1 - a * t) ^ 2 + defect a x * t := by
  unfold beta defect
  ring

lemma defect_nonneg {a x : ℝ} (ha : 0 ≤ a) (hx : x ≤ 1) :
    0 ≤ defect a x := mul_nonneg (by positivity) (sub_nonneg.mpr hx)

lemma beta_pos {a x t : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : x ≤ 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < beta a x t := by
  have hat : a * t < 1 := lt_of_le_of_lt (mul_le_of_le_one_right ha.le ht.2) ha1
  rw [beta_decomposition]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (by linarith))
    (mul_nonneg (defect_nonneg ha.le hx) ht.1)

lemma beta_le_chord {a x t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    beta a x t ≤ 1 - chord a x * t := by
  have h := mul_nonneg (sq_nonneg a) (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
  unfold beta chord
  nlinarith

lemma chord_lt_one {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : x ≤ 1) :
    chord a x < 1 := by
  have h := beta_pos ha ha1 hx (t := 1) (by norm_num)
  unfold beta chord at *
  nlinarith

/-- A genuine finite second-order Taylor majorant, proved by two derivative comparisons.
The lower endpoint is positive, as it is for `(1-at)^2` with `a<1`. -/
lemma rpow_taylor_le {p v w : ℝ} (hp : 2 ≤ p) (hv : 0 < v) (hvw : v ≤ w) :
    w ^ p ≤ v ^ p + p * (w - v) * v ^ (p - 1) +
      (p * (p - 1) / 2) * (w - v) ^ 2 * w ^ (p - 2) := by
  let K := p * (p - 1) * w ^ (p - 2)
  let g := fun z : ℝ => p * z ^ (p - 1) - p * v ^ (p - 1) - K * (z - v)
  have hg : ∀ z ∈ Set.Icc v w, HasDerivAt g
      (p * (p - 1) * z ^ (p - 2) - K) z := by
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt (lt_of_lt_of_le hv hz.1)
    convert! (((Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hz0)).const_mul p).sub_const
      (p * v ^ (p - 1))).sub
      (((hasDerivAt_id z).sub_const v).const_mul K) using 1
    ring_nf
  have hgmono : AntitoneOn g (Set.Icc v w) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    · exact fun z hz => (hg z hz).continuousAt.continuousWithinAt
    · intro z hz
      exact (hg z (interior_subset hz)).hasDerivWithinAt
    · intro z hz
      have hz' := interior_subset hz
      have hpow := Real.rpow_le_rpow (by linarith [hz'.1] : 0 ≤ z) hz'.2
        (by linarith : 0 ≤ p - 2)
      dsimp [K]
      nlinarith [mul_le_mul_of_nonneg_left hpow
        (show 0 ≤ p * (p - 1) by nlinarith)]
  have hgnonpos : ∀ z ∈ Set.Icc v w, g z ≤ 0 := by
    intro z hz
    have h := hgmono (Set.left_mem_Icc.mpr hvw) hz hz.1
    simpa [g] using h
  let f := fun z : ℝ => z ^ p - v ^ p - p * (z - v) * v ^ (p - 1) -
    K / 2 * (z - v) ^ 2
  have hf : ∀ z ∈ Set.Icc v w, HasDerivAt f (g z) z := by
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt (lt_of_lt_of_le hv hz.1)
    convert! (((Real.hasDerivAt_rpow_const (p := p) (Or.inl hz0)).sub_const (v ^ p)).sub
      ((((hasDerivAt_id z).sub_const v).const_mul p).mul_const (v ^ (p - 1)))).sub
      ((((hasDerivAt_id z).sub_const v).pow 2).const_mul (K / 2)) using 1
    dsimp [g]
    ring_nf
  have hfmono : AntitoneOn f (Set.Icc v w) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    · exact fun z hz => (hf z hz).continuousAt.continuousWithinAt
    · exact fun z hz => (hf z (interior_subset hz)).hasDerivWithinAt
    · exact fun z hz => hgnonpos z (interior_subset hz)
  have h := hfmono (Set.left_mem_Icc.mpr hvw) (Set.right_mem_Icc.mpr hvw) hvw
  dsimp [f, K] at h
  nlinarith

/-- The missing quadratic Beta moment, with a real exponent. -/
lemma integral_sq_mul_rpow {s : ℝ} (hs : 0 < s) :
    (∫ t in (0 : ℝ)..1, t ^ 2 * (1 - t) ^ s) =
      2 / ((s + 1) * (s + 2) * (s + 3)) := by
  have hrefl : (∫ t in (0 : ℝ)..1, t ^ 2 * (1 - t) ^ s) =
      ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * t ^ s := by
    simpa using (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
      (fun t : ℝ => (1 - t) ^ 2 * t ^ s) 1)
  have heq : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      (1 - t) ^ 2 * t ^ s = t ^ s - 2 * t ^ (s + (1 : ℕ)) + t ^ (s + (2 : ℕ)) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [Real.rpow_add_natCast' ht.1 (by positivity : s + (1 : ℕ) ≠ 0),
      Real.rpow_add_natCast' ht.1 (by positivity : s + (2 : ℕ) ≠ 0)]
    ring
  have hi : ∀ n : ℕ, IntervalIntegrable (fun t : ℝ => t ^ (s + n)) volume 0 1 := by
    intro n
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hi0 : IntervalIntegrable (fun t : ℝ => t ^ s) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  rw [hrefl, intervalIntegral.integral_congr heq,
    intervalIntegral.integral_add (hi0.sub ((hi 1).const_mul 2)) (hi 2),
    intervalIntegral.integral_sub hi0 ((hi 1).const_mul 2),
    intervalIntegral.integral_const_mul,
    integral_rpow_zero_one (by linarith), integral_rpow_zero_one (by push_cast; linarith),
    integral_rpow_zero_one (by push_cast; linarith)]
  push_cast
  field_simp
  ring

lemma integral_chord_sq {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    (∫ t in (0 : ℝ)..1 / c, t ^ 2 * (1 - c * t) ^ s) =
      2 / (c ^ 3 * ((s + 1) * (s + 2) * (s + 3))) := by
  have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1 / c)
    (fun y : ℝ => (y / c) ^ 2 * (1 - y) ^ s) hc.ne'
  simp only [mul_div_cancel_left₀ _ hc.ne', mul_one_div_cancel hc.ne', mul_zero,
    div_pow, div_mul_eq_mul_div, intervalIntegral.integral_div, integral_sq_mul_rpow hs,
    smul_eq_mul] at h
  rw [h]
  field_simp

/-- Extension to the zero of a nonnegative chord, for any natural weight. -/
lemma integral_chord_extend {s c : ℝ} (hs : 0 ≤ s) (hc : 0 < c) (hc1 : c ≤ 1)
    (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ k * (1 - c * t) ^ s) ≤
      ∫ t in (0 : ℝ)..1 / c, t ^ k * (1 - c * t) ^ s := by
  have hend : (1 : ℝ) ≤ 1 / c := (le_div_iff₀ hc).mpr (by simpa using hc1)
  have hcont : Continuous (fun t : ℝ => t ^ k * (1 - c * t) ^ s) :=
    (continuous_pow k).mul ((continuous_rpow_const hs).comp (by fun_prop))
  have hrest : 0 ≤ ∫ t in (1 : ℝ)..1 / c, t ^ k * (1 - c * t) ^ s := by
    refine intervalIntegral.integral_nonneg hend ?_
    intro t ht
    have ht' := (le_div_iff₀ hc).mp ht.2
    exact mul_nonneg (pow_nonneg (by linarith [ht.1]) k)
      (Real.rpow_nonneg (by nlinarith) s)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hcont.intervalIntegrable 0 1) (hcont.intervalIntegrable 1 (1 / c))
  linarith

lemma sq_rpow {u : ℝ} (hu : 0 ≤ u) (s : ℝ) : (u ^ 2) ^ s = u ^ (2 * s) := by
  rw [← Real.rpow_natCast u 2, ← Real.rpow_mul hu]
  norm_num

/-- Pointwise Taylor bound with the actual quadratic and its actual secant. -/
lemma beta_rpow_taylor {m a x t : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx : x ≤ 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t * beta a x t ^ ((m - 1) / 2) ≤
      t * (1 - a * t) ^ (m - 1) +
      ((m - 1) / 2 * defect a x) * (t ^ 2 * (1 - a * t) ^ (m - 3)) +
      ((m - 1) * (m - 3) / 8 * defect a x ^ 2) *
        (t ^ 3 * (1 - chord a x * t) ^ ((m - 5) / 2)) := by
  have hd := defect_nonneg ha.le hx
  have hu : 0 < 1 - a * t := by
    have := mul_le_of_le_one_right ha.le ht.2
    linarith
  have hβ := beta_pos ha ha1 hx ht
  have hvw : (1 - a * t) ^ 2 ≤ beta a x t := by
    rw [beta_decomposition]
    exact le_add_of_nonneg_right (mul_nonneg hd ht.1)
  have h := rpow_taylor_le (by linarith : 2 ≤ (m - 1) / 2)
    (sq_pos_of_pos hu) hvw
  have hdiff : beta a x t - (1 - a * t) ^ 2 = defect a x * t := by
    rw [beta_decomposition]
    ring
  rw [hdiff, sq_rpow hu.le, sq_rpow hu.le,
    show 2 * ((m - 1) / 2) = m - 1 by ring,
    show 2 * ((m - 1) / 2 - 1) = m - 3 by ring,
    show (m - 1) / 2 - 2 = (m - 5) / 2 by ring] at h
  have hpow := Real.rpow_le_rpow hβ.le (beta_le_chord ht)
    (by linarith : 0 ≤ (m - 5) / 2)
  have hcoef : 0 ≤ (m - 1) / 2 * ((m - 1) / 2 - 1) / 2 * (defect a x * t) ^ 2 := by
    apply mul_nonneg _ (sq_nonneg _)
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg (by linarith) (by linarith)
  have h2 := mul_le_mul_of_nonneg_left hpow hcoef
  have h3 := mul_le_mul_of_nonneg_left (h.trans (add_le_add le_rfl h2)) ht.1
  convert! h3 using 1
  ring

/-- Integrating the pointwise Taylor majorant. All integrability is proved here. -/
lemma integral_beta_taylor {m a x : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx : x ≤ 1) :
    (∫ t in (0 : ℝ)..1, t * beta a x t ^ ((m - 1) / 2)) ≤
      (∫ t in (0 : ℝ)..1, t * (1 - a * t) ^ (m - 1)) +
      ((m - 1) / 2 * defect a x) *
        (∫ t in (0 : ℝ)..1, t ^ 2 * (1 - a * t) ^ (m - 3)) +
      ((m - 1) * (m - 3) / 8 * defect a x ^ 2) *
        (∫ t in (0 : ℝ)..1, t ^ 3 * (1 - chord a x * t) ^ ((m - 5) / 2)) := by
  have hcont : ∀ (k : ℕ) (c s : ℝ), 0 ≤ s →
      Continuous (fun t : ℝ => t ^ k * (1 - c * t) ^ s) := by
    intro k c s hs
    exact (continuous_pow k).mul ((continuous_rpow_const hs).comp (by fun_prop))
  have hi0 : IntervalIntegrable (fun t : ℝ => t * (1 - a * t) ^ (m - 1)) volume 0 1 := by
    simpa using (hcont 1 a (m - 1) (by linarith)).intervalIntegrable 0 1
  have hi1 := ((hcont 2 a (m - 3) (by linarith)).intervalIntegrable 0 1 (μ := volume)).const_mul
    ((m - 1) / 2 * defect a x)
  have hi2 := ((hcont 3 (chord a x) ((m - 5) / 2) (by linarith)).intervalIntegrable 0 1
    (μ := volume)).const_mul ((m - 1) * (m - 3) / 8 * defect a x ^ 2)
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add hi0 hi1,
    ← intervalIntegral.integral_add (hi0.add hi1) hi2]
  apply intervalIntegral.integral_mono_on (by norm_num) _ ((hi0.add hi1).add hi2)
  · intro t ht
    exact beta_rpow_taylor hm ha ha1 hx ht
  · have hβ : Continuous (fun t : ℝ => t * beta a x t ^ ((m - 1) / 2)) :=
      continuous_id.mul ((continuous_rpow_const (by linarith : 0 ≤ (m - 1) / 2)).comp
        (by unfold beta; fun_prop))
    exact hβ.intervalIntegrable 0 1

/-- **(T)**, for the actual integral, not an assumed scalar budget.
It holds even for real `m ≥ 7`; raw polar is only needed elsewhere to supply `c > 0`.
Each nonnegative linear majorant is extended only as far as its zero. -/
theorem budget_le {m a x : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx : x ≤ 1) (hc : 0 < chord a x) :
    budget m a x ≤ 1 / (m + 1) + beta a x 1 ^ (m / 2) +
      defect a x / (a * (m - 2)) +
      12 * m * a ^ 2 * defect a x ^ 2 / (chord a x ^ 4 * (m + 1) * (m + 3)) := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m - 1 := by linarith
  have hm2 : 0 < m - 2 := by linarith
  have hm3 : 0 < m - 3 := by linarith
  have hmp1 : 0 < m + 1 := by linarith
  have hmp3 : 0 < m + 3 := by linarith
  have hd := defect_nonneg ha.le hx
  have hc1 := (chord_lt_one ha ha1 hx).le
  have h0 := integral_chord_extend (s := m - 1) (by linarith) ha ha1.le 1
  simp only [pow_one] at h0
  rw [integral_chord_lin hm1 ha] at h0
  have h1 := integral_chord_extend (s := m - 3) (by linarith) ha ha1.le 2
  rw [integral_chord_sq hm3 ha] at h1
  have h2 := integral_chord_extend (s := (m - 5) / 2) (by linarith) hc hc1 3
  rw [integral_chord_pow (by linarith) hc] at h2
  have hcoef1 : 0 ≤ (m - 1) / 2 * defect a x := mul_nonneg (by linarith) hd
  have hcoef2 : 0 ≤ (m - 1) * (m - 3) / 8 * defect a x ^ 2 := by positivity
  have hsum := (integral_beta_taylor hm ha ha1 hx).trans
    (add_le_add (add_le_add h0 (mul_le_mul_of_nonneg_left h1 hcoef1))
      (mul_le_mul_of_nonneg_left h2 hcoef2))
  have htotal := mul_le_mul_of_nonneg_left hsum (show 0 ≤ m * a ^ 2 by positivity)
  have heq : m * a ^ 2 *
      (1 / (a ^ 2 * ((m - 1 + 1) * (m - 1 + 2))) +
        ((m - 1) / 2 * defect a x) *
          (2 / (a ^ 3 * ((m - 3 + 1) * (m - 3 + 2) * (m - 3 + 3)))) +
        ((m - 1) * (m - 3) / 8 * defect a x ^ 2) *
          (6 / (chord a x ^ 4 * (((m - 5) / 2 + 1) * ((m - 5) / 2 + 2) *
            ((m - 5) / 2 + 3) * ((m - 5) / 2 + 4))))) =
      1 / (m + 1) + defect a x / (a * (m - 2)) +
        12 * m * a ^ 2 * defect a x ^ 2 / (chord a x ^ 4 * (m + 1) * (m + 3)) := by
    have he1 : m - 1 + 1 = m := by ring
    have he2 : m - 1 + 2 = m + 1 := by ring
    have he3 : m - 3 + 1 = m - 2 := by ring
    have he4 : m - 3 + 2 = m - 1 := by ring
    have he5 : m - 3 + 3 = m := by ring
    have he6 : ((m - 5) / 2 + 1) * ((m - 5) / 2 + 2) *
        ((m - 5) / 2 + 3) * ((m - 5) / 2 + 4) =
        (m - 3) * (m - 1) * (m + 1) * (m + 3) / 16 := by ring
    rw [he1, he2, he3, he4, he5, he6]
    field_simp [ha.ne', hc.ne', hm0.ne', hm1.ne', hm2.ne', hm3.ne', hmp1.ne', hmp3.ne']
    ring
  rw [heq] at htotal
  unfold budget
  linarith

lemma chord_eq_one_sub_beta (a x : ℝ) : chord a x = 1 - beta a x 1 := by
  unfold chord beta
  ring

lemma defect_eq_beta_sub_sq (a x : ℝ) : defect a x = beta a x 1 - (1 - a) ^ 2 := by
  unfold defect beta
  ring

/-- The paper's exact `b,c,d` notation, with `T` expanded as an integral. -/
theorem finite_taylor_budget {m a x : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx : x ≤ 1) (hc : 0 < 1 - beta a x 1) :
    let b := beta a x 1
    let c := 1 - b
    let d := 2 * a * (1 - x)
    b ^ (m / 2) + m * a ^ 2 * (∫ t in (0 : ℝ)..1, t * beta a x t ^ ((m - 1) / 2)) ≤
      1 / (m + 1) + b ^ (m / 2) + d / (a * (m - 2)) +
        12 * m * a ^ 2 * d ^ 2 / (c ^ 4 * (m + 1) * (m + 3)) := by
  have h := budget_le hm ha ha1 hx (by simpa [chord_eq_one_sub_beta] using hc)
  simpa only [budget, defect, chord_eq_one_sub_beta] using h

end Sendov.PaperTaylor
