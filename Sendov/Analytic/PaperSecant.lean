import Sendov.Analytic.PaperPolar
import Sendov.Analytic.PaperTaylor
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Curvature-corrected finite polar secant

Source: first-origin-uniform/round6/REPORT.md §§2–3. All endpoint formulas
use natural powers, including odd degrees. The gate below is sufficient;
no universal positivity claim is made.
-/
namespace Sendov.PaperSecant
open MeasureTheory

noncomputable def R (m : ℕ) (a x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, Ppolar a x t ^ ((m : ℝ) / 2)
noncomputable def U1 (m : ℕ) (a : ℝ) : ℝ :=
  ((a + (1 - a ^ 2)) ^ (m + 1) - a ^ (m + 1)) / (((m : ℝ) + 1) * (1 - a ^ 2))
noncomputable def U0 (m : ℕ) (a : ℝ) : ℝ :=
  2 * (1 - a ^ (m + 2)) / (((m : ℝ) + 2) * (1 - a ^ 2))
noncomputable def V0 (m : ℕ) (a : ℝ) : ℝ :=
  U0 m a - (m : ℝ) / 12 * a ^ (m - 2) * (1 - a ^ 2) ^ 2
noncomputable def S (m : ℕ) (a : ℝ) : ℝ :=
  a / 2 + (1 - a / 2) * (1 - V0 m a) / (U1 m a - V0 m a)
noncomputable def B (m : ℕ) (a : ℝ) : ℝ := 1 - (m : ℝ) * a / ((m : ℝ) + 1)
noncomputable def Wsec (m : ℕ) (a : ℝ) : ℝ :=
  1 / ((m : ℝ) + 1) + (PaperTaylor.beta a (S m a) 1) ^ (m / 2) +
    PaperTaylor.defect a (S m a) / (a * ((m : ℝ) - 2)) +
    12 * (m : ℝ) * a ^ 2 * PaperTaylor.defect a (S m a) ^ 2 /
      (PaperTaylor.chord a (S m a) ^ 4 * ((m : ℝ) + 1) * ((m : ℝ) + 3))
noncomputable def Fsec (m : ℕ) (a : ℝ) : ℝ := B m a - Wsec m a

lemma delta_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) : 0 < 1 - a ^ 2 := by
  nlinarith

lemma integrable_R (m : ℕ) (a x : ℝ) :
    IntervalIntegrable (fun t => Ppolar a x t ^ ((m : ℝ) / 2)) volume 0 1 :=
  ((continuous_rpow_const (by positivity : 0 ≤ (m : ℝ) / 2)).comp
    (continuous_Ppolar a x)).intervalIntegrable _ _

/-- Exact finite upper endpoint, not an exponential replacement. -/
theorem R_one {m : ℕ} {a : ℝ} (ha : 0 < a) (ha1 : a < 1) : R m a 1 = U1 m a := by
  have hd := delta_pos ha ha1
  have heq : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      Ppolar a 1 t ^ ((m : ℝ) / 2) = (a + (1 - a ^ 2) * t) ^ m := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have hid : Ppolar a 1 t = (a + (1 - a ^ 2) * t) ^ 2 := by unfold Ppolar; ring
    rw [hid, PaperTaylor.sq_rpow (add_nonneg ha.le (mul_nonneg hd.le ht.1)),
      show 2 * ((m : ℝ) / 2) = m by ring,
      Real.rpow_natCast]
  unfold R U1
  rw [intervalIntegral.integral_congr heq,
    intervalIntegral.integral_comp_add_mul (fun y : ℝ => y ^ m) hd.ne', integral_pow]
  simp only [mul_zero, add_zero, mul_one, smul_eq_mul]
  rw [mul_comm ((m : ℝ) + 1), ← div_div]
  ring

/-- Exact integral of the chord at `x = a/2`. -/
theorem integral_chord {m : ℕ} {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (∫ t in (0 : ℝ)..1, (a ^ 2 + (1 - a ^ 2) * t) ^ ((m : ℝ) / 2)) = U0 m a := by
  have hd := delta_pos ha ha1
  rw [intervalIntegral.integral_comp_add_mul (fun y : ℝ => y ^ ((m : ℝ) / 2)) hd.ne',
    integral_rpow (Or.inl (by have := Nat.cast_nonneg (α := ℝ) m; linarith : -1 < (m : ℝ) / 2))]
  simp only [mul_zero, add_zero, mul_one, smul_eq_mul]
  rw [show a ^ 2 + (1 - a ^ 2) = 1 by ring, Real.one_rpow,
    PaperTaylor.sq_rpow ha.le, show 2 * ((m : ℝ) / 2 + 1) = ((m + 2 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]
  unfold U0
  field_simp

/-- A derivative lower bound valid uniformly above a positive base. -/
lemma rpow_sub_lower {p q v w : ℝ} (hp : 1 ≤ p) (hq : 0 < q)
    (hqv : q ≤ v) (hvw : v ≤ w) :
    p * q ^ (p - 1) * (w - v) ≤ w ^ p - v ^ p := by
  let f := fun z : ℝ => z ^ p - p * q ^ (p - 1) * z
  have hf : ∀ z ∈ Set.Icc v w, HasDerivAt f
      (p * z ^ (p - 1) - p * q ^ (p - 1)) z := by
    intro z hz
    convert! (Real.hasDerivAt_rpow_const (p := p)
      (Or.inl (ne_of_gt (by linarith [hz.1] : 0 < z)))).sub
        ((hasDerivAt_id z).const_mul (p * q ^ (p - 1))) using 1
    simp
  have hmono : MonotoneOn f (Set.Icc v w) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    · exact fun z hz => (hf z hz).continuousAt.continuousWithinAt
    · exact fun z hz => (hf z (interior_subset hz)).hasDerivWithinAt
    · intro z hz
      have hz' := interior_subset hz
      have hpow := Real.rpow_le_rpow hq.le (hqv.trans hz'.1) (by linarith : 0 ≤ p - 1)
      exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left hpow (by linarith))
  have h := hmono (Set.left_mem_Icc.mpr hvw) (Set.right_mem_Icc.mpr hvw) hvw
  dsimp [f] at h
  nlinarith

lemma kernel_half (a t : ℝ) :
    Ppolar a (a / 2) t = (a ^ 2 + (1 - a ^ 2) * t) - (1 - a ^ 2) ^ 2 * t * (1 - t) := by
  unfold Ppolar
  ring

lemma kernel_half_ge {a t : ℝ} (ha : 0 < a) (ha1 : a < 1) (ht : 0 ≤ t) :
    a ^ 2 ≤ Ppolar a (a / 2) t := by
  have hd := delta_pos ha ha1
  have h : 0 ≤ a ^ 2 * t * (1 - a ^ 2) + t ^ 2 * (1 - a ^ 2) ^ 2 := by positivity
  unfold Ppolar
  nlinarith

/-- The actual pointwise curvature subtraction from the chord. -/
theorem curvature_pointwise {m : ℕ} {a t : ℝ} (hm : 2 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Ppolar a (a / 2) t ^ ((m : ℝ) / 2) ≤
      (a ^ 2 + (1 - a ^ 2) * t) ^ ((m : ℝ) / 2) -
        ((m : ℝ) / 2 * a ^ (m - 2) * (1 - a ^ 2) ^ 2) * (t * (1 - t)) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hq := kernel_half_ge ha ha1 ht.1
  have hgap : 0 ≤ (1 - a ^ 2) ^ 2 * t * (1 - t) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) ht.1) (sub_nonneg.mpr ht.2)
  have hvw : Ppolar a (a / 2) t ≤ a ^ 2 + (1 - a ^ 2) * t := by rw [kernel_half]; linarith
  have h := rpow_sub_lower (by linarith : 1 ≤ (m : ℝ) / 2) (sq_pos_of_pos ha) hq hvw
  rw [PaperTaylor.sq_rpow ha.le,
    show 2 * ((m : ℝ) / 2 - 1) = ((m - 2 : ℕ) : ℝ) by rw [Nat.cast_sub hm]; push_cast; ring,
    Real.rpow_natCast, kernel_half] at h
  rw [kernel_half]
  nlinarith

lemma integral_bubble : (∫ t in (0 : ℝ)..1, t * (1 - t)) = 1 / 6 := by
  have hid : (fun t : ℝ => t * (1 - t)) = fun t => t ^ 1 - t ^ 2 := by funext t; ring
  rw [hid, intervalIntegral.integral_sub ((continuous_pow 1).intervalIntegrable _ _)
    ((continuous_pow 2).intervalIntegrable _ _), integral_pow, integral_pow]
  norm_num

/-- Integrated curvature correction with explicit finite coefficient. -/
theorem R_half_le_V0 {m : ℕ} {a : ℝ} (hm : 2 ≤ m) (ha : 0 < a) (ha1 : a < 1) :
    R m a (a / 2) ≤ V0 m a := by
  have hi : IntervalIntegrable
      (fun t : ℝ => (a ^ 2 + (1 - a ^ 2) * t) ^ ((m : ℝ) / 2)) volume 0 1 :=
    ((continuous_rpow_const (by positivity : 0 ≤ (m : ℝ) / 2)).comp
      (by fun_prop)).intervalIntegrable _ _
  have hb : IntervalIntegrable (fun t : ℝ => t * (1 - t)) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (integrable_R m a (a / 2)) (hi.sub (hb.const_mul _))
    (fun t ht => curvature_pointwise hm ha ha1 ht)
  rw [intervalIntegral.integral_sub hi (hb.const_mul _), intervalIntegral.integral_const_mul,
    integral_chord ha ha1, integral_bubble] at h
  unfold R V0
  convert h using 1
  ring

/-- The chord integral is already strictly below one. -/
theorem U0_lt_one {m : ℕ} {a : ℝ} (hm : 2 ≤ m) (ha : 0 < a) (ha1 : a < 1) : U0 m a < 1 := by
  have hd := delta_pos ha ha1
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : Continuous (fun t : ℝ => a ^ 2 + (1 - a ^ 2) * t) := by fun_prop
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (((continuous_rpow_const (by positivity : 0 ≤ (m : ℝ) / 2)).comp hc).intervalIntegrable 0 1)
    (hc.intervalIntegrable 0 1 (μ := volume)) (fun t ht => Real.rpow_le_self_of_le_one
      (add_nonneg (sq_nonneg _) (mul_nonneg hd.le ht.1))
      (by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr ht.2)] : a ^ 2 + (1 - a ^ 2) * t ≤ 1)
      (by linarith : 1 ≤ (m : ℝ) / 2))
  simp only [Function.comp_apply] at h
  rw [integral_chord ha ha1] at h
  have he : (∫ t in (0 : ℝ)..1, a ^ 2 + (1 - a ^ 2) * t) = (1 + a ^ 2) / 2 := by
    have hi : IntervalIntegrable (fun t : ℝ => (1 - a ^ 2) * t) volume 0 1 :=
      (by fun_prop : Continuous (fun t : ℝ => (1 - a ^ 2) * t)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add (intervalIntegrable_const (c := a ^ 2)) hi,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
    norm_num
    ring
  rw [he] at h
  nlinarith

lemma V0_lt_one {m : ℕ} {a : ℝ} (hm : 2 ≤ m) (ha : 0 < a) (ha1 : a < 1) : V0 m a < 1 := by
  have h := U0_lt_one hm ha ha1
  have hsub : 0 ≤ (m : ℝ) / 12 * a ^ (m - 2) * (1 - a ^ 2) ^ 2 := by positivity
  unfold V0
  linarith

/-- Positive lower endpoint, hence the corrected upper endpoint is positive too. -/
lemma R_half_pos {m : ℕ} {a : ℝ} (ha : 0 < a) (ha1 : a < 1) : 0 < R m a (a / 2) := by
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (intervalIntegrable_const (c := (a ^ 2) ^ ((m : ℝ) / 2)))
    (integrable_R m a (a / 2)) (fun t ht => Real.rpow_le_rpow (sq_nonneg a)
      (kernel_half_ge ha ha1 ht.1) (by positivity : 0 ≤ (m : ℝ) / 2))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at h
  exact (Real.rpow_pos_of_pos (sq_pos_of_pos ha) _).trans_le h

lemma V0_pos {m : ℕ} {a : ℝ} (hm : 2 ≤ m) (ha : 0 < a) (ha1 : a < 1) : 0 < V0 m a :=
  (R_half_pos ha ha1).trans_le (R_half_le_V0 hm ha ha1)

/-- Monotonicity of the actual raw integral on its full feasible interval. -/
theorem R_mono {m : ℕ} {a x y : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hxy : x ≤ y) : R m a x ≤ R m a y := by
  have hd := delta_pos ha ha1
  refine intervalIntegral.integral_mono_on (by norm_num) (integrable_R m a x)
    (integrable_R m a y) ?_
  intro t ht
  apply Real.rpow_le_rpow (Ppolar_nonneg (PaperPolar.x_sq_le_one hx0 hx1) a t) _ (by positivity)
  have h := mul_nonneg (mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * a) ht.1) hd.le)
    (sub_nonneg.mpr hxy)
  unfold Ppolar
  nlinarith

/-- `U1 < 1` excludes every raw-polar feasible mean. -/
theorem one_le_U1 {m : ℕ} {a x : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hraw : PaperPolar.RawPolar m a x) : 1 ≤ U1 m a := by
  have h := ((PaperPolar.rawPolar_iff m a x).mp hraw).trans (R_mono ha ha1 hx0 hx1 hx1)
  rwa [R_one ha ha1] at h

/-- Convexity is proved pointwise from the affine kernel and integrated. -/
theorem R_secant {m : ℕ} {a θ : ℝ} (hm : 2 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    R m a ((1 - θ) * (a / 2) + θ * 1) ≤ (1 - θ) * V0 m a + θ * U1 m a := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 1 ≤ (m : ℝ) / 2 := by linarith
  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Ppolar a ((1 - θ) * (a / 2) + θ * 1) t ^ ((m : ℝ) / 2) ≤
        (1 - θ) * Ppolar a (a / 2) t ^ ((m : ℝ) / 2) + θ * Ppolar a 1 t ^ ((m : ℝ) / 2) := by
    intro t ht
    have h0 : 0 ≤ Ppolar a (a / 2) t := (sq_nonneg a).trans (kernel_half_ge ha ha1 ht.1)
    have h1 : 0 ≤ Ppolar a 1 t := Ppolar_nonneg (by norm_num) a t
    have h := (convexOn_rpow hp).2 h0 h1 (sub_nonneg.mpr hθ1) hθ0 (by ring : 1 - θ + θ = 1)
    simp only [smul_eq_mul] at h
    have hid : Ppolar a ((1 - θ) * (a / 2) + θ * 1) t =
        (1 - θ) * Ppolar a (a / 2) t + θ * Ppolar a 1 t := by unfold Ppolar; ring
    rwa [hid]
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (integrable_R m a _) (((integrable_R m a (a / 2)).const_mul (1 - θ)).add
      ((integrable_R m a 1).const_mul θ)) hpoint
  rw [intervalIntegral.integral_add ((integrable_R m a (a / 2)).const_mul (1 - θ))
    ((integrable_R m a 1).const_mul θ), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h
  change R m a _ ≤ (1 - θ) * R m a (a / 2) + θ * R m a 1 at h
  rw [R_one ha ha1] at h
  exact h.trans (add_le_add
    (mul_le_mul_of_nonneg_left (R_half_le_V0 hm ha ha1) (sub_nonneg.mpr hθ1)) le_rfl)

/-- All denominators in the secant are strictly positive. -/
lemma secant_den_pos {m : ℕ} {a : ℝ} (hm : 2 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hu : 1 ≤ U1 m a) : 0 < U1 m a - V0 m a := by
  have hv := V0_lt_one hm ha ha1
  linarith

lemma S_bounds {m : ℕ} {a : ℝ} (hm : 2 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hu : 1 ≤ U1 m a) : a / 2 < S m a ∧ S m a ≤ 1 := by
  have hv := V0_lt_one hm ha ha1
  have hd := secant_den_pos hm ha ha1 hu
  have hleft : 0 < (1 - a / 2) * (1 - V0 m a) / (U1 m a - V0 m a) := by
    apply div_pos _ hd
    exact mul_pos (by linarith) (by linarith)
  have hright : (1 - a / 2) * (1 - V0 m a) / (U1 m a - V0 m a) ≤ 1 - a / 2 := by
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg (show 0 ≤ 1 - a / 2 by linarith) (sub_nonneg.mpr hu)]
  unfold S
  constructor <;> linarith

lemma V0_le_U0 (m : ℕ) {a : ℝ} (ha : 0 ≤ a) : V0 m a ≤ U0 m a := by
  have h : 0 ≤ (m : ℝ) / 12 * a ^ (m - 2) * (1 - a ^ 2) ^ 2 := by positivity
  unfold V0
  linarith

/-- Retaining curvature can only improve the plain endpoint secant. -/
theorem plain_secant_le_S {m : ℕ} {a : ℝ} (hm : 2 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hu : 1 ≤ U1 m a) :
    a / 2 + (1 - a / 2) * (1 - U0 m a) / (U1 m a - U0 m a) ≤ S m a := by
  have hvu := V0_le_U0 m ha.le
  have hu0 := U0_lt_one hm ha ha1
  have hd0 : 0 < U1 m a - U0 m a := by linarith
  have hdv := secant_den_pos hm ha ha1 hu
  have hf : (1 - U0 m a) / (U1 m a - U0 m a) ≤
      (1 - V0 m a) / (U1 m a - V0 m a) := by
    apply (div_le_div_iff₀ hd0 hdv).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hvu)]
  have h := mul_le_mul_of_nonneg_left hf (show 0 ≤ 1 - a / 2 by linarith)
  unfold S
  simp only [mul_div_assoc]
  exact add_le_add le_rfl h

/-- Positivity of both Taylor-gate denominators follows from the finite secant. -/
lemma gate_denominators_pos {m : ℕ} {a : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hu : 1 ≤ U1 m a) :
    0 < a * ((m : ℝ) - 2) ∧
      0 < PaperTaylor.chord a (S m a) ^ 4 * ((m : ℝ) + 1) * ((m : ℝ) + 3) := by
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hs := (S_bounds (by omega : 2 ≤ m) ha ha1 hu).1
  have hc : 0 < PaperTaylor.chord a (S m a) := by
    unfold PaperTaylor.chord
    exact mul_pos ha (by linarith)
  constructor
  · exact mul_pos ha (by linarith)
  · positivity

/-- The curvature-corrected analytic lower bound follows from raw polar alone. -/
theorem raw_implies_secant {m : ℕ} {a x : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hraw : PaperPolar.RawPolar m a x) : S m a ≤ x := by
  have hx := (PaperPolar.geometry hm ha ha1 hx0 hx1 hraw).1
  have hu := one_le_U1 ha ha1 hx0 hx1 hraw
  have hd := secant_den_pos (by omega : 2 ≤ m) ha ha1 hu
  have he : 0 < 1 - a / 2 := by linarith
  let θ := (x - a / 2) / (1 - a / 2)
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) he.le
  have hθ1 : θ ≤ 1 := (div_le_one he).2 (by linarith)
  have hid : (1 - θ) * (a / 2) + θ * 1 = x := by
    dsimp [θ]
    field_simp [show 2 - a ≠ 0 by linarith]
    ring
  have h := R_secant (by omega : 2 ≤ m) ha ha1 hθ0 hθ1
  rw [hid] at h
  have hr : 1 ≤ R m a x := (PaperPolar.rawPolar_iff m a x).mp hraw
  have hnum : 1 - V0 m a ≤ θ * (U1 m a - V0 m a) := by nlinarith
  have hratio : (1 - V0 m a) / (U1 m a - V0 m a) ≤ θ := (div_le_iff₀ hd).2 hnum
  have hmul := mul_le_mul_of_nonneg_left hratio he.le
  have hid2 : (1 - a / 2) * θ = x - a / 2 := by
    dsimp [θ]
    exact mul_div_cancel₀ _ he.ne'
  rw [hid2] at hmul
  unfold S
  rw [mul_div_assoc]
  linarith

/-- The alternative finite endpoint form in the report. -/
lemma S_eq_one_sub {m : ℕ} {a : ℝ} (hd : U1 m a - V0 m a ≠ 0) :
    S m a = 1 - (1 - a / 2) * (U1 m a - 1) / (U1 m a - V0 m a) := by
  unfold S
  field_simp
  ring

/-- The actual origin budget is antitone in the mean; no budget surrogate is assumed. -/
theorem budget_antitone {m a x y : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hxy : x ≤ y) (hy : y ≤ 1) : PaperTaylor.budget m a y ≤ PaperTaylor.budget m a x := by
  have hx : x ≤ 1 := hxy.trans hy
  have hβ : ∀ t ∈ Set.Icc (0 : ℝ) 1, PaperTaylor.beta a y t ≤ PaperTaylor.beta a x t := by
    intro t ht
    have h := mul_nonneg (mul_nonneg (show 0 ≤ 2 * a by positivity) ht.1) (sub_nonneg.mpr hxy)
    unfold PaperTaylor.beta
    nlinarith
  have he := Real.rpow_le_rpow (PaperTaylor.beta_pos ha ha1 hy (t := 1) (by norm_num)).le
    (hβ 1 (by norm_num)) (by linarith : 0 ≤ m / 2)
  have hc : ∀ z : ℝ, Continuous (fun t : ℝ => t * PaperTaylor.beta a z t ^ ((m - 1) / 2)) := by
    intro z
    exact continuous_id.mul ((continuous_rpow_const (by linarith : 0 ≤ (m - 1) / 2)).comp
      (by unfold PaperTaylor.beta; fun_prop))
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    ((hc y).intervalIntegrable 0 1 (μ := volume)) ((hc x).intervalIntegrable 0 1) (fun t ht =>
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (PaperTaylor.beta_pos ha ha1 hy ht).le
        (hβ t ht) (by linarith : 0 ≤ (m - 1) / 2)) ht.1)
  have hmul := mul_le_mul_of_nonneg_left hi (show 0 ≤ m * a ^ 2 by positivity)
  unfold PaperTaylor.budget
  linarith

/-- Odd degrees are rounded down in the exponent, never evaluated by a rational square root. -/
lemma endpoint_pow_le {m : ℕ} {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    b ^ ((m : ℝ) / 2) ≤ b ^ (m / 2) := by
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_ge hb hb1
  have hn : m / 2 * 2 ≤ m := Nat.div_mul_le_self m 2
  have hn' : ((m / 2 : ℕ) : ℝ) * 2 ≤ m := by exact_mod_cast hn
  linarith

/-- The rational gate majorizes the actual origin budget at the secant. -/
theorem budget_S_le_Wsec {m : ℕ} {a : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hu : 1 ≤ U1 m a) : PaperTaylor.budget m a (S m a) ≤ Wsec m a := by
  have hs := S_bounds (by omega : 2 ≤ m) ha ha1 hu
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : 0 < PaperTaylor.chord a (S m a) := by
    unfold PaperTaylor.chord
    exact mul_pos ha (by linarith [hs.1])
  have hb := PaperTaylor.beta_pos ha ha1 hs.2 (t := 1) (by norm_num)
  have hb1 : PaperTaylor.beta a (S m a) 1 ≤ 1 := by
    rw [PaperTaylor.chord_eq_one_sub_beta] at hc
    linarith
  have ht := PaperTaylor.budget_le hm' ha ha1 hs.2 hc
  have hp := endpoint_pow_le (m := m) hb hb1
  unfold Wsec
  linarith

/-- `Fsec > 0` is a sufficient condition for D for every raw-polar feasible mean.
There is no hypothesis assuming an integral secant, and no assertion that this
finite rational function is positive everywhere. -/
theorem gate_implies_D {m : ℕ} {a x : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hraw : PaperPolar.RawPolar m a x)
    (hgate : 0 < Fsec m a) : PaperTaylor.budget m a x < B m a := by
  have hu := one_le_U1 ha ha1 hx0 hx1 hraw
  have hs := raw_implies_secant hm ha ha1 hx0 hx1 hraw
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have ht := (budget_antitone hm' ha ha1 hs hx1).trans (budget_S_le_Wsec hm ha ha1 hu)
  unfold Fsec at hgate
  linarith

end Sendov.PaperSecant
