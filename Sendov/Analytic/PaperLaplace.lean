import Sendov.Analytic.PaperTaylor
import Sendov.Analytic.PaperPolar
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Sharp Laplace bound for the actual Taylor budget

Source: round4/REPORT.md §5.2 and round5/REPORT.md §5.3.
The split point is `x / (2*a)` and all integrals below are actual interval integrals.
-/

namespace Sendov.PaperLaplace

open MeasureTheory PaperTaylor

/-- The first-order exponential remainder, valid without a sign restriction. -/
lemma exp_le_one_add_mul_exp (v : ℝ) :
    Real.exp v ≤ 1 + v * Real.exp v := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-v)) (Real.exp_pos v).le
  rw [← Real.exp_add] at h
  simp only [neg_add_cancel, Real.exp_zero] at h
  nlinarith

/-- A reusable exponential Taylor comparison with a controlled quadratic error. -/
lemma rpow_le_exp_taylor {b p u v : ℝ} (hb : 0 < b) (hp : 0 ≤ p)
    (hv : 0 ≤ v) (hlog : p * (b - 1) ≤ -u + v) (hvu : v ≤ u / 4) :
    b ^ p ≤ Real.exp (-u) + v * Real.exp (-(3 / 4 : ℝ) * u) := by
  have hlog' := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hb) hp
  have hpow : b ^ p ≤ Real.exp (-u + v) := by
    rw [Real.rpow_def_of_pos hb]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hexp := mul_le_mul_of_nonneg_left (exp_le_one_add_mul_exp v)
    (Real.exp_pos (-u)).le
  have hrem := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (show -u + v ≤ -(3 / 4 : ℝ) * u by linarith)) hv
  rw [Real.exp_add] at hpow hrem
  nlinarith

lemma split_mem {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (hxa : x < 2 * a) :
    x / (2 * a) ∈ Set.Ioo (0 : ℝ) 1 := by
  exact ⟨div_pos hx (by positivity), (div_lt_one (by positivity)).mpr hxa⟩

lemma beta_split {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    beta a x (x / (2 * a)) = 1 - 3 * x ^ 2 / 4 := by
  unfold beta
  field_simp
  ring

/-- The paper's pointwise two-exponential majorant on the left interval. -/
lemma beta_rpow_le_exp {m a x t : ℝ} (hm : 1 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx : x ≤ 1) (hxa : x < 2 * a) (ht : t ∈ Set.Icc (0 : ℝ) (x / (2 * a))) :
    beta a x t ^ ((m - 1) / 2) ≤
      Real.exp (-((m - 1) * a * x) * t) +
      ((m - 1) / 2 * a ^ 2 * t ^ 2) *
        Real.exp (-(3 / 4 : ℝ) * ((m - 1) * a * x) * t) := by
  have ht1 : t ≤ 1 := ht.2.trans ((div_lt_one (by positivity)).mpr hxa).le
  have ht0 := ht.1
  have hm0 : 0 ≤ m - 1 := sub_nonneg.mpr hm
  have hat : 2 * a * t ≤ x := by
    have h := (le_div_iff₀ (show 0 < 2 * a by positivity)).mp ht.2
    nlinarith
  have hvu : (m - 1) / 2 * a ^ 2 * t ^ 2 ≤ ((m - 1) * a * x * t) / 4 := by
    have h := mul_nonneg (show 0 ≤ (m - 1) * a * t by positivity) (sub_nonneg.mpr hat)
    nlinarith only [h]
  have h := rpow_le_exp_taylor (beta_pos ha ha1 hx ⟨ht.1, ht1⟩)
    (by positivity : 0 ≤ (m - 1) / 2)
    (by positivity : 0 ≤ (m - 1) / 2 * a ^ 2 * t ^ 2)
    (show (m - 1) / 2 * (beta a x t - 1) ≤
      -((m - 1) * a * x * t) + (m - 1) / 2 * a ^ 2 * t ^ 2 by unfold beta; ring_nf; exact le_rfl)
    hvu
  simpa only [neg_mul, mul_assoc] using h

/-- Exact first exponential moment, including the finite endpoint remainder. -/
lemma integral_mul_exp {s : ℝ} (hs : s ≠ 0) (z : ℝ) :
    (∫ t in (0 : ℝ)..z, t * Real.exp (-s * t)) =
      1 / s ^ 2 - (z / s + 1 / s ^ 2) * Real.exp (-s * z) := by
  have hd : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => -(t / s + 1 / s ^ 2) * Real.exp (-s * t))
      (t * Real.exp (-s * t)) t := by
    intro t
    convert! ((((hasDerivAt_id t).div_const s).add_const (1 / s ^ 2)).neg.mul
      (((hasDerivAt_id t).const_mul (-s)).exp)) using 1
    dsimp
    field_simp
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((by fun_prop : Continuous (fun t : ℝ => t * Real.exp (-s * t))).intervalIntegrable 0 z)
  convert! h using 1
  simp
  ring

/-- Exact cubic exponential moment. -/
lemma integral_cube_mul_exp {s : ℝ} (hs : s ≠ 0) (z : ℝ) :
    (∫ t in (0 : ℝ)..z, t ^ 3 * Real.exp (-s * t)) =
      6 / s ^ 4 - (z ^ 3 / s + 3 * z ^ 2 / s ^ 2 + 6 * z / s ^ 3 + 6 / s ^ 4) *
        Real.exp (-s * z) := by
  have hd : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => -(t ^ 3 / s + 3 * t ^ 2 / s ^ 2 + 6 * t / s ^ 3 + 6 / s ^ 4) *
        Real.exp (-s * t)) (t ^ 3 * Real.exp (-s * t)) t := by
    intro t
    convert! ((((((hasDerivAt_id t).pow 3).div_const s).add
      ((((hasDerivAt_id t).pow 2).const_mul 3).div_const (s ^ 2))).add
      (((hasDerivAt_id t).const_mul 6).div_const (s ^ 3))).add_const (6 / s ^ 4)).neg.mul
      (((hasDerivAt_id t).const_mul (-s)).exp) using 1
    dsimp
    field_simp
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((by fun_prop : Continuous (fun t : ℝ => t ^ 3 * Real.exp (-s * t))).intervalIntegrable 0 z)
  convert! h using 1
  simp
  ring

lemma integral_mul_exp_le {s z : ℝ} (hs : 0 < s) (hz : 0 ≤ z) :
    (∫ t in (0 : ℝ)..z, t * Real.exp (-s * t)) ≤ 1 / s ^ 2 := by
  rw [integral_mul_exp hs.ne']
  have : 0 ≤ (z / s + 1 / s ^ 2) * Real.exp (-s * z) := by positivity
  linarith

lemma integral_cube_mul_exp_le {s z : ℝ} (hs : 0 < s) (hz : 0 ≤ z) :
    (∫ t in (0 : ℝ)..z, t ^ 3 * Real.exp (-s * t)) ≤ 6 / s ^ 4 := by
  rw [integral_cube_mul_exp hs.ne']
  have : 0 ≤ (z ^ 3 / s + 3 * z ^ 2 / s ^ 2 + 6 * z / s ^ 3 + 6 / s ^ 4) *
      Real.exp (-s * z) := by positivity
  linarith

/-- Continuity supplies every integrability obligation for the actual kernel. -/
lemma continuous_weighted_beta (a x p : ℝ) (hp : 0 ≤ p) :
    Continuous (fun t : ℝ => t * beta a x t ^ p) :=
  continuous_id.mul ((continuous_rpow_const hp).comp (by unfold beta; fun_prop))

/-- Convexity of the quadratic, expressed as an explicit secant certificate. -/
lemma beta_le_of_endpoints {a x z t r : ℝ} (hz : z < 1)
    (ht : t ∈ Set.Icc z 1) (hzr : beta a x z ≤ r) (h1r : beta a x 1 ≤ r) :
    beta a x t ≤ r := by
  have h0 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hzr)
  have h1 := mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr h1r)
  have h2 := mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg a)
    (sub_nonneg.mpr ht.1)) (sub_nonneg.mpr ht.2)) (sub_nonneg.mpr hz.le)
  by_contra h
  have h3 := mul_pos (sub_pos.mpr hz) (sub_pos.mpr (lt_of_not_ge h))
  unfold beta at *
  nlinarith only [h0, h1, h2, h3]

/-- Actual left integral, with the two exponential moments explicitly evaluated. -/
lemma integral_left_le {m a x : ℝ} (hm : 1 < m) (ha : 0 < a) (ha1 : a < 1)
    (hx0 : 0 < x) (hx : x ≤ 1) (hxa : x < 2 * a) :
    (∫ t in (0 : ℝ)..(x / (2 * a)), t * beta a x t ^ ((m - 1) / 2)) ≤
      1 / ((m - 1) ^ 2 * a ^ 2 * x ^ 2) +
      (256 / 27 : ℝ) / ((m - 1) ^ 3 * a ^ 2 * x ^ 4) := by
  let s := (m - 1) * a * x
  let c := (m - 1) / 2 * a ^ 2
  let z := x / (2 * a)
  have hm0 : 0 < m - 1 := sub_pos.mpr hm
  have hs : 0 < s := by dsimp [s]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hz : 0 ≤ z := (split_mem ha hx0 hxa).1.le
  have hf : IntervalIntegrable (fun t : ℝ => t * Real.exp (-s * t)) volume 0 z :=
    (by fun_prop : Continuous (fun t : ℝ => t * Real.exp (-s * t))).intervalIntegrable _ _
  have hg : IntervalIntegrable (fun t : ℝ => t ^ 3 * Real.exp (-(3 / 4 : ℝ) * s * t))
      volume 0 z :=
    (by fun_prop : Continuous
      (fun t : ℝ => t ^ 3 * Real.exp (-(3 / 4 : ℝ) * s * t))).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on hz
    ((continuous_weighted_beta a x ((m - 1) / 2) (by positivity)).intervalIntegrable 0 z)
    (hf.add (hg.const_mul c)) (show ∀ t ∈ Set.Icc (0 : ℝ) z,
      t * beta a x t ^ ((m - 1) / 2) ≤
        t * Real.exp (-s * t) + c * (t ^ 3 * Real.exp (-(3 / 4 : ℝ) * s * t)) from by
      intro t ht
      have h := mul_le_mul_of_nonneg_left (beta_rpow_le_exp hm.le ha ha1 hx hxa ht) ht.1
      convert! h using 1
      dsimp [s, c]
      ring)
  rw [intervalIntegral.integral_add hf (hg.const_mul c), intervalIntegral.integral_const_mul] at h
  have hfirst := integral_mul_exp_le hs hz
  have hthird := integral_cube_mul_exp_le (show 0 < (3 / 4 : ℝ) * s by positivity) hz
  have hthird' : (∫ t in (0 : ℝ)..z, t ^ 3 * Real.exp (-(3 / 4 : ℝ) * s * t)) ≤
      6 / ((3 / 4 : ℝ) * s) ^ 4 := by simpa only [neg_mul] using hthird
  have hbound := h.trans (add_le_add hfirst (mul_le_mul_of_nonneg_left hthird' hc))
  convert! hbound using 1
  dsimp [s, c]
  field_simp
  ring

/-- Actual right integral: convexity controls the kernel by the two endpoints. -/
lemma integral_right_le {m a x r : ℝ} (hm : 1 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx0 : 0 < x) (hx : x ≤ 1) (hxa : x < 2 * a)
    (hr0 : 1 - 3 * x ^ 2 / 4 ≤ r) (hr1 : beta a x 1 ≤ r) :
    (∫ t in (x / (2 * a))..(1 : ℝ), t * beta a x t ^ ((m - 1) / 2)) ≤
      r ^ ((m - 1) / 2) / 2 := by
  let z := x / (2 * a)
  have hz := split_mem ha hx0 hxa
  have hp : 0 ≤ (m - 1) / 2 := by linarith
  have hr : 0 < r := (beta_pos ha ha1 hx (t := 1) (by norm_num)).trans_le hr1
  have hzr : beta a x z ≤ r := by simpa only [z, beta_split ha.ne'] using hr0
  have h := intervalIntegral.integral_mono_on (μ := volume) hz.2.le
    ((continuous_weighted_beta a x ((m - 1) / 2) hp).intervalIntegrable z 1)
    ((continuous_id.mul_const (r ^ ((m - 1) / 2))).intervalIntegrable z 1)
    (show ∀ t ∈ Set.Icc z (1 : ℝ), t * beta a x t ^ ((m - 1) / 2) ≤
      t * r ^ ((m - 1) / 2) from by
      intro t ht
      have ht0 : 0 ≤ t := hz.1.le.trans ht.1
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (beta_pos ha ha1 hx ⟨ht0, ht.2⟩).le
          (beta_le_of_endpoints hz.2 ht hzr hr1) hp) ht0)
  rw [intervalIntegral.integral_mul_const] at h
  simp only [id_eq, integral_id, one_pow] at h
  have hpow := Real.rpow_nonneg hr.le ((m - 1) / 2)
  have hrest := mul_nonneg (sq_nonneg z) hpow
  nlinarith

/-- **(S)** for `PaperTaylor.budget`, including its endpoint term and actual integral.

The analytic statement holds for every real `m > 1`. Raw polar is not needed here:
it is used by the paper to supply the geometric and endpoint hypotheses.
No exponential or integral estimate is assumed. -/
theorem budget_le_of_beta_le_one {m a x r : ℝ} (hm : 1 < m) (ha : 0 < a) (ha1 : a < 1)
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hxa : x < 2 * a)
    (hr0 : 1 - 3 * x ^ 2 / 4 ≤ r) (hrb : beta a x 1 ≤ r) (hb1 : beta a x 1 ≤ 1) :
    m * x ^ 2 * PaperTaylor.budget m a x ≤
      m ^ 2 / (m - 1) ^ 2 + (256 / 27 : ℝ) * m ^ 2 / ((m - 1) ^ 3 * x ^ 2) +
      (m ^ 2 / 2 + m) * r ^ ((m - 1) / 2) := by
  let L := 1 / ((m - 1) ^ 2 * a ^ 2 * x ^ 2) +
    (256 / 27 : ℝ) / ((m - 1) ^ 3 * a ^ 2 * x ^ 4)
  let R := r ^ ((m - 1) / 2)
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m - 1 := sub_pos.mpr hm
  have hp : 0 ≤ (m - 1) / 2 := by positivity
  have hb : 0 < beta a x 1 := beta_pos ha ha1 hx1 (by norm_num)
  have hR : 0 ≤ R := Real.rpow_nonneg (hb.le.trans hrb) _
  have hleft := integral_left_le hm ha ha1 hx0 hx1 hxa
  have hright := integral_right_le hm.le ha ha1 hx0 hx1 hxa hr0 hrb
  have hi : (∫ t in (0 : ℝ)..1, t * beta a x t ^ ((m - 1) / 2)) ≤ L + R / 2 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((continuous_weighted_beta a x ((m - 1) / 2) hp).intervalIntegrable
        (0 : ℝ) (x / (2 * a)))
      ((continuous_weighted_beta a x ((m - 1) / 2) hp).intervalIntegrable
        (x / (2 * a)) (1 : ℝ))]
    exact add_le_add hleft hright
  have hend : beta a x 1 ^ (m / 2) ≤ R :=
    (Real.rpow_le_rpow_of_exponent_ge hb hb1 (by linarith)).trans
      (Real.rpow_le_rpow hb.le hrb hp)
  have hbudget : PaperTaylor.budget m a x ≤ R + m * a ^ 2 * (L + R / 2) := by
    unfold PaperTaylor.budget
    exact add_le_add hend (mul_le_mul_of_nonneg_left hi (by positivity))
  have hscaled := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ m * x ^ 2 by positivity)
  have heq : m * x ^ 2 * (R + m * a ^ 2 * (L + R / 2)) =
      m ^ 2 / (m - 1) ^ 2 + (256 / 27 : ℝ) * m ^ 2 / ((m - 1) ^ 3 * x ^ 2) +
      (m * x ^ 2 + m ^ 2 * a ^ 2 * x ^ 2 / 2) * R := by
    dsimp [L]
    field_simp
    ring
  rw [heq] at hscaled
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hax2 : a ^ 2 * x ^ 2 ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hx2 (sq_nonneg a)]
  have hcoef : m * x ^ 2 + m ^ 2 * a ^ 2 * x ^ 2 / 2 ≤ m ^ 2 / 2 + m := by
    nlinarith only [mul_le_mul_of_nonneg_left hx2 hm0.le,
      mul_le_mul_of_nonneg_left hax2 (sq_nonneg m)]
  exact hscaled.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef hR))

/-- Convenient radius form of **(S)**. The endpoint positivity also proves `0 < r`. -/
theorem budget_le {m a x r : ℝ} (hm : 1 < m) (ha : 0 < a) (ha1 : a < 1)
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hxa : x < 2 * a)
    (hr0 : 1 - 3 * x ^ 2 / 4 ≤ r) (hrb : beta a x 1 ≤ r) (hr1 : r ≤ 1) :
    m * x ^ 2 * PaperTaylor.budget m a x ≤
      m ^ 2 / (m - 1) ^ 2 + (256 / 27 : ℝ) * m ^ 2 / ((m - 1) ^ 3 * x ^ 2) +
      (m ^ 2 / 2 + m) * r ^ ((m - 1) / 2) :=
  budget_le_of_beta_le_one hm ha ha1 hx0 hx1 hxa hr0 hrb (hrb.trans hr1)

/-- Paper interface: raw polar supplies positivity of `x` and `beta(1) < 1`.
The hypothesis `1/2 < a` ensures the paper's split lies strictly before 1.
Only the two stated endpoint bounds on `r` remain; `r ≤ 1` is not required. -/
theorem sharp_laplace {m : ℕ} {a x r : ℝ} (hm : 7 ≤ m)
    (ha : 1 / 2 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : PaperPolar.RawPolar m a x)
    (hr0 : 1 - 3 * x ^ 2 / 4 ≤ r) (hrb : PaperPolar.b a x ≤ r) :
    (m : ℝ) * x ^ 2 * PaperTaylor.budget m a x ≤
      (m : ℝ) ^ 2 / (m - 1) ^ 2 +
      (256 / 27 : ℝ) * m ^ 2 / ((m - 1) ^ 3 * x ^ 2) +
      ((m : ℝ) ^ 2 / 2 + m) * r ^ (((m : ℝ) - 1) / 2) := by
  have ha0 : 0 < a := by linarith
  have hgeom := PaperPolar.geometry hm ha0 ha1 hx0 hx1 hraw
  have hb := PaperPolar.b_lt_one (by omega : 0 < m) ha0 ha1 hx0 hx1 hraw
  have heq : beta a x 1 = PaperPolar.b a x := by simp [beta, PaperPolar.b]
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  exact budget_le_of_beta_le_one (by linarith) ha0 ha1 (by linarith [hgeom.1])
    hx1 (by linarith) hr0 (by simpa only [heq] using hrb) (by simpa only [heq] using hb.le)

end Sendov.PaperLaplace
