import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Topology.Algebra.Polynomial
import Sendov.Analytic.Maclaurin

/-!
# Centered coefficient estimates

Exact Cauchy circle coefficient extraction and AM–GM, independently of centered
integral expansions. The multiset formulation permits repetitions and imposes no
pointwise root bound. The optimized theorem covers zero variance separately, and
the radius estimate is valid for every real radius (including zero and negatives).

The cached mathlib polynomial Parseval module is unavailable here; this proof uses
only the already available exact circle integrals of integer powers, not samples.
-/

open scoped BigOperators
open Polynomial Complex
open scoped Real

namespace Sendov.PaperCoefficient

private lemma circleIntegrable_eval_mul_zpow (p : ℂ[X]) (n : ℤ) :
    CircleIntegrable (fun z ↦ p.eval z * z ^ n) 0 1 := by
  have h : CircleIntegrable (fun z : ℂ ↦ z ^ n) 0 1 := by
    simpa using (circleIntegrable_sub_zpow_iff (c := 0) (w := 0) (R := 1) (n := n)).2
      (Or.inr (Or.inr (by simp)))
  exact h.fun_continuousOn_mul p.continuous.continuousOn

/-- Exact Cauchy coefficient extraction on the unit circle. -/
theorem circleIntegral_coeff (p : ℂ[X]) (k : ℕ) :
    (∮ z in C(0, 1), p.eval z * z ^ (-(k : ℤ) - 1)) =
      p.coeff k * (2 * π * I) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add, add_mul, coeff_add]
    rw [circleIntegral.integral_add (circleIntegrable_eval_mul_zpow p _)
      (circleIntegrable_eval_mul_zpow q _), hp, hq]
  | monomial n a =>
    have hi : (∮ z in C(0, 1), (monomial n a).eval z * z ^ (-(k : ℤ) - 1)) =
        a * ∮ z in C(0, 1), z ^ ((n : ℤ) - k - 1) := by
      rw [← circleIntegral.integral_const_mul]
      apply circleIntegral.integral_congr (by norm_num)
      intro z hz
      have hz0 : z ≠ 0 := by intro h; simp [h] at hz
      simp only [eval_monomial]
      rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hz0]
      congr 2; omega
    rw [hi]
    by_cases hnk : n = k
    · subst n
      simp only [sub_self, zero_sub, zpow_neg_one, coeff_monomial, ↓reduceIte]
      simpa using congrArg (a * ·)
        (circleIntegral.integral_sub_center_inv (0 : ℂ) (R := 1) (by norm_num))
    · have hn : (n : ℤ) - k - 1 ≠ -1 := by omega
      have hzero := circleIntegral.integral_sub_zpow_of_ne hn (0 : ℂ) 0 1
      simp only [sub_zero] at hzero
      simp [hzero, coeff_monomial, hnk]

/-- Cauchy's coefficient bound from a uniform bound on the unit circle. -/
theorem norm_coeff_le_of_circle (p : ℂ[X]) (k : ℕ) (B : ℝ)
    (hB : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ B) :
    ‖p.coeff k‖ ≤ B := by
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (f := fun z ↦ p.eval z * z ^ (-(k : ℤ) - 1)) (c := 0) (R := 1)
    (C := B) (by norm_num) (by
      intro z hz
      have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
      simpa [norm_mul, norm_zpow, hz1] using hB z hz1)
  rw [circleIntegral_coeff] at h
  have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have heq : (2 * π * I : ℂ)⁻¹ • (p.coeff k * (2 * π * I)) = p.coeff k := by
    rw [smul_eq_mul, mul_comm (p.coeff k), inv_mul_cancel_left₀ hpi]
  rw [heq, one_mul] at h
  exact h

/-- Squared Cauchy bound, with no positivity assumption hidden in the interface. -/
theorem norm_coeff_sq_le_of_circle (p : ℂ[X]) (k : ℕ) (B : ℝ)
    (hB : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ^ 2 ≤ B) :
    ‖p.coeff k‖ ^ 2 ≤ B := by
  have hB0 : 0 ≤ B := (sq_nonneg _).trans (hB 1 (by simp))
  have h := norm_coeff_le_of_circle p k (Real.sqrt B) (fun z hz ↦
    (Real.le_sqrt (norm_nonneg _) hB0).2 (hB z hz))
  exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 h |>.trans_eq
    (Real.sq_sqrt hB0)

/-- The variance parameter for a centered multiset. -/
noncomputable def variance (r : Multiset ℂ) : ℝ :=
  (r.map (fun z ↦ ‖z‖ ^ 2)).sum / r.card

/-- AM–GM gives the sharp top-degree product bound, including the empty family. -/
theorem norm_prod_sq_le_variance_pow (r : Multiset ℂ) :
    ‖r.prod‖ ^ 2 ≤ variance r ^ r.card := by
  have h := Sendov.Multiset.prod_le_mean_pow (r.map (fun z ↦ ‖z‖ ^ 2)) (by
    intro x hx
    obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hx
    exact sq_nonneg _)
  have hn : (r.map norm).prod = ‖r.prod‖ := by
    clear h
    induction r using Multiset.induction_on with
    | empty => simp
    | cons a r ih => simp [ih]
  simpa [variance, Multiset.prod_map_pow, hn] using h

/-- The cross term in the mean square is exactly the sum of the roots. -/
theorem sum_norm_add_sq (r : Multiset ℂ) (z : ℂ) :
    (r.map (fun w ↦ ‖z + w‖ ^ 2)).sum =
      r.card * ‖z‖ ^ 2 + (r.map (fun w ↦ ‖w‖ ^ 2)).sum +
        2 * (z * (starRingEnd ℂ) r.sum).re := by
  simp only [← Complex.normSq_eq_norm_sq]
  induction r using Multiset.induction_on with
  | empty => simp
  | cons a r ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
      Nat.cast_add, Nat.cast_one, ih]
    rw [Complex.normSq_add, map_add, mul_add, add_re]
    ring

/-- The centered AM–GM circle bound; no individual bound on the roots is used. -/
theorem norm_prod_add_sq_le (r : Multiset ℂ) (hr : r.sum = 0)
    (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(r.map (fun w ↦ z + w)).prod‖ ^ 2 ≤ (1 + variance r) ^ r.card := by
  by_cases hcard : r.card = 0
  · have hr0 := Multiset.card_eq_zero.mp hcard
    subst r
    simp
  have hc : (r.card : ℝ) ≠ 0 := by exact_mod_cast hcard
  have h := norm_prod_sq_le_variance_pow (r.map (fun w ↦ z + w))
  have hv : variance (r.map (fun w ↦ z + w)) = 1 + variance r := by
    unfold variance
    simp only [Multiset.map_map, Multiset.card_map, Function.comp_def]
    rw [sum_norm_add_sq, hr, hz]
    simp only [one_pow, mul_one, map_zero, mul_zero, zero_re, add_zero]
    rw [add_div, div_self hc]
  simpa only [hv, Multiset.card_map] using h

/-- All elementary symmetric coefficients obey the centered unit-circle bound. -/
theorem norm_esymm_sq_le (r : Multiset ℂ) (hr : r.sum = 0)
    (k : ℕ) (hk : k ≤ r.card) :
    ‖r.esymm k‖ ^ 2 ≤ (1 + variance r) ^ r.card := by
  let p : ℂ[X] := (r.map (fun w ↦ X + C w)).prod
  have hp : p.coeff (r.card - k) = r.esymm k := by
    dsimp [p]
    rw [Multiset.prod_X_add_C_coeff r (Nat.sub_le _ _), Nat.sub_sub_self hk]
  rw [← hp]
  apply norm_coeff_sq_le_of_circle
  intro z hz
  have heval : p.eval z = (r.map (fun w ↦ z + w)).prod := by
    dsimp [p]
    change (evalRingHom z) (r.map (fun w ↦ X + C w)).prod = _
    rw [map_multiset_prod]
    simp [Multiset.map_map]
  rw [heval]
  exact norm_prod_add_sq_le r hr z hz

/-- Scaling of variance, valid also when the scalar or the family is zero. -/
theorem variance_map_mul (r : Multiset ℂ) (a : ℂ) :
    variance (r.map (a * ·)) = ‖a‖ ^ 2 * variance r := by
  simp only [variance, Multiset.map_map, Multiset.card_map, Function.comp_def, norm_mul,
    mul_pow, Multiset.sum_map_mul_left]
  ring

/-- The radius-parametrized coefficient estimate from REPORT §3.2. -/
theorem norm_esymm_sq_mul_pow_le (r : Multiset ℂ) (hr : r.sum = 0)
    (k : ℕ) (hk : k ≤ r.card) (R : ℝ) :
    ‖r.esymm k‖ ^ 2 * R ^ (2 * k) ≤ (1 + R ^ 2 * variance r) ^ r.card := by
  have hs : (r.map ((R : ℂ) * ·)).sum = 0 := by
    rw [Multiset.sum_map_mul_left]
    simp [hr]
  have h := norm_esymm_sq_le (r.map ((R : ℂ) * ·)) hs k (by simpa using hk)
  have he := Multiset.pow_smul_esymm (R : ℂ) k r
  simp only [smul_eq_mul] at he
  rw [← he, variance_map_mul] at h
  simp only [norm_mul, norm_pow, Multiset.card_map,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] at h
  have habs : (|R| ^ k) ^ 2 = R ^ (2 * k) := by
    calc
      _ = (|R| ^ 2) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
      _ = _ := by rw [sq_abs, ← pow_mul]
  simpa only [habs, mul_comm] using h

/-- Variance is always nonnegative. -/
theorem variance_nonneg (r : Multiset ℂ) : 0 ≤ variance r := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Multiset.sum_nonneg (by
    intro x hx
    obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hx
    exact sq_nonneg _)

/-- Vanishing variance makes every positive-degree elementary coefficient vanish. -/
theorem esymm_eq_zero_of_variance_eq_zero (r : Multiset ℂ)
    (hv : variance r = 0) (k : ℕ) (hk : 0 < k) : r.esymm k = 0 := by
  have hall : ∀ z ∈ r, z = 0 := by
    intro z hz
    have hc : r.card ≠ 0 := by
      intro hc
      simp [Multiset.card_eq_zero.mp hc] at hz
    have hs : (r.map (fun z ↦ ‖z‖ ^ 2)).sum = 0 := by
      exact (div_eq_zero_iff.mp hv).resolve_right (by exact_mod_cast hc)
    have hle := Multiset.single_le_sum (s := r.map (fun z ↦ ‖z‖ ^ 2))
      (by intro x hx; obtain ⟨w, _, rfl⟩ := Multiset.mem_map.mp hx; exact sq_nonneg _)
      (‖z‖ ^ 2) (Multiset.mem_map.mpr ⟨z, hz, rfl⟩)
    rw [hs] at hle
    have hn : ‖z‖ = 0 := by nlinarith [sq_nonneg ‖z‖]
    exact norm_eq_zero.mp hn
  have hm : r.map ((0 : ℂ) • ·) = r := by
    calc
      _ = r.map id := Multiset.map_congr rfl (fun z hz ↦ by simp [hall z hz])
      _ = r := Multiset.map_id r
  have he := Multiset.pow_smul_esymm (0 : ℂ) k r
  rw [hm] at he
  simpa [zero_pow hk.ne'] using he.symm

/-- Scalar optimization of the radius-parametrized inequality. -/
theorem optimized_scalar_bound {E v : ℝ} {m k : ℕ}
    (hv : 0 < v) (hk : 0 < k) (hkm : k < m)
    (h : ∀ t : ℝ, 0 ≤ t → E * t ^ k ≤ (1 + t * v) ^ m) :
    E ≤ (m : ℝ) ^ m / ((k : ℝ) ^ k * ((m - k : ℕ) : ℝ) ^ (m - k)) * v ^ k := by
  let d : ℝ := (m - k : ℕ)
  have hd : 0 < d := by dsimp [d]; exact_mod_cast Nat.sub_pos_of_lt hkm
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hmR : (m : ℝ) = (k : ℝ) + d := by
    dsimp [d]
    exact_mod_cast (Nat.add_sub_of_le hkm.le).symm
  have ht : 0 < (k : ℝ) / (d * v) := div_pos hkR (mul_pos hd hv)
  have hh := h ((k : ℝ) / (d * v)) ht.le
  have hbase : 1 + (k : ℝ) / (d * v) * v = (m : ℝ) / d := by
    rw [hmR]
    field_simp
    ring
  rw [hbase] at hh
  have he := (le_div_iff₀ (pow_pos ht k)).mpr hh
  apply he.trans_eq
  change ((m : ℝ) / d) ^ m / ((k : ℝ) / (d * v)) ^ k =
    (m : ℝ) ^ m / ((k : ℝ) ^ k * d ^ (m - k)) * v ^ k
  have hdp : d ^ m = d ^ k * d ^ (m - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkm.le]
  rw [div_pow, hdp, div_pow, mul_pow]
  field_simp

/-- The optimized finite-degree bound of REPORT §3.2, including zero variance. -/
theorem norm_esymm_sq_le_optimized (r : Multiset ℂ) (hr : r.sum = 0)
    (k : ℕ) (hk : 0 < k) (hkm : k < r.card) :
    ‖r.esymm k‖ ^ 2 ≤
      (r.card : ℝ) ^ r.card /
        ((k : ℝ) ^ k * ((r.card - k : ℕ) : ℝ) ^ (r.card - k)) * variance r ^ k := by
  rcases (variance_nonneg r).eq_or_lt with hv | hv
  · rw [esymm_eq_zero_of_variance_eq_zero r hv.symm k hk, ← hv]
    simp [zero_pow hk.ne']
  · apply optimized_scalar_bound hv hk hkm
    intro t ht
    have h := norm_esymm_sq_mul_pow_le r hr k hkm.le (Real.sqrt t)
    simpa only [pow_mul, Real.sq_sqrt ht] using h

/-- The top-degree coefficient has the sharper product bound, without centeredness. -/
theorem norm_esymm_card_sq_le (r : Multiset ℂ) :
    ‖r.esymm r.card‖ ^ 2 ≤ variance r ^ r.card := by
  simpa [Multiset.esymm] using norm_prod_sq_le_variance_pow r

end Sendov.PaperCoefficient
