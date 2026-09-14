import Sendov.Analytic.PaperCenteredBound
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact finite certificate bridge

Rational witnesses may be generated externally, but this module consumes only
kernel-checked inequalities bound to the actual centered multiset. It does not
assume an error estimate or replace either error definition by a scalar proxy.
-/
noncomputable section
open scoped BigOperators
namespace Sendov.PaperCenteredCertificate
open PaperCentered PaperCenteredBound

/-- Real binomial endpoint, useful for exact rational replay. -/
def realB (m k : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), (m + 1).choose j * z ^ j * (1 - z) ^ (m + 1 - j)

lemma B_ofReal (m k : ℕ) (z : ℝ) : B m k (z : ℂ) = (realB m k z : ℂ) := by
  simp [B, realB]

lemma realB_nonneg (m k : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ realB m k z := by
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _))
    (pow_nonneg (sub_nonneg.mpr hz1) _)

lemma realB_le_one (m k : ℕ) (z : ℝ) (hk : k ≤ m)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) : realB m k z ≤ 1 := by
  have hsum : (∑ j ∈ Finset.range (m + 1 + 1),
      ((m + 1).choose j : ℝ) * z ^ j * (1 - z) ^ (m + 1 - j)) = 1 := by
    have h := add_pow z (1 - z) (m + 1)
    rw [show z + (1 - z) = 1 by ring, one_pow] at h
    calc
      _ = ∑ j ∈ Finset.range (m + 1 + 1),
          z ^ j * (1 - z) ^ (m + 1 - j) * ((m + 1).choose j : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 1 := h.symm
  unfold realB
  apply le_trans (b := ∑ j ∈ Finset.range (m + 1 + 1),
    ((m + 1).choose j : ℝ) * z ^ j * (1 - z) ^ (m + 1 - j)) _ hsum.le
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (by omega)
  · intro j hj hj'
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _))
      (pow_nonneg (sub_nonneg.mpr hz1) _)

/-- All endpoints, including the top endpoint, have norm at most one when the
scale really is in the real unit interval. No such claim is made for complex scales. -/
theorem norm_H_ofReal_le_one (m k : ℕ) (z : ℝ) (hk : k ≤ m)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) : ‖H m k (z : ℂ)‖ ≤ 1 := by
  rw [H, B_ofReal, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (sub_nonneg.mpr (realB_le_one m k z hk hz hz1))]
  linarith [realB_nonneg m k z hz hz1]

/-- A square witness checks a normalized square-root coefficient without trusting
an external square-root implementation. The top-degree branch is explicit. -/
theorem normalized_C_le (m k : ℕ) (v u b : ℝ)
    (hk : 0 < k) (hkm : k ≤ m) (hu : 0 < u) (hb : 0 ≤ b)
    (hsq : (if k = m then v ^ m else
      (m : ℝ) ^ m / ((k : ℝ) ^ k * ((m - k : ℕ) : ℝ) ^ (m - k)) * v ^ k) ≤
        (b * ((m.choose k : ℝ) * u ^ k)) ^ 2) :
    C m k v / ((m.choose k : ℝ) * u ^ k) ≤ b := by
  have hd : 0 < (m.choose k : ℝ) * u ^ k :=
    mul_pos (by exact_mod_cast Nat.choose_pos hkm) (pow_pos hu _)
  apply (div_le_iff₀ hd).2
  have he : C m k v = Real.sqrt (if k = m then v ^ m else
      (m : ℝ) ^ m / ((k : ℝ) ^ k * ((m - k : ℕ) : ℝ) ^ (m - k)) * v ^ k) := by
    by_cases h : k = m
    · simp [h]
    · simp [C, h, hk, lt_of_le_of_ne hkm h]
  rw [he]
  exact (Real.sqrt_le_left (mul_nonneg hb hd.le)).2 hsq

/-- Finite per-degree normalized bounds assemble into the actual majorant. -/
theorem majorant_le (r : Multiset ℂ) (μ z : ℂ) (p : ℝ) (b : ℕ → ℝ)
    (hp : ‖1 - z‖ ^ (r.card + 1) + Gamma r μ * ‖B r.card 2 z‖ ≤ p)
    (hH : ∀ k ∈ Finset.Ico 3 (r.card + 1), ‖H r.card k z‖ ≤ 1)
    (hb : ∀ k ∈ Finset.Ico 3 (r.card + 1),
      C r.card k (variance r) / ((r.card.choose k : ℝ) * ‖μ‖ ^ k) ≤ b k) :
    majorant_Efin r μ z ≤ p + ∑ k ∈ Finset.Ico 3 (r.card + 1), b k := by
  apply add_le_add hp
  apply Finset.sum_le_sum
  intro k hk
  calc
    _ ≤ C r.card k (variance r) / ((r.card.choose k : ℝ) * ‖μ‖ ^ k) :=
      mul_le_of_le_one_right (div_nonneg (C_nonneg _ _ _) (by positivity)) (hH k hk)
    _ ≤ b k := hb k hk

/-- Independent actual-coefficient certificate path, not the generic C majorant. -/
theorem actual_le (r : Multiset ℂ) (μ z : ℂ) (p : ℝ) (b : ℕ → ℝ)
    (hp : ‖1 - z‖ ^ (r.card + 1) + Gamma r μ * ‖B r.card 2 z‖ ≤ p)
    (hH : ∀ k ∈ Finset.Ico 3 (r.card + 1), ‖H r.card k z‖ ≤ 1)
    (hb : ∀ k ∈ Finset.Ico 3 (r.card + 1),
      ‖r.esymm k‖ / ((r.card.choose k : ℝ) * ‖μ‖ ^ k) ≤ b k) :
    Efin r μ z ≤ p + ∑ k ∈ Finset.Ico 3 (r.card + 1), b k := by
  apply add_le_add hp
  apply Finset.sum_le_sum
  intro k hk
  calc
    _ ≤ ‖r.esymm k‖ / ((r.card.choose k : ℝ) * ‖μ‖ ^ k) :=
      mul_le_of_le_one_right (by positivity) (hH k hk)
    _ ≤ b k := hb k hk

/-- Exact elementary coefficients of two equally repeated opposite deviations.
The formula uses Vieta and polynomial dilation, not enumeration of subsets. -/
theorem esymm_opposite_replicate (n k : ℕ) (d : ℂ) (hk : k ≤ 2 * n) :
    (Multiset.replicate n (-d) + Multiset.replicate n d).esymm k =
      if 2 ∣ (2 * n - k) then
        (-d ^ 2) ^ (n - (2 * n - k) / 2) * (n.choose ((2 * n - k) / 2) : ℂ)
      else 0 := by
  let r := Multiset.replicate n (-d) + Multiset.replicate n d
  have hc : r.card = 2 * n := by simp [r]; omega
  have hp : (r.map (fun w => Polynomial.X + Polynomial.C w)).prod =
      Polynomial.expand ℂ 2 ((Polynomial.X + Polynomial.C (-d ^ 2)) ^ n) := by
    simp only [r, Multiset.map_add, Multiset.map_replicate, Multiset.prod_add,
      Multiset.prod_replicate, map_pow, map_add, Polynomial.expand_X,
      Polynomial.expand_C, ← mul_pow]
    congr 1
    simp only [map_neg, map_pow]
    ring
  have hv := Multiset.prod_X_add_C_coeff r (k := 2 * n - k) (by omega)
  rw [hc, Nat.sub_sub_self hk, hp, Polynomial.coeff_expand (by decide : 0 < 2)] at hv
  simpa only [Polynomial.coeff_X_add_C_pow] using hv.symm

/-- A reusable exact lower rectangle for a real integrand. -/
theorem lower_rectangle (f : ℝ → ℝ) (s t b : ℝ) (hst : s ≤ t)
    (hf : IntervalIntegrable f MeasureTheory.volume s t)
    (hb : ∀ x ∈ Set.Icc s t, b ≤ f x) :
    (t - s) * b ≤ ∫ x in s..t, f x := by
  have h := intervalIntegral.integral_mono_on hst
    (intervalIntegrable_const (c := b)) hf hb
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using h

end Sendov.PaperCenteredCertificate
