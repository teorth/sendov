import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Factorial.Cast
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Finite factorial-weighted centered tails. All bounds are uniform in the
ambient degree. The coefficient estimate is an explicit hypothesis; no claim
about the open positive-variance scalar budget is made. -/
noncomputable section
open scoped BigOperators
namespace Sendov.PaperFactorialTail

/-- The factorial/binomial coefficient shift, without division. -/
theorem descFactorial_mul_choose (m k K : ℕ) (hk : K ≤ k) :
    k.descFactorial K * m.choose k =
      m.descFactorial K * (m - K).choose (k - K) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose]
  calc
    _ = K.factorial * (m.choose k * k.choose K) := by ring
    _ = _ := by rw [Nat.choose_mul hk]; ring

/-- Exact finite factorial moment. No positivity assumptions are needed. -/
theorem factorial_binomial_moment (m K : ℕ) (hKm : K ≤ m) (X Y : ℝ) :
    (∑ k ∈ Finset.Ico K (m + 1),
      (k.descFactorial K : ℝ) * (m.choose k : ℝ) * X ^ k * Y ^ (m - k)) =
    (m.descFactorial K : ℝ) * X ^ K * (Y + X) ^ (m - K) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : m + 1 - K = (m - K) + 1 := by omega
  rw [hlen, add_comm Y X, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hc : ((K + j).descFactorial K : ℝ) * (m.choose (K + j) : ℝ) =
      (m.descFactorial K : ℝ) * ((m - K).choose j : ℝ) := by
    exact_mod_cast (by simpa using descFactorial_mul_choose m (K + j) K (by omega))
  rw [hc, pow_add]
  have he : m - (K + j) = m - K - j := by omega
  rw [he]
  ring

/-- Weighted Cauchy--Schwarz using a supplied pointwise square bound.
This formulation does not need nonnegativity of the summands themselves. -/
theorem factorial_weighted_cs (m K : ℕ) (C : ℕ → ℝ) (X A : ℝ)
    (hX : 0 ≤ X)
    (hcoeff : ∀ k ∈ Finset.Ico K (m + 1),
      C k ^ 2 ≤ (2 * (k : ℝ) + 1) * (m.choose k : ℝ) * X ^ k) :
    (∑ k ∈ Finset.Ico K (m + 1), C k * A ^ (m - k)) ^ 2 ≤
      (∑ k ∈ Finset.Ico K (m + 1), (2 * (k : ℝ) + 1) / (k.descFactorial K : ℝ)) *
      ∑ k ∈ Finset.Ico K (m + 1),
        (k.descFactorial K : ℝ) * (m.choose k : ℝ) * X ^ k * (A ^ 2) ^ (m - k) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro k hk
    positivity
  · intro k hk
    positivity
  · intro k hk
    have hw : (k.descFactorial K : ℝ) ≠ 0 := by
      exact ne_of_gt (by exact_mod_cast (Nat.descFactorial_pos.mpr (Finset.mem_Ico.mp hk).1))
    calc
      (C k * A ^ (m - k)) ^ 2 = C k ^ 2 * (A ^ 2) ^ (m - k) := by ring
      _ ≤ ((2 * (k : ℝ) + 1) * (m.choose k : ℝ) * X ^ k) *
          (A ^ 2) ^ (m - k) := mul_le_mul_of_nonneg_right (hcoeff k hk) (by positivity)
      _ = _ := by field_simp

/-- A single structural envelope for the whole finite tail, with any proved
upper bound S for the reciprocal factorial weights. -/
theorem factorial_tail_sq (m K : ℕ) (hKm : K ≤ m) (C : ℕ → ℝ) (X A S : ℝ)
    (hX : 0 ≤ X)
    (hcoeff : ∀ k ∈ Finset.Ico K (m + 1),
      C k ^ 2 ≤ (2 * (k : ℝ) + 1) * (m.choose k : ℝ) * X ^ k)
    (hweight : (∑ k ∈ Finset.Ico K (m + 1),
      (2 * (k : ℝ) + 1) / (k.descFactorial K : ℝ)) ≤ S) :
    (∑ k ∈ Finset.Ico K (m + 1), C k * A ^ (m - k)) ^ 2 ≤
      S * (m.descFactorial K : ℝ) * X ^ K * (A ^ 2 + X) ^ (m - K) := by
  have h := factorial_weighted_cs m K C X A hX hcoeff
  rw [factorial_binomial_moment m K hKm X (A ^ 2)] at h
  calc
    _ ≤ _ := h
    _ ≤ _ := by
      calc
        _ ≤ S * ((m.descFactorial K : ℝ) * X ^ K * (A ^ 2 + X) ^ (m - K)) :=
          mul_le_mul_of_nonneg_right hweight (by positivity)
        _ = _ := by ring

/-- Square-root version, including signed coefficients and all degenerate cases. -/
theorem factorial_tail_le_sqrt (m K : ℕ) (hKm : K ≤ m) (C : ℕ → ℝ) (X A S : ℝ)
    (hX : 0 ≤ X)
    (hcoeff : ∀ k ∈ Finset.Ico K (m + 1),
      C k ^ 2 ≤ (2 * (k : ℝ) + 1) * (m.choose k : ℝ) * X ^ k)
    (hweight : (∑ k ∈ Finset.Ico K (m + 1),
      (2 * (k : ℝ) + 1) / (k.descFactorial K : ℝ)) ≤ S) :
    (∑ k ∈ Finset.Ico K (m + 1), C k * A ^ (m - k)) ≤
      Real.sqrt (S * (m.descFactorial K : ℝ) * X ^ K * (A ^ 2 + X) ^ (m - K)) :=
  Real.le_sqrt_of_sq_le (factorial_tail_sq m K hKm C X A S hX hcoeff hweight)

/-- A real polynomial expression for the cubic falling factorial. -/
theorem cast_descFactorial_three (k : ℕ) (hk : 3 ≤ k) :
    (k.descFactorial 3 : ℝ) = (k : ℝ) * (k - 1) * (k - 2) := by
  simp [Nat.descFactorial_succ, Nat.cast_sub (show 2 ≤ k by omega),
    Nat.cast_sub (show 1 ≤ k by omega)]
  ring

/-- The antiderivative for the K=3 reciprocal factorial weights. -/
def weightPrimitive3 (k : ℕ) : ℝ :=
  2 / ((k : ℝ) - 2) + 1 / (2 * ((k : ℝ) - 1) * ((k : ℝ) - 2))

/-- Uniform telescoping step, not a finite-degree certificate. -/
theorem weight3_step (k : ℕ) (hk : 3 ≤ k) :
    (2 * (k : ℝ) + 1) / (k.descFactorial 3 : ℝ) =
      weightPrimitive3 k - weightPrimitive3 (k + 1) := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  rw [cast_descFactorial_three k hk]
  unfold weightPrimitive3
  push_cast
  have h0 : (k : ℝ) ≠ 0 := by linarith
  have h1 : (k : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (k : ℝ) - 2 ≠ 0 := by linarith
  simp only [add_sub_cancel_right]
  rw [show (k : ℝ) + 1 - 2 = (k : ℝ) - 1 by ring]
  field_simp
  ring

/-- Exact finite K=3 weight sum, retaining both terminal remainders. -/
theorem weight3_sum (m : ℕ) (hm : 3 ≤ m) :
    (∑ k ∈ Finset.Ico 3 (m + 1), (2 * (k : ℝ) + 1) / (k.descFactorial 3 : ℝ)) =
      9 / 4 - 2 / ((m : ℝ) - 1) - 1 / (2 * (m : ℝ) * ((m : ℝ) - 1)) := by
  calc
    _ = ∑ k ∈ Finset.Ico 3 (m + 1),
        ((-weightPrimitive3 (k + 1)) - (-weightPrimitive3 k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [weight3_step k (Finset.mem_Ico.mp hk).1]
      ring
    _ = -weightPrimitive3 (m + 1) - (-weightPrimitive3 3) :=
      Finset.sum_Ico_sub (fun k => -weightPrimitive3 k) (by omega)
    _ = _ := by
      unfold weightPrimitive3
      push_cast
      norm_num
      ring

/-- The degree-independent K=3 constant. -/
theorem weight3_sum_le (m : ℕ) (hm : 3 ≤ m) :
    (∑ k ∈ Finset.Ico 3 (m + 1), (2 * (k : ℝ) + 1) / (k.descFactorial 3 : ℝ)) ≤ 9 / 4 := by
  rw [weight3_sum m hm]
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : 0 < (m : ℝ) - 1 := by linarith
  have h1 : 0 ≤ 2 / ((m : ℝ) - 1) := by positivity
  have h2 : 0 ≤ 1 / (2 * (m : ℝ) * ((m : ℝ) - 1)) := by positivity
  linarith

/-- A real polynomial expression for the quartic falling factorial. -/
theorem cast_descFactorial_four (k : ℕ) (hk : 4 ≤ k) :
    (k.descFactorial 4 : ℝ) = (k : ℝ) * (k - 1) * (k - 2) * (k - 3) := by
  rw [show 4 = 3 + 1 from rfl, Nat.descFactorial_succ, Nat.cast_mul,
    Nat.cast_sub (show 3 ≤ k by omega), cast_descFactorial_three k (by omega)]
  push_cast
  ring

/-- Discrete antiderivative for the K=4 weights. -/
def weightPrimitive4 (k : ℕ) : ℝ :=
  1 / (((k : ℝ) - 2) * ((k : ℝ) - 3)) +
    1 / (3 * ((k : ℝ) - 1) * ((k : ℝ) - 2) * ((k : ℝ) - 3))

theorem weight4_step (k : ℕ) (hk : 4 ≤ k) :
    (2 * (k : ℝ) + 1) / (k.descFactorial 4 : ℝ) =
      weightPrimitive4 k - weightPrimitive4 (k + 1) := by
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  rw [cast_descFactorial_four k hk]
  unfold weightPrimitive4
  push_cast
  have h0 : (k : ℝ) ≠ 0 := by linarith
  have h1 : (k : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (k : ℝ) - 2 ≠ 0 := by linarith
  have h3 : (k : ℝ) - 3 ≠ 0 := by linarith
  simp only [add_sub_cancel_right]
  rw [show (k : ℝ) + 1 - 2 = (k : ℝ) - 1 by ring,
    show (k : ℝ) + 1 - 3 = (k : ℝ) - 2 by ring]
  field_simp
  ring

/-- Exact finite K=4 sum with its two positive remainders. -/
theorem weight4_sum (m : ℕ) (hm : 4 ≤ m) :
    (∑ k ∈ Finset.Ico 4 (m + 1), (2 * (k : ℝ) + 1) / (k.descFactorial 4 : ℝ)) =
      5 / 9 - 1 / (((m : ℝ) - 1) * ((m : ℝ) - 2)) -
        1 / (3 * (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2)) := by
  calc
    _ = ∑ k ∈ Finset.Ico 4 (m + 1),
        ((-weightPrimitive4 (k + 1)) - (-weightPrimitive4 k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [weight4_step k (Finset.mem_Ico.mp hk).1]
      ring
    _ = -weightPrimitive4 (m + 1) - (-weightPrimitive4 4) :=
      Finset.sum_Ico_sub (fun k => -weightPrimitive4 k) (by omega)
    _ = _ := by
      unfold weightPrimitive4
      push_cast
      norm_num
      ring

/-- The degree-independent K=4 constant. -/
theorem weight4_sum_le (m : ℕ) (hm : 4 ≤ m) :
    (∑ k ∈ Finset.Ico 4 (m + 1), (2 * (k : ℝ) + 1) / (k.descFactorial 4 : ℝ)) ≤ 5 / 9 := by
  rw [weight4_sum m hm]
  have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : 0 < (m : ℝ) - 1 := by linarith
  have hm2 : 0 < (m : ℝ) - 2 := by linarith
  have h1 : 0 ≤ 1 / (((m : ℝ) - 1) * ((m : ℝ) - 2)) := by positivity
  have h2 : 0 ≤ 1 / (3 * (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2)) := by positivity
  linarith

/-- The supplied uniform coefficient estimate is preserved under multiplication
by x^k. This is the only coefficient input to the structural envelope. -/
theorem rescale_coefficient_bound (m K : ℕ) (C : ℕ → ℝ) (v x : ℝ)
    (hcoeff : ∀ k ∈ Finset.Ico K (m + 1),
      C k ^ 2 ≤ (2 * (k : ℝ) + 1) * (m.choose k : ℝ) * v ^ k) :
    ∀ k ∈ Finset.Ico K (m + 1),
      (C k * x ^ k) ^ 2 ≤ (2 * (k : ℝ) + 1) * (m.choose k : ℝ) * (v * x ^ 2) ^ k := by
  intro k hk
  calc
    _ = C k ^ 2 * (x ^ k) ^ 2 := by ring
    _ ≤ ((2 * (k : ℝ) + 1) * (m.choose k : ℝ) * v ^ k) * (x ^ k) ^ 2 :=
      mul_le_mul_of_nonneg_right (hcoeff k hk) (sq_nonneg _)
    _ = _ := by ring

/-- Pointwise high-degree envelope in the actual variance variable. The x used
in the paper is a*t. The half-power is represented as a square root of a
natural power, so odd m-K is not truncated by natural-number division. -/
theorem coefficient_tail_le (m K : ℕ) (hKm : K ≤ m) (C : ℕ → ℝ) (v x A S : ℝ)
    (hv : 0 ≤ v) (hx : 0 ≤ x) (hS : 0 ≤ S)
    (hcoeff : ∀ k ∈ Finset.Ico K (m + 1),
      C k ^ 2 ≤ (2 * (k : ℝ) + 1) * (m.choose k : ℝ) * v ^ k)
    (hweight : (∑ k ∈ Finset.Ico K (m + 1),
      (2 * (k : ℝ) + 1) / (k.descFactorial K : ℝ)) ≤ S) :
    (∑ k ∈ Finset.Ico K (m + 1), C k * x ^ k * A ^ (m - k)) ≤
      Real.sqrt (S * (m.descFactorial K : ℝ)) * (x * Real.sqrt v) ^ K *
        Real.sqrt ((A ^ 2 + v * x ^ 2) ^ (m - K)) := by
  have h := factorial_tail_sq m K hKm (fun k => C k * x ^ k)
    (v * x ^ 2) A S (by positivity) (rescale_coefficient_bound m K C v x hcoeff) hweight
  have hr : 0 ≤ Real.sqrt (S * (m.descFactorial K : ℝ)) * (x * Real.sqrt v) ^ K *
      Real.sqrt ((A ^ 2 + v * x ^ 2) ^ (m - K)) := by positivity
  have he : (Real.sqrt (S * (m.descFactorial K : ℝ)) * (x * Real.sqrt v) ^ K *
      Real.sqrt ((A ^ 2 + v * x ^ 2) ^ (m - K))) ^ 2 =
      S * (m.descFactorial K : ℝ) * (v * x ^ 2) ^ K * (A ^ 2 + v * x ^ 2) ^ (m - K) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      ← pow_mul, Nat.mul_comm K 2, pow_mul, mul_pow, Real.sq_sqrt hv]
    ring
  nlinarith

/-- K=3 specialization with S3=9/4, uniform in the ambient degree. -/
theorem coefficient_tail3_le (m : ℕ) (hm : 3 ≤ m) (C : ℕ → ℝ) (v x A : ℝ)
    (hv : 0 ≤ v) (hx : 0 ≤ x)
    (hcoeff : ∀ k ∈ Finset.Ico 3 (m + 1),
      C k ^ 2 ≤ (2 * (k : ℝ) + 1) * (m.choose k : ℝ) * v ^ k) :
    (∑ k ∈ Finset.Ico 3 (m + 1), C k * x ^ k * A ^ (m - k)) ≤
      Real.sqrt ((9 / 4) * (m.descFactorial 3 : ℝ)) * (x * Real.sqrt v) ^ 3 *
        Real.sqrt ((A ^ 2 + v * x ^ 2) ^ (m - 3)) :=
  coefficient_tail_le m 3 hm C v x A (9 / 4) hv hx (by norm_num) hcoeff (weight3_sum_le m hm)

/-- K=4 specialization with S4=5/9, uniform in the ambient degree. -/
theorem coefficient_tail4_le (m : ℕ) (hm : 4 ≤ m) (C : ℕ → ℝ) (v x A : ℝ)
    (hv : 0 ≤ v) (hx : 0 ≤ x)
    (hcoeff : ∀ k ∈ Finset.Ico 4 (m + 1),
      C k ^ 2 ≤ (2 * (k : ℝ) + 1) * (m.choose k : ℝ) * v ^ k) :
    (∑ k ∈ Finset.Ico 4 (m + 1), C k * x ^ k * A ^ (m - k)) ≤
      Real.sqrt ((5 / 9) * (m.descFactorial 4 : ℝ)) * (x * Real.sqrt v) ^ 4 *
        Real.sqrt ((A ^ 2 + v * x ^ 2) ^ (m - 4)) :=
  coefficient_tail_le m 4 hm C v x A (5 / 9) hv hx (by norm_num) hcoeff (weight4_sum_le m hm)

/-- Converting the half-power notation without any parity restriction. -/
theorem sqrt_pow_eq_rpow (B : ℝ) (hB : 0 ≤ B) (n : ℕ) :
    Real.sqrt (B ^ n) = B ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hB]
  congr 1
  ring

/-- The paper's pointwise high-degree bound, with real half-exponent. -/
theorem coefficient_tail_rpow (m K : ℕ) (hKm : K ≤ m) (C : ℕ → ℝ) (v x A S : ℝ)
    (hv : 0 ≤ v) (hx : 0 ≤ x) (hS : 0 ≤ S)
    (hcoeff : ∀ k ∈ Finset.Ico K (m + 1),
      C k ^ 2 ≤ (2 * (k : ℝ) + 1) * (m.choose k : ℝ) * v ^ k)
    (hweight : (∑ k ∈ Finset.Ico K (m + 1),
      (2 * (k : ℝ) + 1) / (k.descFactorial K : ℝ)) ≤ S) :
    (∑ k ∈ Finset.Ico K (m + 1), C k * x ^ k * A ^ (m - k)) ≤
      Real.sqrt (S * (m.descFactorial K : ℝ)) * (x * Real.sqrt v) ^ K *
        (A ^ 2 + v * x ^ 2) ^ ((m - K : ℕ) / (2 : ℝ)) := by
  rw [← sqrt_pow_eq_rpow _ (by positivity)]
  exact coefficient_tail_le m K hKm C v x A S hv hx hS hcoeff hweight

end Sendov.PaperFactorialTail
