import Sendov.Analytic.PaperCenteredEndpoint
import Sendov.Analytic.PaperConsequences

/-! # Actual variance suppresses the second endpoint

The variance and endpoint radius cannot be maximized independently. This
finite binomial estimate keeps their coupling and removes the apparent
polynomial-in-degree growth of the second endpoint's variance factor.
-/
noncomputable section
open scoped BigOperators
namespace Sendov.PaperCenteredVarianceEndpoint
open PaperCentered

/-- Pointwise unit-disk data couple the actual variance to the endpoint radius. -/
theorem actual_variance_endpoint (q : Multiset ℂ) (μ : ℂ) (a : ℝ)
    (hm : 0 < q.card) (hmean : q.sum = q.card * μ) (hq : ∀ z ∈ q, ‖z‖ ≤ 1) :
    ‖1 - (a : ℂ) * μ‖ ^ 2 + a ^ 2 * variance (q.map (fun z => z - μ)) ≤
      PaperPolar.b a μ.re := by
  have hv := (PaperConsequences.centered_variance_le q μ hm hmean hq).1
  have hid : ‖1 - (a : ℂ) * μ‖ ^ 2 = 1 - 2 * a * μ.re + a ^ 2 * ‖μ‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      Complex.one_im, Complex.mul_im]
    ring
  rw [hid]
  unfold PaperPolar.b
  nlinarith only [mul_le_mul_of_nonneg_left hv (sq_nonneg a)]

/-- A finite first binomial term bounds variance times an endpoint power.
This holds at all natural orders n, without a per-degree certificate. -/
theorem variance_endpoint_power (n : ℕ) (hn : 1 ≤ n) (a w v b : ℝ)
    (hv : 0 ≤ v) (hbound : w ^ 2 + a ^ 2 * v ≤ b) :
    (n : ℝ) * a ^ 2 * v * w ^ (2 * (n-1)) ≤ b ^ n := by
  have hu : 0 ≤ a ^ 2 * v := mul_nonneg (sq_nonneg a) hv
  have ht := Finset.single_le_sum
    (s := Finset.range (n+1))
    (f := fun k => (a^2*v)^k * (w^2)^(n-k) * (n.choose k : ℝ))
    (a := 1) (fun k _ => by positivity) (by simp; omega)
  have hs := add_pow (a^2*v) (w^2) n
  rw [← hs] at ht
  simp only [pow_one, Nat.choose_one_right, ← pow_mul] at ht
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ w^2+a^2*v) hbound n
  calc
    _ = (a^2*v) * w^(2*(n-1)) * (n : ℝ) := by ring
    _ ≤ (a^2*v+w^2)^n := ht
    _ = (w^2+a^2*v)^n := by rw [add_comm]
    _ ≤ b^n := hp

/-- The preceding suppression on the actual centered multiset. -/
theorem actual_variance_endpoint_power (q : Multiset ℂ) (μ : ℂ) (a : ℝ)
    (hm : 0 < q.card) (hmean : q.sum = q.card * μ) (hq : ∀ z ∈ q, ‖z‖ ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * a ^ 2 * variance (q.map (fun z => z - μ)) *
      ‖1 - (a : ℂ) * μ‖ ^ (2 * (n-1)) ≤ (PaperPolar.b a μ.re) ^ n := by
  apply variance_endpoint_power n hn a ‖1 - (a : ℂ)*μ‖
    (variance (q.map (fun z => z - μ))) (PaperPolar.b a μ.re)
  · exact PaperCoefficient.variance_nonneg _
  · exact actual_variance_endpoint q μ a hm hmean hq

end Sendov.PaperCenteredVarianceEndpoint
