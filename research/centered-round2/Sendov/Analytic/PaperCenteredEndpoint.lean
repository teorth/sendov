import Sendov.Analytic.PaperCenteredTail
import Sendov.Analytic.PaperPolar
import Mathlib.Data.Nat.Choose.Cast

/-! # Uniform control of the zeroth centered endpoint
A single binomial term proves the h/2 bound for the zeroth endpoint in every
degree; no finite table or bound on alpha is used. The positive-variance tail
and the second endpoint remain separate obligations.
-/
noncomputable section
open scoped BigOperators
namespace Sendov.PaperCenteredEndpoint

lemma binomial_term (n k : ℕ) (hk : k ≤ n) (b : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (n.choose k : ℝ) * (1 - b) ^ k * b ^ (n-k) ≤ 1 := by
  have ht := Finset.single_le_sum
    (s := Finset.range (n+1))
    (f := fun j => (1-b)^j * b^(n-j) * (n.choose j : ℝ))
    (a := k) (fun j _ => by positivity) (by simp; omega)
  have hs := add_pow (1-b) b n
  rw [show 1-b+b = 1 by ring, one_pow] at hs
  rw [← hs] at ht
  nlinarith only [ht]

/-- Any fixed endpoint order, with the finite binomial factor retained.
This provides arbitrarily high algebraic endpoint decay without a degree table. -/
theorem endpoint_power_order (m k : ℕ) (hk : k ≤ m + 1) (b L : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hL : 0 ≤ L)
    (hslope : 3 * b ≤ L * (1 - b)) :
    3^k * ((m+1).choose k : ℝ) * b^(m+1) ≤ L^k := by
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 3*b) hslope k
  have hc := binomial_term (m+1) k hk b hb0 hb1
  have he : b^k*b^(m+1-k) = b^(m+1) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  have ht := mul_le_mul_of_nonneg_right hs
    (mul_nonneg (Nat.cast_nonneg ((m+1).choose k)) (pow_nonneg hb0 (m+1-k)))
  have ht' := mul_le_mul_of_nonneg_left hc (pow_nonneg hL k)
  calc
    _ = (3*b)^k * (((m+1).choose k : ℝ)*b^(m+1-k)) := by rw [mul_pow, ← he]; ring
    _ ≤ (L*(1-b))^k * (((m+1).choose k : ℝ)*b^(m+1-k)) := ht
    _ = L^k * (((m+1).choose k : ℝ)*(1-b)^k*b^(m+1-k)) := by rw [mul_pow]; ring
    _ ≤ L^k := by simpa only [mul_one] using ht'

lemma binomial_second_term (n : ℕ) (hn : 2 ≤ n) (b : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (n.choose 2 : ℝ) * (1-b)^2 * b^(n-2) ≤ 1 := by
  have ht := Finset.single_le_sum
    (s := Finset.range (n+1))
    (f := fun k => (1-b)^k * b^(n-k) * (n.choose k : ℝ))
    (a := 2) (fun k _ => by positivity) (by simp; omega)
  have hs := add_pow (1-b) b n
  rw [show 1-b+b = 1 by ring, one_pow] at hs
  rw [← hs] at ht
  nlinarith only [ht]

/-- The rational polar slope controls the entire zeroth endpoint uniformly. -/
theorem endpoint_power_half (m : ℕ) (hm : 1 ≤ m) (b h : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (_hh : 0 ≤ h)
        (hslope : 3 * b ≤ (m : ℝ) * h * (1 - b)) :
    4*b^(m+1) ≤ h^2 := by
  have hc := binomial_second_term (m+1) (by omega) b hb0 hb1
  have hchoose : ((m+1).choose 2 : ℝ) = (m : ℝ)*((m : ℝ)+1)/2 := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  have he : b^2*b^(m-1) = b^(m+1) := by
    rw [← pow_add]
    congr 1
    omega
  have hs : 9*b^2 ≤ (m : ℝ)^2*h^2*(1-b)^2 := by
    have hp := mul_self_le_mul_self (by positivity : 0 ≤ 3*b) hslope
    nlinarith only [hp]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn : 0 ≤ ((m+1).choose 2 : ℝ) := Nat.cast_nonneg _
  have hs' := mul_le_mul_of_nonneg_right hs (mul_nonneg hn (pow_nonneg hb0 (m-1)))
  have hc' := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (m : ℝ)^2*h^2)
  have hbpow : 9*((m+1).choose 2 : ℝ)*b^(m+1) ≤ (m : ℝ)^2*h^2 := by
    calc
      _ = (9*b^2)*(((m+1).choose 2 : ℝ)*b^(m-1)) := by rw [← he]; ring
      _ ≤ ((m : ℝ)^2*h^2*(1-b)^2)*(((m+1).choose 2 : ℝ)*b^(m-1)) := hs'
      _ = (m : ℝ)^2*h^2 * (((m+1).choose 2 : ℝ)*(1-b)^2*b^(m-1)) := by ring
      _ ≤ (m : ℝ)^2*h^2 := by
        simpa only [show m+1-2 = m-1 by omega, mul_one] using hc'
  have hcoef : 4*(m : ℝ)^2 ≤ 9*((m+1).choose 2 : ℝ) := by rw [hchoose]; nlinarith
  have ht := (mul_le_mul_of_nonneg_right hcoef (pow_nonneg hb0 (m+1))).trans hbpow
  have hcancel : (m : ℝ)^2*(4*b^(m+1)) ≤ (m : ℝ)^2*h^2 := by nlinarith only [ht]
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hm0)).mp (by simpa only [mul_comm] using hcancel)

/-- A norm endpoint form, suitable for actual complex means. -/
theorem norm_endpoint_half (m : ℕ) (hm : 1 ≤ m) (z : ℂ) (b h : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hh : 0 ≤ h)
    (hslope : 3 * b ≤ (m : ℝ) * h * (1 - b)) (hz : ‖1 - z‖ ^ 2 ≤ b) :
    ‖1-z‖^(m+1) ≤ h/2 := by
  have hp := pow_le_pow_left₀ (sq_nonneg ‖1-z‖) hz (m+1)
  have he : (‖1-z‖^2)^(m+1) = (‖1-z‖^(m+1))^2 := by rw [← pow_mul, ← pow_mul]; congr 1; omega
  rw [he] at hp
  have hb := endpoint_power_half m hm b h hb0 hb1 hh hslope
  nlinarith only [hp, hb, hh, pow_nonneg (norm_nonneg (1-z)) (m+1)]

/-- The actual complex endpoint is at most h/2 on raw polar, uniformly in degree.
In fact the proof only needs 0<a<1, not a≥9/10. -/
theorem norm_endpoint_half_of_rawPolar (m : ℕ) (hm : 7 ≤ m) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hμ : ‖μ‖ ≤ 1)
    (hx0 : -1 ≤ μ.re) (hx1 : μ.re ≤ 1) (hr : PaperPolar.RawPolar m a μ.re) :
    ‖1 - (a : ℂ)*μ‖^(m+1) ≤ (1-a)/2 := by
  have hb0 := (PaperPolar.b_pos ha0.le ha1 hx1).le
  have hb1 := (PaperPolar.b_lt_one (by omega) ha0 ha1 hx0 hx1 hr).le
  have hb := PaperPolar.endpoint_bounds hm ha0 ha1 hx0 hx1 hr
  have hl := PaperPolar.lambda_pos (by omega : 0 < m) ha1
  have hs := (le_div_iff₀ (by positivity : 0 < 3 + PaperPolar.lambda m a)).mp (hb.1.trans hb.2)
  have hslope : 3 * PaperPolar.b a μ.re ≤ (m : ℝ)*(1-a)*(1-PaperPolar.b a μ.re) := by
    unfold PaperPolar.lambda at hs
    nlinarith only [hs]
  have hid : ‖1-(a : ℂ)*μ‖^2 = 1-2*a*μ.re+a^2*‖μ‖^2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      Complex.one_im, Complex.mul_im]
    ring
  have hu2 : ‖μ‖^2 ≤ 1 := by nlinarith [norm_nonneg μ]
  have hz : ‖1-(a : ℂ)*μ‖^2 ≤ PaperPolar.b a μ.re := by
    rw [hid]
    unfold PaperPolar.b
    nlinarith only [mul_le_mul_of_nonneg_left hu2 (sq_nonneg a)]
  exact norm_endpoint_half m (by omega) ((a : ℂ)*μ) (PaperPolar.b a μ.re) (1-a)
    hb0 hb1 (by linarith) hslope hz

/-- Entire square-root budget on the proved zero-actual-variance domain.
No positive-variance C-near assertion is hidden in this specialization. -/
theorem zero_variance_C_near (r : Multiset ℂ) (hm : 7 ≤ r.card) (a : ℝ) (μ : ℂ)
    (ha0 : 0 < a) (ha1 : a < 1) (hμ : ‖μ‖ ≤ 1)
    (hx0 : -1 ≤ μ.re) (hx1 : μ.re ≤ 1) (hr : PaperPolar.RawPolar r.card a μ.re)
    (hv : PaperCentered.variance r = 0) :
    PaperCenteredBound.majorant_Efin r μ ((a : ℂ)*μ) + PaperCentered.Gamma r μ <
      1-a*‖μ‖ := by
  have hg : PaperCentered.Gamma r μ = 0 := by simp [PaperCentered.Gamma, hv]
  have hE : PaperCenteredBound.majorant_Efin r μ ((a : ℂ)*μ) =
      ‖1-(a : ℂ)*μ‖^(r.card+1) := by
    unfold PaperCenteredBound.majorant_Efin
    rw [hg, zero_mul, add_zero]
    have ht : (∑ k ∈ Finset.Ico 3 (r.card+1),
        (PaperCenteredBound.C r.card k (PaperCentered.variance r) /
          ((r.card.choose k : ℝ)*‖μ‖^k))*‖PaperCentered.H r.card k ((a : ℂ)*μ)‖) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hk0 : 0 < k := by have := (Finset.mem_Ico.mp hk).1; omega
      simp [hv, PaperCenteredBound.C_zero_variance r.card k hk0]
    rw [ht, add_zero]
  rw [hE, hg, add_zero]
  have he := norm_endpoint_half_of_rawPolar r.card hm a μ ha0 ha1 hμ hx0 hx1 hr
  nlinarith [mul_le_mul_of_nonneg_left hμ ha0.le]

end Sendov.PaperCenteredEndpoint
