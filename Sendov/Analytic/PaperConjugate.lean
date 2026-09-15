import Sendov.Analytic.PaperCenteredBound
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.NormNum.NatFactorial

noncomputable section
open scoped BigOperators
namespace Sendov.PaperConjugate
open PaperCentered PaperCenteredBound

def y (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)
def plus (x : ℝ) : ℂ := ⟨x, y x⟩
def minus (x : ℝ) : ℂ := ⟨x, -y x⟩
/-- Exactly n copies of each conjugate; multiplicities are retained. -/
def family (n : ℕ) (x : ℝ) : Multiset ℂ :=
  Multiset.replicate n (plus x) + Multiset.replicate n (minus x)

@[simp] theorem card_family (n : ℕ) (x : ℝ) : (family n x).card = 2*n := by
  simp [family]; omega

theorem y_sq (x : ℝ) (hx : x ^ 2 ≤ 1) : y x ^ 2 = 1 - x ^ 2 :=
  Real.sq_sqrt (sub_nonneg.mpr hx)

theorem norm_plus (x : ℝ) (hx : x ^ 2 ≤ 1) : ‖plus x‖ = 1 := by
  have h : ‖plus x‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    change x*x + y x*y x = 1
    nlinarith [y_sq x hx]
  nlinarith [norm_nonneg (plus x)]

theorem norm_minus (x : ℝ) (hx : x ^ 2 ≤ 1) : ‖minus x‖ = 1 := by
  have h : ‖minus x‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    change x*x + (-y x)*(-y x) = 1
    nlinarith [y_sq x hx]
  nlinarith [norm_nonneg (minus x)]

theorem norm_family (n : ℕ) (x : ℝ) (hx : x ^ 2 ≤ 1) :
    ∀ q ∈ family n x, ‖q‖ = 1 := by
  intro q hq
  simp only [family, Multiset.mem_add, Multiset.mem_replicate] at hq
  rcases hq with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact norm_plus x hx
  · exact norm_minus x hx

theorem sum_family (n : ℕ) (x : ℝ) : (family n x).sum = (2*n : ℕ) * (x : ℂ) := by
  simp only [family, Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul]
  apply Complex.ext <;> simp [plus, minus] <;> ring

theorem mean_family (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (family n x).sum / (family n x).card = (x : ℂ) := by
  rw [sum_family, card_family]
  have h : ((2*n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2*n ≠ 0)
  exact mul_div_cancel_left₀ _ h

theorem variance_family (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ^ 2 ≤ 1) :
    variance ((family n x).map (fun q => q - (x : ℂ))) = 1 - x ^ 2 := by
  have hp : ‖plus x - (x : ℂ)‖ ^ 2 = 1 - x ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simpa [plus, pow_two] using y_sq x hx
  have hm : ‖minus x - (x : ℂ)‖ ^ 2 = 1 - x ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simpa [minus, pow_two] using y_sq x hx
  simp only [variance, Multiset.map_map, Multiset.card_map, card_family,
    family, Multiset.map_add, Multiset.map_replicate, Multiset.sum_add,
    Multiset.sum_replicate, nsmul_eq_mul, Function.comp_apply, hp, hm,
    Multiset.card_add, Multiset.card_replicate]
  have h : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp
  <;> ring

theorem pair_product (x : ℝ) (hx : x ^ 2 ≤ 1) (s r : ℝ) :
    ((s : ℂ) + r * plus x) * (s + r * minus x) =
      ((s^2 + 2*s*r*x + r^2 : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp only [plus, minus, pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, mul_zero, sub_zero, add_zero, zero_add]
  · have h := congrArg (fun z : ℝ => r^2*z) (y_sq x hx)
    nlinarith only [h]
  · ring

theorem polar_product (n : ℕ) (x a t : ℝ) (hx : x^2 ≤ 1) :
    ((family n x).map (fun q => (a : ℂ) + ((1-a^2)*t : ℝ)*q)).prod =
      (((a^2 + 2*a*(1-a^2)*x*t + (1-a^2)^2*t^2)^n : ℝ) : ℂ) := by
  simp only [family, Multiset.map_add, Multiset.map_replicate,
    Multiset.prod_add, Multiset.prod_replicate, ← mul_pow]
  rw [pair_product x hx]
  push_cast
  ring

def K (n : ℕ) (a x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, ((family n x).map
    (fun q => (a : ℂ) + ((1-a^2)*t : ℝ)*q)).prod

def J (n : ℕ) (a x : ℝ) : ℂ :=
  ((family n x).card+1 : ℂ) * (∫ t in (0 : ℝ)..1,
    ((family n x).map (fun q => 1 - (a : ℂ)*t*q)).prod)

theorem K_eq (n : ℕ) (a x : ℝ) (hx : x^2 ≤ 1) :
    K n a x = ((∫ t in (0 : ℝ)..1,
      (a^2 + 2*a*(1-a^2)*x*t + (1-a^2)^2*t^2)^n : ℝ) : ℂ) := by
  unfold K
  simp_rw [polar_product n x a _ hx]
  exact intervalIntegral.integral_ofReal

/-- Finite polynomial integration; certificates supply the exact expansion. -/
theorem integral_coeffs (d : ℕ) (c : Fin d → ℝ) (f : ℝ → ℝ)
    (he : ∀ t, f t = ∑ k : Fin d, c k * t^k.val) :
    (∫ t in (0 : ℝ)..1, f t) = ∑ k : Fin d, c k / (k.val+1) := by
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp
    ring
  · intro k hk
    exact (continuous_const.mul (continuous_pow k.val)).intervalIntegrable _ _

/-- Real endpoint polynomials, still the exact B and H from the paper. -/
def BR (m k : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), ((m+1).choose j : ℝ)*z^j*(1-z)^(m+1-j)

theorem B_ofReal (m k : ℕ) (z : ℝ) : B m k (z : ℂ) = (BR m k z : ℂ) := by
  simp [B, BR]

theorem norm_H_ofReal (m k : ℕ) (z : ℝ) : ‖H m k (z : ℂ)‖ = |1-BR m k z| := by
  rw [H, B_ofReal, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]

def scalarBudget (m : ℕ) (a x : ℝ) : ℝ :=
  |1-a*x|^(m+1) + (1-x^2)/(((m : ℝ)-1)*x^2)*|BR m 2 (a*x)| +
    ∑ k ∈ Finset.Ico 3 (m+1),
      C m k (1-x^2) / ((m.choose k : ℝ)*x^k)*|1-BR m k (a*x)|

theorem budget_eq (n : ℕ) (hn : 0 < n) (a x : ℝ) (hx0 : 0 ≤ x) (hx : x^2 ≤ 1) :
    majorant_Efin ((family n x).map (fun q => q-(x : ℂ))) (x : ℂ) ((a : ℂ)*x) =
      scalarBudget (2*n) a x := by
  unfold majorant_Efin Gamma scalarBudget
  rw [variance_family n hn x hx]
  simp only [Multiset.card_map, card_family, ← Complex.ofReal_mul,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hx0, B_ofReal, norm_H_ofReal]

theorem BR_succ (m k : ℕ) (z : ℝ) : BR m (k+1) z = BR m k z +
    ((m+1).choose (k+1) : ℝ)*z^(k+1)*(1-z)^(m+1-(k+1)) := by
  simp [BR, Finset.sum_range_succ]

/-- Squared rational certificates bound the literal square root times H.
No H endpoint is discarded, even at degree m. -/
theorem sqrt_term_le (s d h b : ℝ) (hs : 0 ≤ s) (hd : 0 < d) (hb : 0 ≤ b)
    (hcert : s*h^2 ≤ (b*d)^2) : Real.sqrt s / d * |h| ≤ b := by
  have hsq := Real.sq_sqrt hs
  have ha : |h|^2 = h^2 := sq_abs h
  have hmul : (Real.sqrt s * |h|)^2 ≤ (b*d)^2 := by
    rw [mul_pow, hsq, ha]
    exact hcert
  have hle : Real.sqrt s * |h| ≤ b*d := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg s) (abs_nonneg h), mul_nonneg hb hd.le]
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hd).2 hle

def term (m k : ℕ) (x z : ℝ) : ℝ :=
  C m k (1-x^2) / ((m.choose k : ℝ)*x^k)*|1-BR m k z|

theorem scalarBudget_le (m : ℕ) (hm : 4 ≤ m) (a x b c : ℝ)
    (h3 : term m 3 x (a*x) ≤ b)
    (hrest : ∀ k ∈ Finset.Ico 4 (m+1), term m k x (a*x) ≤ c) :
    scalarBudget m a x ≤ |1-a*x|^(m+1) +
      (1-x^2)/(((m : ℝ)-1)*x^2)*|BR m 2 (a*x)| + b + (m-3 : ℕ)*c := by
  unfold scalarBudget
  change _ + ∑ k ∈ Finset.Ico 3 (m+1), term m k x (a*x) ≤ _
  rw [Finset.sum_eq_sum_Ico_succ_bot (show 3 < m+1 by omega)]
  have hh := Finset.sum_le_sum hrest
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hh
  have heq : m+1-4 = m-3 := by omega
  rw [heq] at hh
  linarith

theorem budget_implies_J (n : ℕ) (hn : 0 < n) (a x : ℝ) (ha : 0 ≤ a)
    (hx0 : 0 < x) (hx : x^2 ≤ 1)
    (hb : scalarBudget (2*n) a x + (1-x^2)/(((2*n : ℕ) : ℝ)-1)/x^2 < 1-a*x) :
    1 < ‖J n a x‖ := by
  apply PaperCenteredBound.C_budget (family n x) a (x : ℂ)
    (by simp; omega) ha (by rw [sum_family, card_family])
    (by exact_mod_cast hx0.ne')
  rw [budget_eq n hn a x hx0.le hx]
  simpa [Gamma, variance_family n hn x hx, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hx0, div_mul_eq_div_div] using hb

end Sendov.PaperConjugate
