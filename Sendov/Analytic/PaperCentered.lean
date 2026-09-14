import Sendov.Counterexample.Identities
import Mathlib.RingTheory.Polynomial.Vieta

/-! # Finite centered expansion
All endpoints are finite complex polynomials; no reality or positivity of the mean is used.
-/
noncomputable section
open scoped BigOperators
open Polynomial
namespace Sendov.PaperCentered

/-- The finite endpoint sum in the paper. -/
def B (m k : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (k + 1), (m + 1).choose j * z ^ j * (1 - z) ^ (m + 1 - j)

/-- The complementary endpoint, retained at every degree. -/
def H (m k : ℕ) (z : ℂ) : ℂ := 1 - B m k z

@[simp] theorem B_zero (m : ℕ) (z : ℂ) : B m 0 z = (1 - z) ^ (m + 1) := by
  simp [B]

theorem H_succ (m k : ℕ) (z : ℂ) :
    H m (k + 1) z = H m k z -
      (m + 1).choose (k + 1) * z ^ (k + 1) * (1 - z) ^ (m - k) := by
  simp only [H, B, Finset.sum_range_succ]
  rw [show m + 1 - (k + 1) = m - k by omega]
  ring

/-- Homogeneous Vieta identity, including repeated values and zero scaling. -/
theorem prod_affine (r : Multiset ℂ) (x y : ℂ) :
    (r.map (fun v => x + y * v)).prod =
      ∑ k ∈ Finset.range (r.card + 1), y ^ k * r.esymm k * x ^ (r.card - k) := by
  have h := congrArg (Polynomial.eval x)
    (Multiset.prod_X_add_C_eq_sum_esymm (r.map (fun v => y * v)))
  have hs (k : ℕ) : (r.map (fun v => y * v)).esymm k = y ^ k * r.esymm k := by
    exact (Multiset.pow_smul_esymm y k r).symm
  simpa only [eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_add,
    eval_X, eval_C, eval_finsetSum, eval_mul, eval_pow, Multiset.card_map, hs] using h

/-- The actual centered product expansion, before integration. -/
theorem centered_product (q : Multiset ℂ) (a μ : ℂ) (t : ℝ) :
    (q.map (fun v => 1 - a * t * v)).prod =
      ∑ k ∈ Finset.range (q.card + 1), (-a) ^ k *
        (q.map (fun v => v - μ)).esymm k * (t : ℂ) ^ k *
        (1 - a * μ * t) ^ (q.card - k) := by
  have h := prod_affine (q.map (fun v => v - μ)) (1 - a * μ * t) (-a * t)
  simp only [Multiset.map_map, Function.comp_def, Multiset.card_map, mul_pow] at h
  convert h using 1
  · congr 2; ext v; ring
  · apply Finset.sum_congr rfl
    intro k hk
    ring

@[simp] theorem esymm_zero (r : Multiset ℂ) : r.esymm 0 = 1 := by
  simp [Multiset.esymm]

@[simp] theorem esymm_one (r : Multiset ℂ) : r.esymm 1 = r.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one]

/-- Elementary symmetric recursion, without distinctness assumptions. -/
theorem esymm_cons (v : ℂ) (r : Multiset ℂ) (k : ℕ) :
    (v ::ₘ r).esymm (k + 1) = r.esymm (k + 1) + v * r.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add,
    Multiset.sum_add, Multiset.map_map, Function.comp_def, Multiset.prod_cons]
  rw [Multiset.sum_map_mul_left]

/-- Degree two Newton identity proved directly from the multiset recursion. -/
theorem two_mul_esymm_two (r : Multiset ℂ) :
    2 * r.esymm 2 = r.sum ^ 2 - (r.map (fun v => v ^ 2)).sum := by
  induction r using Multiset.induction_on with
  | empty => simp [Multiset.esymm, show 2 = 1 + 1 from rfl, Multiset.powersetCard_zero_right]
  | cons v r ih =>
    rw [show 2 = 1 + 1 from rfl, esymm_cons, esymm_one]
    simp only [Multiset.sum_cons, Multiset.map_cons]
    linear_combination ih

/-- Centering really kills the linear coefficient. -/
theorem centered_sum (q : Multiset ℂ) (μ : ℂ) (hμ : q.sum = q.card * μ) :
    (q.map (fun v => v - μ)).sum = 0 := by
  have hc : (q.map (fun _ => μ)).sum = (q.card : ℂ) * μ := by
    induction q using Multiset.induction_on with
    | empty => simp
    | cons v q ih => simp [Nat.cast_add, add_mul]; ring
  simp only [Multiset.sum_map_sub, Multiset.map_id', hc, hμ, sub_self]

/-- Differentiating the finite endpoint sum telescopes exactly. -/
theorem hasDerivAt_H (m k : ℕ) (hk : k ≤ m) (z : ℂ) :
    HasDerivAt (H m k) ((m + 1) * (m.choose k : ℂ) * z ^ k * (1 - z) ^ (m - k)) z := by
  induction k with
  | zero =>
    have he : H m 0 = fun w => 1 - (1 - w) ^ (m + 1) := by
      funext w; simp [H]
    rw [he]
    simpa using
      (((hasDerivAt_id z).const_sub 1).pow (m + 1)).const_sub 1
  | succ k ih =>
    have hk' : k ≤ m := by omega
    have hmk : m - k = (m - (k + 1)) + 1 := by omega
    have hc₁ : ((m + 1 : ℕ) : ℂ) * m.choose k =
        ((m + 1).choose (k + 1) : ℂ) * (k + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq m k
    have hc₂ : (m.choose (k + 1) : ℂ) * (m + 1) =
        ((m + 1).choose (k + 1) : ℂ) * (m - k) := by
      have h := Nat.choose_mul_succ_eq m (k + 1)
      rw [show m + 1 - (k + 1) = m - k by omega] at h
      exact_mod_cast h
    have hd := (ih hk').sub
      ((((hasDerivAt_id z).pow (k + 1)).const_mul
        ((m + 1).choose (k + 1) : ℂ)).mul
        (((hasDerivAt_id z).const_sub 1).pow (m - k)))
    have he : H m (k + 1) = fun w => H m k w -
        (m + 1).choose (k + 1) * w ^ (k + 1) * (1 - w) ^ (m - k) :=
      funext (H_succ m k)
    rw [he]
    convert hd using 1 <;> try rfl
    simp only [Pi.pow_apply, id_eq, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel, mul_one, mul_neg, hmk, pow_succ]
    have hc₃ : ((m - (k + 1) : ℕ) : ℂ) + 1 = (m : ℂ) - k := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_sub hk'] using
        congrArg (Nat.cast : ℕ → ℂ) hmk.symm
    rw [hc₃]
    push_cast at hc₁
    linear_combination -(z ^ k * (1 - z) ^ (m - (k + 1)) * (1 - z)) * hc₁ +
      (z ^ k * z * (1 - z) ^ (m - (k + 1))) * hc₂

@[simp] theorem H_at_zero (m k : ℕ) : H m k 0 = 0 := by
  rw [H, B, Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    simp [zero_pow hj0]
  · simp

/-- Integer incomplete-beta identity, division-free and valid for every complex z,
including z=0 and the top index k=m. -/
theorem finite_beta (m k : ℕ) (hk : k ≤ m) (z : ℂ) :
    ((m + 1) * (m.choose k : ℂ) * z ^ (k + 1)) *
      (∫ t in (0 : ℝ)..1, (t : ℂ) ^ k * (1 - z * t) ^ (m - k)) = H m k z := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => H m k (z * t))
      (((m + 1) * (m.choose k : ℂ) * z ^ (k + 1)) *
        ((t : ℂ) ^ k * (1 - z * t) ^ (m - k))) t := by
    have ht : HasDerivAt (fun t : ℝ => z * (t : ℂ)) z t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul z
    convert (hasDerivAt_H m k hk (z * t)).scomp t ht using 1 <;> try rfl
    simp only [smul_eq_mul, mul_pow, pow_succ]
    ring
  have hi : IntervalIntegrable (fun t : ℝ =>
      ((m + 1) * (m.choose k : ℂ) * z ^ (k + 1)) *
        ((t : ℂ) ^ k * (1 - z * t) ^ (m - k))) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simpa [intervalIntegral.integral_const_mul] using h

/-- Normalized elementary coefficient (the sign is part of the coefficient). -/
def coeff (r : Multiset ℂ) (μ : ℂ) (k : ℕ) : ℂ :=
  (-1) ^ k * r.esymm k / ((r.card.choose k : ℂ) * μ ^ k)

/-- Exact finite centered beta expansion. Centering need not equal the mean for this
identity; the mean condition is used only to remove degree one below. -/
theorem centered_integral (q : Multiset ℂ) (a μ : ℂ) (hμ : μ ≠ 0) :
    (q.card + 1) * (a * μ) *
      (∫ t in (0 : ℝ)..1, (q.map (fun v => 1 - a * t * v)).prod) =
      ∑ k ∈ Finset.range (q.card + 1),
        coeff (q.map (fun v => v - μ)) μ k * H q.card k (a * μ) := by
  let r := q.map (fun v => v - μ)
  have he : (fun t : ℝ => (q.map (fun v => 1 - a * t * v)).prod) =
      fun t : ℝ => ∑ k ∈ Finset.range (q.card + 1),
        ((-a) ^ k * r.esymm k) * ((t : ℂ) ^ k * (1 - a * μ * t) ^ (q.card - k)) := by
    funext t
    rw [centered_product q a μ t]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [r]
    ring
  rw [he, intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ q.card := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hc : (q.card.choose k : ℂ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hk'
    rw [intervalIntegral.integral_const_mul, ← finite_beta q.card k hk' (a * μ)]
    dsimp [coeff, r]
    rw [Multiset.card_map]
    rw [show -a = (-1 : ℂ) * a by ring]
    simp only [mul_pow, pow_succ]
    field_simp
  · intro k hk
    apply Continuous.intervalIntegrable
    fun_prop

/-- The top endpoint is not dropped: H at k=m is exactly z^(m+1). -/
theorem H_top (m : ℕ) (z : ℂ) : H m m z = z ^ (m + 1) := by
  have hs := add_pow z (1 - z) (m + 1)
  rw [Finset.sum_range_succ] at hs
  simp only [Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, mul_one] at hs
  have hb : B m m z = ∑ i ∈ Finset.range (m + 1),
      z ^ i * (1 - z) ^ (m + 1 - i) * ((m + 1).choose i : ℂ) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [H, hb]
  have he : z + (1 - z) = 1 := by ring
  rw [he, one_pow] at hs
  linear_combination hs

/-- The centered second moment, without complex conjugation. -/
def kappa (r : Multiset ℂ) : ℂ := (r.map (fun v => v ^ 2)).sum / r.card

/-- The exact second-order correction. -/
def correction (r : Multiset ℂ) (μ : ℂ) : ℂ :=
  kappa r / (((r.card : ℂ) - 1) * μ ^ 2)

@[simp] theorem coeff_zero (r : Multiset ℂ) (μ : ℂ) : coeff r μ 0 = 1 := by
  simp [coeff]

theorem coeff_one (r : Multiset ℂ) (μ : ℂ) (hr : r.sum = 0) : coeff r μ 1 = 0 := by
  simp [coeff, hr]

/-- The second-order coefficient is computed, not postulated. -/
theorem coeff_two (r : Multiset ℂ) (μ : ℂ) (hm : 2 ≤ r.card)
    (hr : r.sum = 0) (hμ : μ ≠ 0) : coeff r μ 2 = -correction r μ := by
  have hc : (r.card.choose 2 : ℂ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hm
  have hm₀ : (r.card : ℂ) ≠ 0 := by exact_mod_cast (by omega : r.card ≠ 0)
  have hm₁ : (r.card : ℂ) - 1 ≠ 0 := by
    have h : (r.card : ℂ) ≠ 1 := by exact_mod_cast (by omega : r.card ≠ 1)
    exact sub_ne_zero.mpr h
  have hc₂ : 2 * (r.card.choose 2 : ℂ) = (r.card : ℂ) * ((r.card : ℂ) - 1) := by
    have h₂ := Nat.add_one_mul_choose_eq (r.card - 1) 1
    rw [show r.card - 1 + 1 = r.card by omega] at h₂
    norm_num only [Nat.choose_one_right, Nat.reduceAdd] at h₂
    have h₃ : (r.card : ℂ) * ((r.card : ℂ) - 1) = (r.card.choose 2 : ℂ) * 2 := by
      simpa only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ r.card), Nat.cast_one,
        Nat.cast_ofNat] using congrArg (Nat.cast : ℕ → ℂ) h₂
    linear_combination h₃.symm
  have he := two_mul_esymm_two r
  rw [hr, zero_pow (by decide : 2 ≠ 0), zero_sub] at he
  dsimp [coeff, correction, kappa]
  norm_num
  field_simp
  linear_combination (r.card.choose 2 : ℂ) * he - r.esymm 2 * hc₂

/-- Every degree from 3 through m is retained. -/
def tail (r : Multiset ℂ) (μ z : ℂ) : ℂ :=
  ∑ k ∈ Finset.Ico 3 (r.card + 1), coeff r μ k * H r.card k z

/-- Finite epsilon, with both low-degree endpoint corrections and all higher H terms. -/
def epsilon (r : Multiset ℂ) (μ z : ℂ) : ℂ :=
  -(1 - z) ^ (r.card + 1) + correction r μ * B r.card 2 z + tail r μ z

/-- The paper's exact second-order identity, for any complex nonzero mean. -/
theorem second_order (q : Multiset ℂ) (a μ : ℂ) (hm : 2 ≤ q.card)
    (hmean : q.sum = q.card * μ) (hμ : μ ≠ 0) :
    (q.card + 1) * (a * μ) *
      (∫ t in (0 : ℝ)..1, (q.map (fun v => 1 - a * t * v)).prod) =
      1 - correction (q.map (fun v => v - μ)) μ +
        epsilon (q.map (fun v => v - μ)) μ (a * μ) := by
  let r := q.map (fun v => v - μ)
  have hrc : r.card = q.card := Multiset.card_map _ _
  have hrs : r.sum = 0 := centered_sum q μ hmean
  rw [centered_integral q a μ hμ]
  have hs := Finset.sum_range_add_sum_Ico
    (fun k => coeff r μ k * H q.card k (a * μ)) (by omega : 3 ≤ q.card + 1)
  rw [← hs]
  rw [show 3 = 2 + 1 from rfl, Finset.sum_range_succ,
    show 2 = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, coeff_zero, one_mul, coeff_one r μ hrs, zero_mul,
    zero_add, add_zero]
  rw [coeff_two r μ (by omega) hrs hμ]
  dsimp [epsilon, tail]
  rw [hrc]
  simp only [H, B_zero]
  ring

/-- The mean squared norm of the centered family. -/
def variance (r : Multiset ℂ) : ℝ := (r.map (fun v => ‖v‖ ^ 2)).sum / r.card

/-- The paper's Γ, in real arithmetic. -/
def Gamma (r : Multiset ℂ) (μ : ℂ) : ℝ :=
  variance r / (((r.card : ℝ) - 1) * ‖μ‖ ^ 2)

theorem norm_kappa_le_variance (r : Multiset ℂ) : ‖kappa r‖ ≤ variance r := by
  have hs : ‖(r.map (fun v => v ^ 2)).sum‖ ≤ (r.map (fun v => ‖v‖ ^ 2)).sum := by
    induction r using Multiset.induction_on with
    | empty => simp
    | cons v r ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact (norm_add_le _ _).trans (by simpa [norm_pow] using add_le_add_left ih (‖v ^ 2‖))
  simpa [kappa, variance, norm_div] using
    div_le_div_of_nonneg_right hs (Nat.cast_nonneg r.card)

theorem norm_correction_le_Gamma (r : Multiset ℂ) (μ : ℂ) (hm : 2 ≤ r.card) :
    ‖correction r μ‖ ≤ Gamma r μ := by
  have hmR : (2 : ℝ) ≤ r.card := by exact_mod_cast hm
  have he : (r.card : ℂ) - 1 = (((r.card : ℝ) - 1 : ℝ) : ℂ) := by push_cast; rfl
  have hn : ‖(r.card : ℂ) - 1‖ = (r.card : ℝ) - 1 := by
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  simp only [correction, Gamma, norm_div, norm_mul, norm_pow, hn]
  exact div_le_div_of_nonneg_right (norm_kappa_le_variance r)
    (mul_nonneg (by linarith) (sq_nonneg _))

/-- The actual coefficient modulus, ready for an independent Fourier upper bound. -/
theorem norm_coeff (r : Multiset ℂ) (μ : ℂ) (k : ℕ) :
    ‖coeff r μ k‖ = ‖r.esymm k‖ / ((r.card.choose k : ℝ) * ‖μ‖ ^ k) := by
  simp [coeff, norm_pow]

/-- The finite triangle budget, using the actual elementary symmetric coefficients.
No endpoint H is replaced by 1. -/
def Efin (r : Multiset ℂ) (μ z : ℂ) : ℝ :=
  ‖1 - z‖ ^ (r.card + 1) + Gamma r μ * ‖B r.card 2 z‖ +
    ∑ k ∈ Finset.Ico 3 (r.card + 1),
      (‖r.esymm k‖ / ((r.card.choose k : ℝ) * ‖μ‖ ^ k)) * ‖H r.card k z‖

theorem norm_epsilon_le (r : Multiset ℂ) (μ z : ℂ) (hm : 2 ≤ r.card) :
    ‖epsilon r μ z‖ ≤ Efin r μ z := by
  have ht : ‖tail r μ z‖ ≤ ∑ k ∈ Finset.Ico 3 (r.card + 1),
      (‖r.esymm k‖ / ((r.card.choose k : ℝ) * ‖μ‖ ^ k)) * ‖H r.card k z‖ := by
    simpa only [tail, norm_mul, norm_coeff] using
      norm_sum_le (Finset.Ico 3 (r.card + 1)) (fun k => coeff r μ k * H r.card k z)
  have hc := mul_le_mul_of_nonneg_right (norm_correction_le_Gamma r μ hm)
    (norm_nonneg (B r.card 2 z))
  calc
    ‖epsilon r μ z‖ ≤ ‖-(1 - z) ^ (r.card + 1) + correction r μ * B r.card 2 z‖ +
        ‖tail r μ z‖ := norm_add_le _ _
    _ ≤ (‖-(1 - z) ^ (r.card + 1)‖ + ‖correction r μ * B r.card 2 z‖) +
        ‖tail r μ z‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ Efin r μ z := by
      simp only [norm_neg, norm_pow, norm_mul, Efin]
      linarith

/-- C-budget: the strict finite budget forces the normalized first-origin integral
outside the closed unit disk. The expansion is proved above, not a hypothesis. -/
theorem C_budget (q : Multiset ℂ) (a : ℝ) (μ : ℂ) (hm : 2 ≤ q.card)
    (ha : 0 ≤ a) (hmean : q.sum = q.card * μ) (hμ : μ ≠ 0)
    (hbudget : Efin (q.map (fun v => v - μ)) μ (a * μ) +
      Gamma (q.map (fun v => v - μ)) μ < 1 - a * ‖μ‖) :
    1 < ‖(q.card + 1 : ℂ) *
      (∫ t in (0 : ℝ)..1, (q.map (fun v => 1 - (a : ℂ) * t * v)).prod)‖ := by
  let r := q.map (fun v => v - μ)
  let J : ℂ := (q.card + 1 : ℂ) *
    (∫ t in (0 : ℝ)..1, (q.map (fun v => 1 - (a : ℂ) * t * v)).prod)
  have hm' : 2 ≤ r.card := by simpa [r] using hm
  have he := second_order q (a : ℂ) μ hm hmean hμ
  have hident : (1 : ℂ) = (a * μ) * J + correction r μ - epsilon r μ (a * μ) := by
    dsimp [J, r]
    linear_combination -he
  have hn : (1 : ℝ) ≤ ‖(a * μ) * J‖ + ‖correction r μ‖ + ‖epsilon r μ (a * μ)‖ := by
    calc (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
      _ = ‖(a * μ) * J + correction r μ - epsilon r μ (a * μ)‖ := congrArg norm hident
      _ ≤ ‖(a * μ) * J + correction r μ‖ + ‖epsilon r μ (a * μ)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (norm_add_le _ _) le_rfl
  have ha' : ‖(a : ℂ)‖ = a := by simp [Real.norm_eq_abs, abs_of_nonneg ha]
  simp only [norm_mul, ha'] at hn
  have hc := norm_correction_le_Gamma r μ hm'
  have heps := norm_epsilon_le r μ (a * μ) hm'
  change 1 < ‖J‖
  by_contra h
  have hJ : ‖J‖ ≤ 1 := le_of_not_gt h
  have hmul := mul_le_mul_of_nonneg_left hJ (mul_nonneg ha (norm_nonneg μ))
  change Efin r μ (a * μ) + Gamma r μ < 1 - a * ‖μ‖ at hbudget
  nlinarith

end Sendov.PaperCentered
