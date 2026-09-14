import Sendov.Analytic.PaperCentered
import Sendov.Analytic.PaperCoefficient

/-!
# The paper's square-root centered finite budget

Assembles the optimized coefficient estimate and the exact centered expansion.
The variance is always that of the actual centered multiset. Every complex
endpoint H is retained, including the top degree. This is a sufficient-budget
implication, not a claim that the budget is positive on any geometric domain.
-/

noncomputable section
open scoped BigOperators
namespace Sendov.PaperCenteredBound
open PaperCentered

/-- The two component modules use definitionally identical actual variances. -/
theorem variance_eq (r : Multiset ℂ) :
    PaperCoefficient.variance r = PaperCentered.variance r := rfl

/-- REPORT §3.2, with an explicit top-degree branch. Only positive degrees
through m are used; outside that range the value is zero (except m=k=0). -/
def C (m k : ℕ) (v : ℝ) : ℝ :=
  if k = m then Real.sqrt (v ^ m)
  else if 0 < k ∧ k < m then
    Real.sqrt ((m : ℝ) ^ m / ((k : ℝ) ^ k * ((m - k : ℕ) : ℝ) ^ (m - k)) * v ^ k)
  else 0

@[simp] theorem C_top (m : ℕ) (v : ℝ) : C m m v = Real.sqrt (v ^ m) := by
  simp [C]

theorem C_interior (m k : ℕ) (v : ℝ) (hk : 0 < k) (hkm : k < m) :
    C m k v = Real.sqrt
      ((m : ℝ) ^ m / ((k : ℝ) ^ k * ((m - k : ℕ) : ℝ) ^ (m - k)) * v ^ k) := by
  simp [C, hkm.ne, hk, hkm]

theorem C_nonneg (m k : ℕ) (v : ℝ) : 0 ≤ C m k v := by
  unfold C
  split_ifs <;> positivity

/-- Zero variance is covered without choosing a singular optimizing radius. -/
@[simp] theorem C_zero_variance (m k : ℕ) (hk : 0 < k) : C m k 0 = 0 := by
  by_cases hkm : k = m
  · subst m
    simp [C, zero_pow hk.ne']
  · simp [C, hkm, zero_pow hk.ne']

/-- The exact paper square-root bound, including k=m and zero variance. -/
theorem norm_esymm_le_C (r : Multiset ℂ) (hr : r.sum = 0)
    (k : ℕ) (hk : 0 < k) (hkm : k ≤ r.card) :
    ‖r.esymm k‖ ≤ C r.card k (variance r) := by
  by_cases htop : k = r.card
  · subst k
    rw [C_top]
    have h := PaperCoefficient.norm_esymm_card_sq_le r
    rw [variance_eq] at h
    exact (Real.le_sqrt (norm_nonneg _) ((sq_nonneg _).trans h)).2 h
  · rw [C_interior _ _ _ hk (lt_of_le_of_ne hkm htop)]
    have h := PaperCoefficient.norm_esymm_sq_le_optimized r hr k hk
      (lt_of_le_of_ne hkm htop)
    rw [variance_eq] at h
    exact (Real.le_sqrt (norm_nonneg _) ((sq_nonneg _).trans h)).2 h

/-- Normalized actual coefficient interface. No real-mean assumption is made;
the inequality even holds at zero mean under Lean's total division convention. -/
theorem norm_coeff_le_C (r : Multiset ℂ) (hr : r.sum = 0)
    (μ : ℂ) (k : ℕ) (hk : 0 < k) (hkm : k ≤ r.card) :
    ‖coeff r μ k‖ ≤ C r.card k (variance r) / ((r.card.choose k : ℝ) * ‖μ‖ ^ k) := by
  rw [norm_coeff]
  exact div_le_div_of_nonneg_right (norm_esymm_le_C r hr k hk hkm) (by positivity)

/-- The coefficient interface on the actual deviations from a complex mean. -/
theorem norm_centered_coeff_le_C (q : Multiset ℂ) (μ : ℂ)
    (hmean : q.sum = q.card * μ) (k : ℕ) (hk : 0 < k) (hkm : k ≤ q.card) :
    ‖coeff (q.map (fun v => v - μ)) μ k‖ ≤
      C q.card k (variance (q.map (fun v => v - μ))) /
        ((q.card.choose k : ℝ) * ‖μ‖ ^ k) := by
  simpa only [Multiset.card_map] using
    norm_coeff_le_C (q.map (fun v => v - μ)) (centered_sum q μ hmean) μ k hk
      (by simpa only [Multiset.card_map] using hkm)

/-- REPORT §3.3 E_fin: the exact square-root majorant, not the actual-coefficient
triangle bound. All finite endpoints remain inside complex norms. -/
def majorant_Efin (r : Multiset ℂ) (μ z : ℂ) : ℝ :=
  ‖1 - z‖ ^ (r.card + 1) + Gamma r μ * ‖B r.card 2 z‖ +
    ∑ k ∈ Finset.Ico 3 (r.card + 1),
      (C r.card k (variance r) / ((r.card.choose k : ℝ) * ‖μ‖ ^ k)) * ‖H r.card k z‖

/-- Comparison with the accepted actual-coefficient finite budget. -/
theorem Efin_le_majorant_Efin (r : Multiset ℂ) (hr : r.sum = 0) (μ z : ℂ) :
    Efin r μ z ≤ majorant_Efin r μ z := by
  unfold Efin majorant_Efin
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro k hk
  obtain ⟨hk₀, hk₁⟩ := Finset.mem_Ico.mp hk
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact div_le_div_of_nonneg_right (norm_esymm_le_C r hr k (by omega) (by omega))
    (by positivity)

/-- The actual finite epsilon obeys the paper's square-root majorant. -/
theorem norm_epsilon_le_majorant_Efin (r : Multiset ℂ) (hr : r.sum = 0)
    (μ z : ℂ) (hm : 2 ≤ r.card) :
    ‖epsilon r μ z‖ ≤ majorant_Efin r μ z :=
  (norm_epsilon_le r μ z hm).trans (Efin_le_majorant_Efin r hr μ z)

/-- C-budget with the actual centered variance, valid for any nonzero complex
mean. The strict scalar budget is an explicit hypothesis, never a conclusion. -/
theorem C_budget (q : Multiset ℂ) (a : ℝ) (μ : ℂ) (hm : 2 ≤ q.card)
    (ha : 0 ≤ a) (hmean : q.sum = q.card * μ) (hμ : μ ≠ 0)
    (hbudget : majorant_Efin (q.map (fun v => v - μ)) μ (a * μ) +
      Gamma (q.map (fun v => v - μ)) μ < 1 - a * ‖μ‖) :
    1 < ‖(q.card + 1 : ℂ) *
      (∫ t in (0 : ℝ)..1, (q.map (fun v => 1 - (a : ℂ) * t * v)).prod)‖ := by
  apply PaperCentered.C_budget q a μ hm ha hmean hμ
  exact lt_of_le_of_lt
    (add_le_add (Efin_le_majorant_Efin _ (centered_sum q μ hmean) μ (a * μ)) le_rfl)
    hbudget

/-- At the top endpoint the apparent inverse power of the mean cancels exactly.
The scale a can itself be complex; no positivity interpretation of H is used. -/
theorem majorant_top_suppression (r : Multiset ℂ) (a μ : ℂ) (hμ : μ ≠ 0) :
    (C r.card r.card (variance r) / ((r.card.choose r.card : ℝ) * ‖μ‖ ^ r.card)) *
      ‖H r.card r.card (a * μ)‖ =
    Real.sqrt (variance r ^ r.card) * ‖a‖ ^ (r.card + 1) * ‖μ‖ := by
  have hn : ‖μ‖ ≠ 0 := norm_ne_zero_iff.mpr hμ
  rw [C_top, H_top, norm_pow, norm_mul, mul_pow, Nat.choose_self]
  simp only [Nat.cast_one, one_mul]
  rw [pow_succ ‖μ‖]
  field_simp

/-- The same cancellation for the signed actual top coefficient. -/
theorem coeff_top_suppression (r : Multiset ℂ) (a μ : ℂ) (hμ : μ ≠ 0) :
    coeff r μ r.card * H r.card r.card (a * μ) =
      (-1) ^ r.card * r.prod * a ^ (r.card + 1) * μ := by
  rw [coeff, H_top, Nat.choose_self]
  simp only [Nat.cast_one, one_mul]
  have he : r.esymm r.card = r.prod := by simp [Multiset.esymm]
  rw [he, mul_pow, pow_succ μ]
  field_simp

end Sendov.PaperCenteredBound
