import Sendov.Analytic.PaperCenteredBound

/-! Edge cases and exact public interfaces; no sampled data substitutes for a theorem. -/
noncomputable section
open scoped BigOperators
open Sendov.PaperCentered Sendov.PaperCenteredBound
namespace Sendov.PaperCenteredBoundTests

-- The two actual mean-square definitions are identified, not independently assumed.
example (r : Multiset ℂ) : Sendov.PaperCoefficient.variance r =
    (r.map (fun z => ‖z‖ ^ 2)).sum / r.card := rfl
example (r : Multiset ℂ) : Sendov.PaperCoefficient.variance r = variance r :=
  variance_eq r

-- Piecewise formula: interior, top degree, and zero variance including m=k>0.
example (m k : ℕ) (v : ℝ) (hk : 0 < k) (hkm : k < m) :
    C m k v = Real.sqrt
      ((m : ℝ) ^ m / ((k : ℝ) ^ k * ((m - k : ℕ) : ℝ) ^ (m - k)) * v ^ k) :=
  C_interior m k v hk hkm
example (m : ℕ) (v : ℝ) : C m m v = Real.sqrt (v ^ m) := C_top m v
example (m k : ℕ) (hk : 0 < k) : C m k 0 = 0 := C_zero_variance m k hk
example : C 0 0 0 = 1 := by simp

-- Top degree uses sqrt(v^m), not a singular interior radius.
example (r : Multiset ℂ) (hr : r.sum = 0) (hm : 0 < r.card) :
    ‖r.esymm r.card‖ ≤ Real.sqrt (variance r ^ r.card) := by
  simpa using norm_esymm_le_C r hr r.card hm le_rfl

-- Actual zero variance kills both interior and top positive coefficients.
example (r : Multiset ℂ) (hr : r.sum = 0) (hv : variance r = 0)
    (μ : ℂ) (k : ℕ) (hk : 0 < k) (hkm : k ≤ r.card) : coeff r μ k = 0 := by
  have h := norm_coeff_le_C r hr μ k hk hkm
  rw [hv, C_zero_variance _ _ hk, zero_div] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

-- Explicit coefficient interface with actual deviations and actual mean square.
example (q : Multiset ℂ) (μ : ℂ) (hmean : q.sum = q.card * μ)
    (k : ℕ) (hk : 0 < k) (hkm : k ≤ q.card) :
    ‖coeff (q.map (fun z => z - μ)) μ k‖ ≤
      C q.card k (((q.map (fun z => ‖z - μ‖ ^ 2)).sum) / q.card) /
        ((q.card.choose k : ℝ) * ‖μ‖ ^ k) := by
  simpa [variance, Multiset.map_map, Function.comp_def] using
    norm_centered_coeff_le_C q μ hmean k hk hkm

-- All H endpoints: zero scale and the exact top endpoint for arbitrary complex scale.
example (m k : ℕ) : H m k 0 = 0 := H_at_zero m k
example (m : ℕ) (z : ℂ) : H m m z = z ^ (m + 1) := H_top m z
example (m : ℕ) (z : ℂ) : H m 0 z = 1 - (1 - z) ^ (m + 1) := by simp [H]

-- m=2 has no tail; m=3 retains exactly the top endpoint, not a replacement by 1.
example (r : Multiset ℂ) (hm : r.card = 2) (μ z : ℂ) :
    majorant_Efin r μ z = ‖1 - z‖ ^ 3 + Gamma r μ * ‖B 2 2 z‖ := by
  simp [majorant_Efin, hm]
example (r : Multiset ℂ) (hm : r.card = 3) (μ z : ℂ) :
    majorant_Efin r μ z = ‖1 - z‖ ^ 4 + Gamma r μ * ‖B 3 2 z‖ +
      Real.sqrt (variance r ^ 3) / ‖μ‖ ^ 3 * ‖z ^ 4‖ := by
  norm_num [majorant_Efin, hm, Finset.sum_Ico_succ_top, H_top, norm_pow]

-- A genuinely nonreal mean, with a nontrivial arbitrary complex family.
def q3 (z : ℂ) : Multiset ℂ := (Complex.I + z) ::ₘ (Complex.I - z) ::ₘ {Complex.I}
lemma q3_mean (z : ℂ) : (q3 z).sum = (q3 z).card * Complex.I := by
  simp [q3]
  ring
example : Complex.I.im ≠ 0 := by simp
example (z : ℂ) :
    ‖coeff ((q3 z).map (fun w => w - Complex.I)) Complex.I 2‖ ≤
      C 3 2 (variance ((q3 z).map (fun w => w - Complex.I))) / 3 := by
  simpa [q3] using norm_centered_coeff_le_C (q3 z) Complex.I (q3_mean z) 2
    (by decide) (by simp [q3])
example (z : ℂ) :
    ‖coeff ((q3 z).map (fun w => w - Complex.I)) Complex.I 3‖ ≤
      Real.sqrt (variance ((q3 z).map (fun w => w - Complex.I)) ^ 3) := by
  simpa [q3] using norm_centered_coeff_le_C (q3 z) Complex.I (q3_mean z) 3
    (by decide) (by simp [q3])

-- Nonreal mean is accepted by the epsilon and integral-budget interfaces too.
example (z a : ℂ) :
    ‖epsilon ((q3 z).map (fun w => w - Complex.I)) Complex.I (a * Complex.I)‖ ≤
      majorant_Efin ((q3 z).map (fun w => w - Complex.I)) Complex.I (a * Complex.I) :=
  norm_epsilon_le_majorant_Efin _ (centered_sum _ _ (q3_mean z)) _ _ (by simp [q3])
example (z : ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hb : majorant_Efin ((q3 z).map (fun w => w - Complex.I)) Complex.I (a * Complex.I) +
      Gamma ((q3 z).map (fun w => w - Complex.I)) Complex.I < 1 - a * ‖Complex.I‖) :
    1 < ‖((q3 z).card + 1 : ℂ) *
      (∫ t in (0 : ℝ)..1, ((q3 z).map (fun w => 1 - (a : ℂ) * t * w)).prod)‖ :=
  Sendov.PaperCenteredBound.C_budget (q3 z) a Complex.I (by simp [q3]) ha
    (q3_mean z) Complex.I_ne_zero hb

-- Exact top endpoint suppression on both majorant and signed coefficients.
example (r : Multiset ℂ) (a μ : ℂ) (hμ : μ ≠ 0) :
    C r.card r.card (variance r) / ((r.card.choose r.card : ℝ) * ‖μ‖ ^ r.card) *
      ‖H r.card r.card (a * μ)‖ =
      Real.sqrt (variance r ^ r.card) * ‖a‖ ^ (r.card + 1) * ‖μ‖ :=
  majorant_top_suppression r a μ hμ
example (r : Multiset ℂ) (a : ℂ) :
    coeff r Complex.I r.card * H r.card r.card (a * Complex.I) =
      (-1) ^ r.card * r.prod * a ^ (r.card + 1) * Complex.I :=
  coeff_top_suppression r a Complex.I Complex.I_ne_zero

end Sendov.PaperCenteredBoundTests

#print axioms Sendov.PaperCenteredBound.norm_esymm_le_C
#print axioms Sendov.PaperCenteredBound.norm_coeff_le_C
#print axioms Sendov.PaperCenteredBound.norm_centered_coeff_le_C
#print axioms Sendov.PaperCenteredBound.norm_epsilon_le_majorant_Efin
#print axioms Sendov.PaperCenteredBound.C_budget
#print axioms Sendov.PaperCenteredBound.majorant_top_suppression
#print axioms Sendov.PaperCenteredBound.coeff_top_suppression
