import Sendov.Analytic.PaperLegacyExact
import Sendov.Analytic.PaperLegacyHundred
import Sendov.Analytic.PaperNearMargins

/-!
# DI08–DI10: original full-polar and direct-budget certificates

Sources: first-origin-uniform/{certificates.json,legacy_RESULT.json},
REPORT.md §2.1–2.2, legacy_RESULT.md §19–25.
The binary64 diagnostic's serialized decimal is retained exactly as a rational;
no approximate equality or assumption that it is a feasible root is used.

The polar integrals retain the original exact values. The direct inequalities
use structural integral estimates, not the original Simpson implementation or
its displayed approximate gaps. In particular the legacy 3h/5 margin consumes
PaperTaylor.budget_le, not the weaker uniform h/3 theorem.
-/
namespace Sendov.PaperLegacyCertificates
open MeasureTheory PaperLegacy
open scoped BigOperators

noncomputable def h : ℝ := 1 / 1000000000
noncomputable def a : ℝ := 999999999 / 1000000000
noncomputable def rejectedX : ℝ := 499999993298327 / 500000000000000
noncomputable def upperX : ℝ := a + 100 * h ^ 2
noncomputable def legacyX : ℝ := a + 3 * h ^ 2

theorem exact_source_parameters : a = 1 - h ∧
    rejectedX = 0.999999986596654 ∧
    upperX = 9999999990000001 / 10000000000000000 ∧
    legacyX = 999999999000000003 / 1000000000000000000 := by
  norm_num [a, h, rejectedX, upperX, legacyX]

/-- Pair indexing has the original total multiplicities, not half the degree. -/
theorem pair_cardinalities : Fintype.card (Fin 5 × Fin 2) = 10 ∧
    Fintype.card (Fin 10 × Fin 2) = 20 ∧ Fintype.card (Fin 50 × Fin 2) = 100 := by
  norm_num

lemma rejected_R : R 5 a rejectedX = rejectedValue := rejected_integral
lemma lower_R : R 5 a a = lowerValue := lower_integral
lemma upper_R : R 5 a upperX = upperValue := by
  convert upper_integral using 1 <;> norm_num [a, h, upperX]
lemma legacy_R : R 5 a legacyX = legacyValue := by
  convert legacy_integral using 1 <;> norm_num [a, h, legacyX]

/-- DI08: the exact decimal rejected by the certificate fails FULL complex polar. -/
theorem rejected_full_polar : ‖K 5 a rejectedX‖ < 1 := by
  rw [norm_K_eq (by norm_num [rejectedX]) 5 a (by rw [rejected_R]; norm_num [rejectedValue]),
    rejected_R]
  norm_num [rejectedValue]

theorem rejected_not_raw : ¬ PaperPolar.RawPolar 10 a rejectedX := by
  rw [show 10 = 2 * 5 by rfl, raw_even, rejected_R]
  norm_num [rejectedValue]

/-- DI08: strict endpoints for the true raw threshold. -/
theorem raw_threshold_bracket :
    (∫ t in (0 : ℝ)..1, P a a t ^ ((10 : ℝ) / 2)) < 1 ∧
    1 < ∫ t in (0 : ℝ)..1, P a upperX t ^ ((10 : ℝ) / 2) := by
  norm_num only [show (10 : ℝ) / 2 = 5 by norm_num, Real.rpow_ofNat]
  change R 5 a a < 1 ∧ 1 < R 5 a upperX
  rw [lower_R, upper_R]
  norm_num [lowerValue, upperValue]

/-- The same bracket is a FULL complex K bracket for five unit-circle pairs. -/
theorem full_threshold_bracket : ‖K 5 a a‖ < 1 ∧ 1 < ‖K 5 a upperX‖ := by
  rw [norm_K_eq (by norm_num [a]) 5 a (by rw [lower_R]; norm_num [lowerValue]),
    norm_K_eq (by norm_num [a, h, upperX]) 5 a (by rw [upper_R]; norm_num [upperValue]),
    lower_R, upper_R]
  norm_num [lowerValue, upperValue]

/-- DI08 includes ALL raw-feasible x, not only the replacement witness. -/
theorem all_feasible_D (x : ℝ) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : PaperPolar.RawPolar 10 a x) :
    PaperTaylor.budget 10 a x < 1 - 10 * a / 11 := by
  have hg := PaperNearMargins.near_endpoint_one_fiftieth (m := 10)
    (by norm_num) (by norm_num [a]) (by norm_num [a]) hx0 hx1 hraw (by norm_num [a])
  norm_num at hg
  have hh : 0 < 1 - a := by norm_num [a]
  linarith

/-- DI09: the original a+3h² witness, not the later a+100h² endpoint. -/
theorem legacy_full_polar : 1 < ‖K 5 a legacyX‖ := by
  rw [norm_K_eq (by norm_num [a, h, legacyX]) 5 a
    (by rw [legacy_R]; norm_num [legacyValue]), legacy_R]
  norm_num [legacyValue]

/-- DI09's stronger finite margin is for the actual T integral. -/
theorem legacy_three_fifths :
    (3 / 5 : ℝ) * h < 1 - 10 * a / 11 - PaperTaylor.budget 10 a legacyX := by
  have ht := PaperTaylor.budget_le (m := 10) (a := a) (x := legacyX)
    (by norm_num) (by norm_num [a]) (by norm_num [a])
    (by norm_num [legacyX, a, h]) (by norm_num [PaperTaylor.chord, legacyX, a, h])
  norm_num only [show (10 : ℝ) / 2 = 5 by norm_num, Real.rpow_ofNat] at ht
  have hc : 1 / ((10 : ℝ) + 1) + PaperTaylor.beta a legacyX 1 ^ (5 : ℕ) +
      PaperTaylor.defect a legacyX / (a * (10 - 2)) +
      12 * 10 * a ^ 2 * PaperTaylor.defect a legacyX ^ 2 /
        (PaperTaylor.chord a legacyX ^ 4 * (10 + 1) * (10 + 3)) <
      1 - 10 * a / 11 - (3 / 5) * h := by
    norm_num [PaperTaylor.beta, PaperTaylor.defect, PaperTaylor.chord, legacyX, a, h]
  linarith

/-- DI10: left chord on [0,1/2], bounded right tail; direct T, not Cbudget. -/
theorem twenty_D : PaperTaylor.budget 20 (9 / 10) (83 / 100) <
    1 - 20 * (9 / 10) / 21 := by
  have ht := budget_split_le (m := 20) (a := 9 / 10) (x := 83 / 100)
    (s := 1 / 2) (c := 27 / 25) (r := 1 / 2) (n := 9)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro t ht
      have := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
      dsimp [PaperTaylor.beta]
      nlinarith)
    (by
      intro t ht
      have := mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)
      dsimp [PaperTaylor.beta]
      nlinarith)
  norm_num only [show (20 : ℝ) / 2 = 10 by norm_num, Real.rpow_ofNat] at ht
  apply ht.trans_lt
  norm_num [PaperTaylor.beta]

/-- DI10: a different finite split at 1/4 handles m=100 without Simpson. -/
theorem hundred_D : PaperTaylor.budget 100 (99 / 100) (22 / 25) <
    1 - 100 * (99 / 100) / 101 := by
  have ht := budget_split_le (m := 100) (a := 99 / 100) (x := 22 / 25)
    (s := 1 / 4) (c := 149 / 100) (r := 2 / 3) (n := 49)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro t ht
      have := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
      dsimp [PaperTaylor.beta]
      nlinarith)
    (by
      intro t ht
      have := mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)
      dsimp [PaperTaylor.beta]
      nlinarith)
  norm_num only [show (100 : ℝ) / 2 = 50 by norm_num, Real.rpow_ofNat] at ht
  apply ht.trans_lt
  norm_num [PaperTaylor.beta]

theorem twenty_full_polar : 1 < ‖K 10 (9 / 10) (83 / 100)‖ := by
  rw [norm_K_eq (by norm_num) 10 (9 / 10)
    (by rw [twenty_integral]; norm_num [twentyValue]), twenty_integral]
  norm_num [twentyValue]

theorem hundred_full_polar : 1 < ‖K 50 (99 / 100) (22 / 25)‖ := by
  rw [norm_K_eq (by norm_num) 50 (99 / 100)
    (by rw [hundred_integral]; norm_num [hundredValue]), hundred_integral]
  norm_num [hundredValue]

/-- Literal complex-integral form and unit-circle hypothesis for the legacy point. -/
theorem legacy_complete :
    (∀ j : Fin 5 × Fin 2, ‖q 5 legacyX j‖ = 1) ∧
    1 < ‖∫ t in (0 : ℝ)..1, ∏ j : Fin 5 × Fin 2,
      ((a : ℂ) + ((1 - a ^ 2) * t : ℝ) * q 5 legacyX j)‖ ∧
    (3 / 5 : ℝ) * (1 - a) < 1 - 10 * a / 11 - PaperTaylor.budget 10 a legacyX := by
  refine ⟨norm_q (by norm_num [a, h, legacyX]), legacy_full_polar, ?_⟩
  rw [show 1 - a = h by norm_num [a, h]]
  exact legacy_three_fifths

theorem twenty_complete :
    (∀ j : Fin 10 × Fin 2, ‖q 10 (83 / 100) j‖ = 1) ∧
    1 < ‖K 10 (9 / 10) (83 / 100)‖ ∧
    PaperTaylor.budget 20 (9 / 10) (83 / 100) < 1 - 20 * (9 / 10) / 21 :=
  ⟨norm_q (by norm_num), twenty_full_polar, twenty_D⟩

theorem hundred_complete :
    (∀ j : Fin 50 × Fin 2, ‖q 50 (22 / 25) j‖ = 1) ∧
    1 < ‖K 50 (99 / 100) (22 / 25)‖ ∧
    PaperTaylor.budget 100 (99 / 100) (22 / 25) < 1 - 100 * (99 / 100) / 101 :=
  ⟨norm_q (by norm_num), hundred_full_polar, hundred_D⟩

#print axioms exact_source_parameters
#print axioms rejected_full_polar
#print axioms raw_threshold_bracket
#print axioms full_threshold_bracket
#print axioms all_feasible_D
#print axioms legacy_complete
#print axioms twenty_complete
#print axioms hundred_complete

-- Check transitive proof VALUES: an imported centered theorem cannot silently
-- replace the actual T estimates, nor h/3 replace the finite legacy margin.
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    (`Sendov.PaperLegacyCertificates.legacy_three_fifths,
      #[`Sendov.PaperTaylor.budget_le]),
    (`Sendov.PaperLegacyCertificates.twenty_D,
      #[`Sendov.PaperLegacy.budget_split_le]),
    (`Sendov.PaperLegacyCertificates.hundred_D,
      #[`Sendov.PaperLegacy.budget_split_le]),
    (`Sendov.PaperLegacyCertificates.rejected_full_polar,
      #[`Sendov.PaperLegacy.K_eq_R, `Sendov.PaperLegacy.rejected_integral]),
    (`Sendov.PaperLegacyCertificates.full_threshold_bracket,
      #[`Sendov.PaperLegacy.K_eq_R, `Sendov.PaperLegacy.lower_integral,
        `Sendov.PaperLegacy.upper_integral]),
    (`Sendov.PaperLegacyCertificates.legacy_full_polar,
      #[`Sendov.PaperLegacy.K_eq_R, `Sendov.PaperLegacy.legacy_integral]),
    (`Sendov.PaperLegacyCertificates.twenty_full_polar,
      #[`Sendov.PaperLegacy.K_eq_R, `Sendov.PaperLegacy.twenty_integral]),
    (`Sendov.PaperLegacyCertificates.hundred_full_polar,
      #[`Sendov.PaperLegacy.K_eq_R, `Sendov.PaperLegacy.hundred_integral])]
  for (root, required) in roots do
    let mut pending := [root]
    let mut visited : Std.HashSet Name := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      unless visited.contains name do
        visited := visited.insert name
        let some ci := env.find? name | throwError "missing declaration {name}"
        if let some value := ci.value? (allowOpaque := true) then
          for used in value.getUsedConstants do pending := used :: pending
    for target in required do
      unless visited.contains target do
        throwError "legacy proof missing required dependency {root} -> {target}"
    for name in visited.toList do
      for banned in #[`Sendov.PaperCentered, `Sendov.PaperCenteredBound,
          `Sendov.PaperUniform, `Sendov.PaperNearMargins, `Sendov.PaperNearClosure] do
        if banned.isPrefixOf name then
          throwError "legacy proof uses a forbidden substitute: {root} -> {name}"
    logInfo m!"LEGACY_CERTIFICATE_PROOF_CLOSURE_OK {root}"

end Sendov.PaperLegacyCertificates
