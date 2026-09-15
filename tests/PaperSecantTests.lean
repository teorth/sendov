import Sendov.Analytic.PaperSecant

/-! Regression tests for round6 §§2–3. Numerical tests are kernel-checked
rational arithmetic, not floating-point checks or claims of universal positivity. -/
namespace Sendov.PaperSecant.Tests
open MeasureTheory

-- Odd and even degrees use the same exact finite endpoint theorem.
example {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    R 7 a 1 = ((a + (1 - a ^ 2)) ^ 8 - a ^ 8) / (8 * (1 - a ^ 2)) := by
  have h := R_one (m := 7) ha ha1
  norm_num [U1] at h ⊢
  exact h

example {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (∫ t in (0 : ℝ)..1, (a ^ 2 + (1 - a ^ 2) * t) ^ ((7 : ℝ) / 2)) =
      2 * (1 - a ^ 9) / (9 * (1 - a ^ 2)) := by
  have h := integral_chord (m := 7) ha ha1
  norm_num [U0] at h ⊢
  exact h

example {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    R 8 a (a / 2) ≤ U0 8 a - (8 : ℝ) / 12 * a ^ 6 * (1 - a ^ 2) ^ 2 := by
  simpa [V0] using (R_half_le_V0 (m := 8) (by norm_num) ha ha1)

example {m : ℕ} {a x : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hr : PaperPolar.RawPolar m a x) :
    0 < V0 m a ∧ V0 m a < 1 ∧ 1 ≤ U1 m a ∧ a / 2 < S m a ∧ S m a ≤ x := by
  have hu := one_le_U1 ha ha1 hx0 hx1 hr
  exact ⟨V0_pos (by omega) ha ha1, V0_lt_one (by omega) ha ha1, hu,
    (S_bounds (by omega) ha ha1 hu).1, raw_implies_secant hm ha ha1 hx0 hx1 hr⟩

example {m : ℕ} {a x : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hu : U1 m a < 1) : ¬ PaperPolar.RawPolar m a x := by
  intro hr
  exact (not_le_of_gt hu) (one_le_U1 ha ha1 hx0 hx1 hr)

-- Direct universal interface, with the actual origin integral exposed.
example {m : ℕ} {a : ℝ} (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hg : 0 < Fsec m a) : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → PaperPolar.RawPolar m a x →
      PaperTaylor.beta a x 1 ^ ((m : ℝ) / 2) + (m : ℝ) * a ^ 2 *
        (∫ t in (0 : ℝ)..1, t * PaperTaylor.beta a x t ^ (((m : ℝ) - 1) / 2)) <
          1 - (m : ℝ) * a / ((m : ℝ) + 1) := by
  intro x hx0 hx1 hr
  exact gate_implies_D hm ha ha1 hx0 hx1 hr hg

-- Report §3.1: three positive diagnostics and the failure retained verbatim.
theorem gate_7_four_fifths : 0 < Fsec 7 (4 / 5) := by
  norm_num [Fsec, B, Wsec, S, V0, U0, U1, PaperTaylor.beta,
    PaperTaylor.defect, PaperTaylor.chord]

theorem gate_8_nine_tenths : 0 < Fsec 8 (9 / 10) := by
  norm_num [Fsec, B, Wsec, S, V0, U0, U1, PaperTaylor.beta,
    PaperTaylor.defect, PaperTaylor.chord]

theorem gate_10_nine_tenths : 0 < Fsec 10 (9 / 10) := by
  norm_num [Fsec, B, Wsec, S, V0, U0, U1, PaperTaylor.beta,
    PaperTaylor.defect, PaperTaylor.chord]

theorem gate_16_nine_tenths_negative : Fsec 16 (9 / 10) < 0 := by
  norm_num [Fsec, B, Wsec, S, V0, U0, U1, PaperTaylor.beta,
    PaperTaylor.defect, PaperTaylor.chord]

-- The rejected linear simplification must not creep into the secant API.
theorem linear_simplification_fails :
    S 10 (49 / 50) - (1 - (10 - 4 : ℝ) * (1 - 49 / 50) / 6) =
      -(580765093537365039347573397 : ℝ) / 317624371446602655376674688925300 := by
  norm_num [S, V0, U0, U1]

-- A negative gate is compatible with raw feasibility, not a counterexample to D.
theorem raw_feasible_at_negative_gate : PaperPolar.RawPolar 16 (9 / 10) 1 := by
  rw [PaperPolar.rawPolar_iff]
  change 1 ≤ R 16 (9 / 10) 1
  rw [R_one (by norm_num) (by norm_num)]
  norm_num [U1]

-- The odd-degree positive diagnostic closes D for every feasible mean.
example {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hr : PaperPolar.RawPolar 7 (4 / 5) x) :
    PaperTaylor.budget 7 (4 / 5) x < B 7 (4 / 5) := by
  exact gate_implies_D (by norm_num) (by norm_num) (by norm_num)
    hx0 hx1 hr gate_7_four_fifths

#print axioms R_one
#print axioms integral_chord
#print axioms curvature_pointwise
#print axioms R_half_le_V0
#print axioms V0_pos
#print axioms V0_le_U0
#print axioms V0_lt_one
#print axioms U0_lt_one
#print axioms R_mono
#print axioms one_le_U1
#print axioms R_secant
#print axioms S_bounds
#print axioms S_eq_one_sub
#print axioms plain_secant_le_S
#print axioms gate_denominators_pos
#print axioms raw_implies_secant
#print axioms budget_antitone
#print axioms endpoint_pow_le
#print axioms budget_S_le_Wsec
#print axioms gate_implies_D
#print axioms gate_7_four_fifths
#print axioms gate_8_nine_tenths
#print axioms gate_10_nine_tenths
#print axioms gate_16_nine_tenths_negative

end Sendov.PaperSecant.Tests
