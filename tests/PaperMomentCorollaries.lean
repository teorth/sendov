import Sendov.Analytic.PaperMomentCorollaries

/-! Compiled signatures and regression contracts for the seven paper families. -/
noncomputable section
open Sendov Sendov.PaperPolar Sendov.PaperCentered Sendov.PaperMomentCorollaries

#check Sendov.PaperMomentCorollaries.FO05
#check Sendov.PaperMomentCorollaries.FO06_six
#check Sendov.PaperMomentCorollaries.FO06_five
#check Sendov.PaperMomentCorollaries.FO06
#check Sendov.PaperMomentCorollaries.PO01
#check Sendov.PaperMomentCorollaries.PO07
#check Sendov.PaperMomentCorollaries.PO09
#check Sendov.PaperMomentCorollaries.EX01
#check Sendov.PaperMomentCorollaries.EX02

#print axioms Sendov.PaperMomentCorollaries.FO05
#print axioms Sendov.PaperMomentCorollaries.FO06_six
#print axioms Sendov.PaperMomentCorollaries.FO06_five
#print axioms Sendov.PaperMomentCorollaries.FO06
#print axioms Sendov.PaperMomentCorollaries.PO01
#print axioms Sendov.PaperMomentCorollaries.PO07
#print axioms Sendov.PaperMomentCorollaries.PO09
#print axioms Sendov.PaperMomentCorollaries.EX01
#print axioms Sendov.PaperMomentCorollaries.EX02

namespace Sendov.PaperMomentCorollariesTests

/-- The disk bound is closed: unit points and s=1 are admitted. -/
theorem unit_mean : mean ({(1 : ℂ)} : Multiset ℂ) = 1 := by simp [mean]
theorem unit_secondMoment : secondMoment ({(1 : ℂ)} : Multiset ℂ) = 1 := by
  simp [secondMoment]

/-- The variance is the actual centered moment, not a scalar supplied in a premise. -/
theorem actual_variance (q : Multiset ℂ) (hm : 0 < q.card) (hq : ∀ z ∈ q, ‖z‖ ≤ 1) :
    variance (q.map (fun z => z - q.sum / (q.card : ℂ))) =
      (q.map (fun z => ‖z‖ ^ 2)).sum / (q.card : ℝ) - ‖q.sum / (q.card : ℂ)‖ ^ 2 :=
  (FO05 q hm hq).2.2.1

/-- Both deficits use precisely the raw natural degree exponent m/2. -/
theorem raw_deficits {a x : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hx0 : -1 ≤ x) (hx : x ≤ (1 + a) / 2) :
    (∫ t in (0 : ℝ)..1, Ppolar a x t ^ ((5 : ℕ) / (2 : ℝ))) ≤
      1 - 23 * (1 - a) ^ 2 / 42 ∧
    (∫ t in (0 : ℝ)..1, Ppolar a x t ^ ((6 : ℕ) / (2 : ℝ))) ≤
      1 - 23 * (1 - a) ^ 2 / 35 := by
  constructor
  · exact FO06_five ha.le ha1.le hx0 hx
  · norm_num [Real.rpow_natCast]
    exact FO06_six ha.le ha1.le hx0 hx

theorem degree_five_mean {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x)
    (hr : RawPolar 5 a x) : (1 + a) / 2 < x := FO06 (Or.inl rfl) ha ha1 hx0 hr

theorem degree_six_mean {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x)
    (hr : RawPolar 6 a x) : (1 + a) / 2 < x := FO06 (Or.inr rfl) ha ha1 hx0 hr

/-- Regression below seven: no invocation of the restricted geometry API. -/
theorem degree_one_geometry {a x : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hr : RawPolar 1 a x) :
    a / 2 < x ∧ 0 < c a x ∧ c a x < 1 ∧ 0 < b a x ∧ b a x < 1 :=
  PO01 (by norm_num) ha ha1 hx0 hx1 hr

/-- PO07 is uniform in natural degree, and retains the full quadratic y factor. -/
theorem y_chain {m : ℕ} {a x : ℝ} (hm : 1 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hr : RawPolar m a x) :
    1 - (1 + c a x) / 2 ≤ alpha m a * ((1 + c a x) / 2) ^ 2 / 6 ∧
    alpha m a * ((1 + c a x) / 2) ^ 2 / 6 ≤
      lambda m a * ((1 + c a x) / 2) ^ 2 / 6 ∧
    1 - x ≤ lambda m a / (6 * a) := PO07 hm ha ha1 hx0 hx1 hr

/-- Strictness is retained, not weakened to a non-strict root comparison. -/
theorem strict_gaussian {m : ℕ} {a x : ℝ} (hm : 1 ≤ m)
    (ha : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hr : RawPolar m a x) :
    (Real.sqrt (36 + 24 * alpha m a) - 6) / (2 * alpha m a) <
      (alpha m a + 6) / (2 * (alpha m a + 3)) := (PO09 hm ha ha1 hx0 hx1 hr).1

/-- EX01 accepts the actual arithmetic mean without an independent mean assumption. -/
theorem actual_ratio (q : Multiset ℂ) {a : ℝ} (hm : 7 ≤ q.card)
    (ha : 0 < a) (ha1 : a < 1) (hq : ∀ z ∈ q, ‖z‖ ≤ 1)
    (hx0 : -1 ≤ (mean q).re) (hx1 : (mean q).re ≤ 1)
    (hr : RawPolar q.card a (mean q).re) :
    variance (q.map (fun z => z - mean q)) / ‖mean q‖ ^ 2 ≤
      b a (mean q).re / (1 - b a (mean q).re) :=
  (EX01 q hm ha ha1 (mean_spec q (by omega)) hq hx0 hx1 rfl hr).1

/-- EX02's conditional hypothesis remains exactly the actual finite majorant. -/
theorem conditional_norm (q : Multiset ℂ) {a : ℝ} (hm : 7 ≤ q.card)
    (ha : 0 < a) (ha1 : a < 1) (hq : ∀ z ∈ q, ‖z‖ ≤ 1)
    (hx0 : -1 ≤ (mean q).re) (hx1 : (mean q).re ≤ 1)
    (hr : RawPolar q.card a (mean q).re)
    (hfin : PaperCenteredBound.majorant_Efin (q.map (fun z => z - mean q))
      (mean q) (a * mean q) ≤ (1 - a) / 2) :
    1 < ‖(q.card + 1 : ℂ) *
      (∫ t in (0 : ℝ)..1, (q.map (fun z => 1 - (a : ℂ) * t * z)).prod)‖ :=
  (EX02 q hm ha ha1 (mean_spec q (by omega)) hq hx0 hx1 rfl hr hfin).2.2.2

end Sendov.PaperMomentCorollariesTests
