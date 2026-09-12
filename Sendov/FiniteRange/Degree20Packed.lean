/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.FiniteRange.PackBridge
import Sendov.FiniteRange.Reduce

/-!
# Degree twenty through the packed path

A differential test of the packing bridge.  Degree twenty is already proved in
`Sendov.FiniteRange.Degree20` by the direct route, so any disagreement here is a bug in the
bridge rather than a new mathematical fact.  `Sendov.packed_agrees_twenty` states the
cross-check: the multinomial formula `(M)` and the packed recurrence compute the same
number, proved by transitivity through the integral itself, with no expansion at any `k`.
-/

-- Generated numerals cannot be wrapped, so the long-line linter is off in this file.
set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace Sendov

/-- `lcm (4 .. 20)`, clearing the weights `1/(j+4)` for `j` up to `16`. -/
def L20 : ℤ := 232792560

/-- Kronecker base packing a coefficient polynomial in `α`. -/
def beta20 : ℤ := 17557640290828443979548888553985

/-- Kronecker base packing the row, a polynomial in `t`. -/
def tau20 : ℤ := 1447326351619059204898716406983437305998463825678484019367742677287287571938439552267338057721680937249870701724020109571363451685542225000786583505247484723991737401320219819072484624701345840153357440293821689316804560778960232462168634392032438245400519751866728942882795389626136102212364132385633624149225435592794976728090795053404519509839779809147905536216226810069323449403279508449916679354531279513212284207024264926083620338904064993814111335110426148352741960595286112549871063419480493020052871564730892657665

/-- The moment numerator, supplied by the generator and verified below. -/
def Nmom20 : List ℤ :=
  [342652681018715139072, 1290458050152354091008, 2243577184611827226624, 2399637756691021787136, 1783512729454695095808, 996976999580720707584, 454864090944105851904, 197832256724748957696, 157260237317474747904, 14092143950522867712, 885156618381127680, 38940288112115712, 1195127971889152, 25104659120128, 344544313344, 2787377152, 10092544]

/-- The generator's numerator is the moment numerator.  The computational content is one
integer exponentiation and seventeen digit extractions. -/
theorem Nmom20_eq :
    Nmom20 = wsum L20 0 (qrow (gg0 20) (gg1 20) (gg2 20) 8) := by
  refine wsum_eq_of_packed (gg0 20) (gg1 20) (gg2 20) 8 L20 beta20 tau20 Nmom20
    (by decide) (by decide) ?_ ?_ ?_ ?_ ?_
  · decide -- No overflow when packing the row in τ.
  · decide -- The supplied numerator coefficients fit in β.
  · decide -- The computed weighted sum also fits in β.
  · rfl -- The two coefficient lists have the same length.
  · rfl -- Exact packed integer equality.

/-- The degree-twenty moment, via the packed route. -/
theorem integral_twenty_packed (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 20 α t ^ 8)
      = pev Nmom20 α / ((L20 : ℝ) * (2 * M 20 * (3 + α)) ^ 8) :=
  integral_moment_packed 20 8 (by norm_num) α hα L20 (by decide) Nmom20
    (by decide) (by rw [Nmom20_eq])

/-- **The cross-check.**  The multinomial formula and the packed recurrence agree.  Neither
side is expanded: both compute the same integral, so they are equal by transitivity. -/
theorem packed_agrees_twenty (α : ℝ) (hα : 0 ≤ α) :
    pev Nmom20 α / ((L20 : ℝ) * (2 * M 20 * (3 + α)) ^ 8) = mom 20 α 8 := by
  exact (integral_twenty_packed α hα).symm.trans (integral_moment 20 α 8)

end Sendov
