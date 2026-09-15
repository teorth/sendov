import Sendov.Collinear.Mass

open Polynomial

namespace Collinear.Tests

-- The public gate is not restricted to a fixed degree or squarefree polynomial.
example (p : ℝ[X]) (hs : p.Splits) (hn : 2 ≤ p.natDegree) :
    p.derivative.Splits ∧
    p.derivative.roots = (p.roots - p.roots.dedup) +
      (p.derivative.roots.toFinset \ p.roots.toFinset).val ∧
    (p.derivative.roots.toFinset \ p.roots.toFinset).card + 1 =
      p.roots.toFinset.card :=
  Collinear.derivative_root_budget p hs (by omega)

-- Nontrivial universal consumer: both signed sides, arbitrary distinguished root.
example (p : ℝ[X]) (hs : p.Splits) (hn : 2 ≤ p.natDegree)
    (a : ℝ) (ha : a ∈ p.roots) :
    (((p.roots.filter (· < a)).map (fun x => 1 / (a - x))).sum ≤
      ((p.derivative.roots.filter (· < a)).map (fun y => 1 / (a - y))).sum) ∧
    (((p.roots.filter (a < ·)).map (fun x => 1 / (x - a))).sum ≤
      ((p.derivative.roots.filter (a < ·)).map (fun y => 1 / (y - a))).sum) :=
  Collinear.signed_reciprocal_domination p hs (by omega) a ha

-- Multiple-root branch must be routed away from finite reciprocal moments.
-- This is a general regression, not a fixed example with coincident roots.
example (p : ℝ[X]) (hn : 2 ≤ p.natDegree) (a : ℝ)
    (hm : 1 < p.rootMultiplicity a) : p.derivative.IsRoot a := by
  have hp : p ≠ 0 := by intro h; simp [h] at hn
  exact ((one_lt_rootMultiplicity_iff_isRoot hp).mp hm).2

-- At a simple original root the derivative denominator really is nonzero.
example (p : ℝ[X]) (hn : 2 ≤ p.natDegree) (a : ℝ)
    (hm : p.rootMultiplicity a = 1) : ¬p.derivative.IsRoot a := by
  have hp : p ≠ 0 := by intro h; simp [h] at hn
  intro hd
  have ha : p.IsRoot a := (rootMultiplicity_pos hp).mp (by omega)
  have := (one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨ha, hd⟩
  omega

#print axioms Collinear.derivative_root_budget
#print axioms Collinear.new_critical_point_gap
#print axioms Collinear.adjacent_gap_unique
#print axioms Collinear.signed_reciprocal_domination

end Collinear.Tests
