import Sendov.Collinear.Moment

open Polynomial
open scoped BigOperators
namespace Collinear

-- Acceptance contract: arbitrary degree, with all algebraic multiplicities retained.
example (p : ℝ[X]) (hs : p.Splits) (hn : 0 < p.natDegree) :
    p.derivative.Splits ∧
    p.derivative.roots = (p.roots - p.roots.dedup) +
      (p.derivative.roots.toFinset \ p.roots.toFinset).val ∧
    (p.derivative.roots.toFinset \ p.roots.toFinset).card + 1 =
      p.roots.toFinset.card := by
  exact derivative_root_budget p hs hn

-- Second vertical acceptance: every new critical point owns an adjacent gap,
-- and it is the unique critical point there.  The multiplicity is also certified.
example (p : ℝ[X]) (hs : p.Splits) (hn : 0 < p.natDegree)
    (z : ℝ) (hz : z ∈ p.derivative.roots) (hzp : z ∉ p.roots) :
    p.derivative.rootMultiplicity z = 1 ∧
    ∃ a ∈ p.roots, ∃ b ∈ p.roots,
      a < z ∧ z < b ∧
      (∀ x ∈ p.roots, x ∉ Set.Ioo a b) ∧
      (∀ w ∈ p.derivative.roots, w ∈ Set.Ioo a b → w = z) := by
  exact new_critical_point_gap p hs hn z hz hzp

-- Third vertical acceptance: not merely every new root has a gap, but every
-- adjacent gap has exactly one simple critical point.
example (p : ℝ[X]) (hs : p.Splits) (hn : 0 < p.natDegree)
    (a : ℝ) (ha : a ∈ p.roots) (b : ℝ) (hb : b ∈ p.roots)
    (hab : a < b) (hgap : ∀ x ∈ p.roots, x ∉ Set.Ioo a b) :
    ∃! z : ℝ, z ∈ p.derivative.roots ∧ z ∈ Set.Ioo a b ∧
      p.derivative.rootMultiplicity z = 1 := by
  exact adjacent_gap_unique p hs hn a ha b hb hab hgap

-- Degree-uniform signed-side acceptance; repetitions are Multiset occurrences.
example (p : ℝ[X]) (hs : p.Splits) (hn : 0 < p.natDegree)
    (a : ℝ) (ha : a ∈ p.roots) :
    (((p.roots.filter (· < a)).map (fun x => 1 / (a - x))).sum ≤
      ((p.derivative.roots.filter (· < a)).map (fun y => 1 / (a - y))).sum) ∧
    (((p.roots.filter (a < ·)).map (fun x => 1 / (x - a))).sum ≤
      ((p.derivative.roots.filter (a < ·)).map (fun y => 1 / (y - a))).sum) := by
  exact signed_reciprocal_domination p hs hn a ha

#print axioms reciprocal_balance
#print axioms two_sided_mass

example (p : ℝ[X]) (hs : p.Splits) (hn : 0 < p.natDegree)
    (a : ℝ) (ha : a ∈ p.roots) (hd : p.derivative.eval a ≠ 0) :
    ((p.derivative.roots.map (fun x => 1 / (a - x))).sum) =
      2 * ((p.roots.map (fun x => 1 / (a - x))).sum) := by
  exact reciprocal_balance p hs hn a ha hd

example (p : ℝ[X]) (hs : p.Splits) (hn : 0 < p.natDegree)
    (a : ℝ) (ha : a ∈ p.roots) (hd : p.derivative.eval a ≠ 0) :
    2 * ((p.roots.filter (· < a)).map (fun x => 1 / (a - x))).sum ≤
      (p.derivative.roots.map (fun x => 1 / |a - x|)).sum ∧
    2 * ((p.roots.filter (a < ·)).map (fun x => 1 / (x - a))).sum ≤
      (p.derivative.roots.map (fun x => 1 / |a - x|)).sum := by
  exact two_sided_mass p hs hn a ha hd

#print axioms diameter_reciprocal

example (p : ℝ[X]) (hs : p.Splits) (hn : 2 ≤ p.natDegree)
    (A B : ℝ) (hAB : A < B) (hroots : ∀ x ∈ p.roots, x ∈ Set.Icc A B)
    (a : ℝ) (ha : a ∈ p.roots) :
    p.derivative.eval a = 0 ∨
      (p.natDegree - 1 : ℝ) * (2 / (B - A)) ≤
        (p.derivative.roots.map (fun x => 1 / |a - x|)).sum := by
  exact diameter_reciprocal p hs hn A B hAB hroots a ha

#print axioms diameter_moment

example (p : ℝ[X]) (hs : p.Splits) (hn : 2 ≤ p.natDegree)
    (A B : ℝ) (hAB : A < B) (hroots : ∀ x ∈ p.roots, x ∈ Set.Icc A B)
    (a : ℝ) (ha : a ∈ p.roots) (r : ℝ) (hr : 1 ≤ r) :
    p.derivative.eval a = 0 ∨
      (p.natDegree - 1 : ℝ) * (2 / (B - A)) ^ r ≤
        (p.derivative.roots.map (fun x => |a - x| ^ (-r))).sum := by
  exact diameter_moment p hs hn A B hAB hroots a ha r hr

end Collinear
