import Sendov.Collinear.Moment
import tests.CollinearTests

open Polynomial
namespace Collinear.Round2Tests

-- Simplicity only at the marked root; all other roots can have arbitrary multiplicity.
example (p : ℝ[X]) (hs : p.Splits) (hn : 2 ≤ p.natDegree)
    (a : ℝ) (ha : a ∈ p.roots) (hm : p.rootMultiplicity a = 1) :
    ((p.derivative.roots.filter (· < a)).map (fun x => 1 / (a - x))).sum -
        ((p.derivative.roots.filter (a < ·)).map (fun x => 1 / (x - a))).sum =
      2 * (((p.roots.filter (· < a)).map (fun x => 1 / (a - x))).sum -
        ((p.roots.filter (a < ·)).map (fun x => 1 / (x - a))).sum) := by
  have hd : p.derivative.eval a ≠ 0 := by
    intro h
    have := (one_lt_rootMultiplicity_iff_isRoot (ne_zero_of_mem_roots ha)).mpr
      ⟨(mem_roots (ne_zero_of_mem_roots ha)).mp ha, h⟩
    omega
  have hb := reciprocal_balance p hs (by omega) a ha hd
  rwa [(reciprocal_decomposition p.roots a).1,
    (reciprocal_decomposition p.derivative.roots a).1] at hb

-- Endpoint consumers do not require strict interior membership or positive side lengths.
example (p : ℝ[X]) (hs : p.Splits) (hn : 2 ≤ p.natDegree)
    (A B : ℝ) (hAB : A < B) (hb : ∀ x ∈ p.roots, x ∈ Set.Icc A B)
    (ha : A ∈ p.roots) (hd : p.derivative.eval A ≠ 0) (r : ℝ) (hr : 1 ≤ r) :
    p.roots.filter (· < A) = 0 ∧
      (p.natDegree - 1 : ℝ) * (2 / (B - A)) ^ r ≤
        (p.derivative.roots.map (fun x => |A - x| ^ (-r))).sum := by
  refine ⟨?_, (diameter_moment p hs hn A B hAB hb A ha r hr).resolve_left hd⟩
  exact Multiset.filter_eq_nil.mpr (fun x hx => not_lt.mpr (hb x hx).1)

example (p : ℝ[X]) (hs : p.Splits) (hn : 2 ≤ p.natDegree)
    (A B : ℝ) (hAB : A < B) (hb : ∀ x ∈ p.roots, x ∈ Set.Icc A B)
    (ha : B ∈ p.roots) (hd : p.derivative.eval B ≠ 0) (r : ℝ) (hr : 1 ≤ r) :
    p.roots.filter (B < ·) = 0 ∧
      (p.natDegree - 1 : ℝ) * (2 / (B - A)) ^ r ≤
        (p.derivative.roots.map (fun x => |B - x| ^ (-r))).sum := by
  refine ⟨?_, (diameter_moment p hs hn A B hAB hb B ha r hr).resolve_left hd⟩
  exact Multiset.filter_eq_nil.mpr (fun x hx => not_lt.mpr (hb x hx).2)

-- The singular branch is genuinely available for arbitrary multiple roots.
example (p : ℝ[X]) (hn : 2 ≤ p.natDegree) (a : ℝ)
    (hm : 1 < p.rootMultiplicity a) : p.derivative.eval a = 0 := by
  have hp : p ≠ 0 := by intro h; simp [h] at hn
  exact ((one_lt_rootMultiplicity_iff_isRoot hp).mp hm).2

-- The finite branch never relies on a zero derivative-root distance.
example (p : ℝ[X]) (a : ℝ) (hd : p.derivative.eval a ≠ 0)
    (w : ℝ) (hw : w ∈ p.derivative.roots) : 0 < |a - w| := by
  apply abs_pos.mpr
  intro h
  have he := (mem_roots (ne_zero_of_mem_roots hw)).mp hw
  exact hd ((sub_eq_zero.mp h) ▸ he)

-- Exact occurrence count, not number of distinct roots and not n.
example (p : ℝ[X]) (hs : p.Splits) (hn : 2 ≤ p.natDegree) :
    p.derivative.roots.card = p.natDegree - 1 := by
  rw [← (derivative_root_budget p hs (by omega)).1.natDegree_eq_card_roots,
    natDegree_derivative]

-- Full final interface, including r=1, with no squarefree premise.
example (p : ℝ[X]) (hs : p.Splits) (hn : 2 ≤ p.natDegree)
    (A B : ℝ) (hAB : A < B) (hb : ∀ x ∈ p.roots, x ∈ Set.Icc A B)
    (a : ℝ) (ha : a ∈ p.roots) :
    p.derivative.eval a = 0 ∨
      (p.natDegree - 1 : ℝ) * (2 / (B - A)) ≤
        (p.derivative.roots.map (fun x => |a - x| ^ (-1 : ℝ))).sum := by
  simpa only [Real.rpow_one] using diameter_moment p hs hn A B hAB hb a ha 1 le_rfl

-- Dropping the disjunction is false, even for a fully split quadratic in a
-- positive-length interval.  This is a symbolic family, not numeric sampling.
example (a : ℝ) :
    let p : ℝ[X] := (X - C a) ^ 2
    p.Splits ∧ p.natDegree = 2 ∧ a - 1 < a + 1 ∧
      (∀ x ∈ p.roots, x ∈ Set.Icc (a - 1) (a + 1)) ∧
      a ∈ p.roots ∧
      ¬((p.natDegree - 1 : ℝ) * (2 / ((a + 1) - (a - 1))) ≤
        (p.derivative.roots.map (fun x => 1 / |a - x|)).sum) := by
  dsimp only
  have hd : ((X - C a) ^ 2).derivative = C 2 * (X - C a) := by simp [derivative_pow]
  have hroot : (((X - C a) ^ 2 : ℝ[X]).derivative).roots = {a} := by
    rw [hd, roots_C_mul _ (by norm_num), roots_X_sub_C]
  have hdeg : ((X - C a) ^ 2 : ℝ[X]).natDegree = 2 := by simp
  refine ⟨(Splits.X_sub_C a).pow _, hdeg, by linarith, ?_, ?_, ?_⟩
  · intro x hx
    have he : x = a := by
      simpa [sub_eq_zero] using (mem_roots (pow_ne_zero 2 (X_sub_C_ne_zero a))).mp hx
    subst x
    constructor <;> linarith
  · rw [mem_roots (pow_ne_zero 2 (X_sub_C_ne_zero a))]
    simp
  · rw [hroot, hdeg]
    norm_num

#print axioms Collinear.reciprocal_balance
#print axioms Collinear.reciprocal_decomposition
#print axioms Collinear.two_sided_mass
#print axioms Collinear.diameter_reciprocal
#print axioms Collinear.diameter_moment

end Collinear.Round2Tests
