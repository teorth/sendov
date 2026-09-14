import Sendov.Collinear.Balance

open Polynomial
namespace Collinear

/-- No division by a side length: this also covers empty endpoint sides. -/
private theorem count_le_side_mass (s : Multiset ℝ) (A B a : ℝ)
    (hb : ∀ x ∈ s, x ∈ Set.Icc A B) (hne : a ∉ s) :
    (s.card : ℝ) ≤
      (a - A) * ((s.filter (· < a)).map (fun x => 1 / (a - x))).sum +
      (B - a) * ((s.filter (a < ·)).map (fun x => 1 / (x - a))).sum := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
    have hxs := hb x (Multiset.mem_cons_self x s)
    have hxa : x ≠ a := by intro h; subst x; exact hne (Multiset.mem_cons_self a s)
    have hi := ih (fun y hy => hb y (Multiset.mem_cons_of_mem hy))
      (fun h => hne (Multiset.mem_cons_of_mem h))
    simp only [Multiset.card_cons, Nat.cast_add, Nat.cast_one, Multiset.filter_cons]
    rcases lt_or_gt_of_ne hxa with h | h
    · have ht : 1 ≤ (a - A) * (1 / (a - x)) := by
        rw [mul_one_div, le_div_iff₀ (sub_pos.mpr h)]; linarith [hxs.1]
      simp only [h, not_lt.mpr h.le, ite_true, ite_false, zero_add,
        Multiset.map_add, Multiset.sum_add, Multiset.map_singleton, Multiset.sum_singleton]
      nlinarith
    · have ht : 1 ≤ (B - a) * (1 / (x - a)) := by
        rw [mul_one_div, le_div_iff₀ (sub_pos.mpr h)]; linarith [hxs.2]
      simp only [h, not_lt.mpr h.le, ite_true, ite_false, zero_add,
        Multiset.map_add, Multiset.sum_add, Multiset.map_singleton, Multiset.sum_singleton]
      nlinarith

/-- The real-root diameter bound with the multiple-root branch explicit. -/
theorem diameter_reciprocal (p : ℝ[X]) (hs : p.Splits) (hn : 2 ≤ p.natDegree)
    (A B : ℝ) (hAB : A < B) (hroots : ∀ x ∈ p.roots, x ∈ Set.Icc A B)
    (a : ℝ) (ha : a ∈ p.roots) :
    p.derivative.eval a = 0 ∨
      (p.natDegree - 1 : ℝ) * (2 / (B - A)) ≤
        (p.derivative.roots.map (fun x => 1 / |a - x|)).sum := by
  classical
  by_cases hd : p.derivative.eval a = 0
  · exact Or.inl hd
  right
  have hp := ne_zero_of_mem_roots ha
  have hm : p.rootMultiplicity a = 1 := by
    have hpos := (rootMultiplicity_pos hp).mpr ((mem_roots hp).mp ha)
    have hnot : ¬1 < p.rootMultiplicity a := by
      intro h; exact hd ((one_lt_rootMultiplicity_iff_isRoot hp).mp h).2
    omega
  have hne : a ∉ p.roots.erase a := by
    rw [← Multiset.count_eq_zero, Multiset.count_erase_self, count_roots, hm]
  have hc := count_le_side_mass (p.roots.erase a) A B a
    (fun x hx => hroots x (Multiset.mem_of_mem_erase hx)) hne
  have hcard : ((p.roots.erase a).card : ℝ) = p.natDegree - 1 := by
    have h := Multiset.card_erase_add_one ha
    rw [hs.natDegree_eq_card_roots] at ⊢
    have hh : ((p.roots.erase a).card : ℝ) + 1 = p.roots.card := by exact_mod_cast h
    linarith
  have hside :
      p.roots.filter (· < a) = (p.roots.erase a).filter (· < a) ∧
      p.roots.filter (a < ·) = (p.roots.erase a).filter (a < ·) := by
    constructor <;> (conv_lhs => rw [← Multiset.cons_erase ha]) <;> simp
  rw [hcard, ← hside.1, ← hside.2] at hc
  obtain ⟨hl, hr⟩ := two_sided_mass p hs (by omega) a ha hd
  have hL := mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr (hroots a ha).1)
  have hR := mul_le_mul_of_nonneg_left hr (sub_nonneg.mpr (hroots a ha).2)
  rw [← mul_div_assoc, div_le_iff₀ (sub_pos.mpr hAB)]
  nlinarith

end Collinear
