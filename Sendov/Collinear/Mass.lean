import Sendov.Collinear.Gate

open Polynomial
open scoped BigOperators

namespace Collinear

/-- Monotone nonnegative mass transfers along finite root gaps.  Multiplicities
are handled by cancelling the common `s - s.dedup` part, not by discarding them. -/
private theorem weighted_left {α : Type*} [LinearOrder α]
    (s t : Multiset α) (u : Finset α)
    (ht : t = (s - s.dedup) + u.val)
    (hgap : ∀ x ∈ s, ∀ y ∈ s, x < y →
      (∀ v ∈ s, v ∉ Set.Ioo x y) → ∃ w ∈ u, x < w ∧ w < y)
    (a : α) (ha : a ∈ s) (f : α → ℝ)
    (hf : ∀ x y, x ≤ y → y < a → f x ≤ f y)
    (hpos : ∀ y, y < a → 0 ≤ f y) :
    ((s.filter (· < a)).map f).sum ≤ ((t.filter (· < a)).map f).sum := by
  classical
  let l := s.toFinset.filter (· < a)
  let r := u.filter (· < a)
  have hex : ∀ x, ∃ y, x ∈ l →
      y ∈ r ∧ x < y ∧ (∀ v ∈ s, x < v → y < v) := by
    intro x
    by_cases hx : x ∈ l
    · obtain ⟨hxs, hxa⟩ := Finset.mem_filter.mp hx
      obtain ⟨b, hb, hxb, hleast⟩ := Finset.exists_next_right
        (s := s.toFinset) ⟨a, Multiset.mem_toFinset.mpr ha, hxa⟩
      obtain ⟨w, hw, hxw, hwb⟩ := hgap x (Multiset.mem_toFinset.mp hxs)
        b (Multiset.mem_toFinset.mp hb) hxb (by
          intro v hv hvi
          exact hvi.2.not_ge (hleast v (Multiset.mem_toFinset.mpr hv) hvi.1))
      refine ⟨w, fun _ => ⟨Finset.mem_filter.mpr ⟨hw, ?_⟩, hxw, ?_⟩⟩
      · exact hwb.trans_le (hleast a (Multiset.mem_toFinset.mpr ha) hxa)
      · intro v hv hxv
        exact hwb.trans_le (hleast v (Multiset.mem_toFinset.mpr hv) hxv)
    · exact ⟨a, fun h => (hx h).elim⟩
  choose g hg using hex
  have hginj : Set.InjOn g (↑l : Set α) := by
    intro x hx y hy heq
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · have hlt := (hg x hx).2.2 y
        (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hy).1) hxy
      exact False.elim ((hlt.trans (hg y hy).2.1).ne heq)
    · exact hxy
    · have hlt := (hg y hy).2.2 x
        (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hx).1) hyx
      exact False.elim ((hlt.trans (hg x hx).2.1).ne heq.symm)
  have hsum : ∑ x ∈ l, f x ≤ ∑ y ∈ r, f y := calc
    _ ≤ ∑ x ∈ l, f (g x) := Finset.sum_le_sum (fun x hx =>
      hf x (g x) (hg x hx).2.1.le (Finset.mem_filter.mp (hg x hx).1).2)
    _ = ∑ y ∈ l.image g, f y := (Finset.sum_image hginj).symm
    _ ≤ ∑ y ∈ r, f y := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.image_subset_iff.mpr (fun x hx => (hg x hx).1))
      (fun y hy _ => hpos y (Finset.mem_filter.mp hy).2)
  have hsdec : s = (s - s.dedup) + s.dedup :=
    (tsub_add_cancel_of_le (Multiset.dedup_le s)).symm
  have hs_sum := congrArg (fun m : Multiset α => ((m.filter (· < a)).map f).sum) hsdec
  have ht_sum := congrArg (fun m : Multiset α => ((m.filter (· < a)).map f).sum) ht
  simp only [Multiset.filter_add, Multiset.map_add, Multiset.sum_add] at hs_sum ht_sum
  rw [hs_sum, ht_sum]
  exact add_le_add (le_refl _) hsum

/-- The two signed-side inequalities in Zhang's Proposition 3.1.  They hold
with all occurrences counted, even before imposing simplicity of `a` (the
strict filters omit occurrences equal to `a`). -/
theorem signed_reciprocal_domination (p : ℝ[X]) (hs : p.Splits) (hn : 0 < p.natDegree)
    (a : ℝ) (ha : a ∈ p.roots) :
    (((p.roots.filter (· < a)).map (fun x => 1 / (a - x))).sum ≤
      ((p.derivative.roots.filter (· < a)).map (fun y => 1 / (a - y))).sum) ∧
    (((p.roots.filter (a < ·)).map (fun x => 1 / (x - a))).sum ≤
      ((p.derivative.roots.filter (a < ·)).map (fun y => 1 / (y - a))).sum) := by
  classical
  obtain ⟨_, ht, _⟩ := derivative_root_budget p hs hn
  have hgap : ∀ x ∈ p.roots, ∀ y ∈ p.roots, x < y →
      (∀ v ∈ p.roots, v ∉ Set.Ioo x y) →
      ∃ w ∈ p.derivative.roots.toFinset \ p.roots.toFinset, x < w ∧ w < y := by
    intro x hx y hy hxy hg
    obtain ⟨w, hw, _⟩ := adjacent_gap_unique p hs hn x hx y hy hxy hg
    exact ⟨w, Finset.mem_sdiff.mpr ⟨Multiset.mem_toFinset.mpr hw.1,
      fun h => hg w (Multiset.mem_toFinset.mp h) hw.2.1⟩, hw.2.1⟩
  constructor
  · apply weighted_left p.roots p.derivative.roots _ ht hgap a ha (fun x => 1 / (a - x))
    · intro x y hxy hya
      exact one_div_le_one_div_of_le (sub_pos.mpr hya) (sub_le_sub_left hxy a)
    · intro y hya
      exact le_of_lt (one_div_pos.mpr (sub_pos.mpr hya))
  · refine weighted_left (α := OrderDual ℝ)
      (show Multiset (OrderDual ℝ) from p.roots)
      (show Multiset (OrderDual ℝ) from p.derivative.roots)
      (show Finset (OrderDual ℝ) from
        p.derivative.roots.toFinset \ p.roots.toFinset) ?_
      (fun x hx y hy hyx hg => ?_) (OrderDual.toDual a) ha
      (fun x => 1 / (OrderDual.ofDual x - a)) ?_ ?_
    · exact ht
    · obtain ⟨w, hw, hyw, hwx⟩ := hgap y hy x hx hyx
        (fun v hv hvi => hg v hv ⟨hvi.2, hvi.1⟩)
      exact ⟨w, hw, hwx, hyw⟩
    · intro x y hyx hay
      exact one_div_le_one_div_of_le (sub_pos.mpr hay) (sub_le_sub_right hyx a)
    · intro y hay
      exact le_of_lt (one_div_pos.mpr (sub_pos.mpr hay))

end Collinear
