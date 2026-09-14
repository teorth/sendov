import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Algebra.Polynomial.Splits

open Polynomial

namespace Collinear

/-- Rolle's lower bounds exhaust the derivative degree.  The old roots lose one
copy each; all remaining derivative roots are simple, and there are exactly one
fewer of them than distinct original roots. -/
theorem derivative_root_budget (p : ℝ[X]) (hs : p.Splits) (hn : 0 < p.natDegree) :
    p.derivative.Splits ∧
    p.derivative.roots = (p.roots - p.roots.dedup) +
      (p.derivative.roots.toFinset \ p.roots.toFinset).val ∧
    (p.derivative.roots.toFinset \ p.roots.toFinset).card + 1 =
      p.roots.toFinset.card := by
  classical
  let u := p.derivative.roots.toFinset \ p.roots.toFinset
  let m := (p.roots - p.roots.dedup) + u.val
  have hle : m ≤ p.derivative.roots := by
    apply Multiset.le_iff_count.mpr
    intro a
    by_cases ha : a ∈ p.roots
    · have hau : a ∉ u := by simp [u, ha]
      simp only [m, Multiset.count_add, Multiset.count_sub,
        Multiset.count_dedup, ha, ↓reduceIte]
      have huz : u.val.count a = 0 := Multiset.count_eq_zero.mpr hau
      rw [huz, add_zero, count_roots, count_roots]
      exact rootMultiplicity_sub_one_le_derivative_rootMultiplicity p a
    · have haz := Multiset.count_eq_zero.mpr ha
      simp only [m, Multiset.count_add, Multiset.count_sub, haz,
        Nat.zero_sub, zero_add]
      exact Multiset.le_iff_count.mp
        (le_trans (Finset.val_le_iff.mpr (Finset.sdiff_subset (s := p.derivative.roots.toFinset)
          (t := p.roots.toFinset))) (Multiset.dedup_le _)) a
  have hcardp : p.roots.card = p.natDegree := hs.natDegree_eq_card_roots.symm
  have hcount := p.card_roots_le_derivative
  have hupper := p.derivative.card_roots'
  rw [p.natDegree_derivative] at hupper
  have hcardd : p.derivative.roots.card = p.natDegree - 1 := by omega
  have hsplit : p.derivative.Splits :=
    splits_iff_card_roots.mpr (by simpa [p.natDegree_derivative] using hcardd)
  have hdistinct := p.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ
  have hdedup : p.roots.dedup.card = p.roots.toFinset.card := rfl
  have hsmall : p.roots.toFinset.card ≤ p.roots.card := by
    simpa [hdedup] using Multiset.card_le_card (Multiset.dedup_le p.roots)
  have hmcard : m.card = p.natDegree - p.roots.toFinset.card + u.card := by
    simp only [m, Multiset.card_add, Multiset.card_sub (Multiset.dedup_le _),
      hcardp, hdedup, Finset.card_def]
  have heq : m = p.derivative.roots :=
    Multiset.eq_of_le_of_card_le hle (by dsimp [u] at hmcard; omega)
  have hnew : u.card + 1 = p.roots.toFinset.card := by
    have := congrArg Multiset.card heq
    omega
  exact ⟨hsplit, heq.symm, hnew⟩

/-- A saturated finite interlacing has no dispensable point.  Erasing a point
would violate mathlib's interlaced cardinality bound. -/
private theorem essential_gap (s t : Finset ℝ) (hcard : t.card + 1 = s.card)
    (hrolle : ∀ a ∈ s, ∀ b ∈ s, a < b →
      (∀ x ∈ s, x ∉ Set.Ioo a b) → ∃ w ∈ t, a < w ∧ w < b)
    (z : ℝ) (hz : z ∈ t) :
    ∃ a ∈ s, ∃ b ∈ s, a < z ∧ z < b ∧
      (∀ x ∈ s, x ∉ Set.Ioo a b) ∧
      (∀ w ∈ t, w ∈ Set.Ioo a b → w = z) := by
  classical
  have hfail : ¬ (∀ a ∈ s, ∀ b ∈ s, a < b →
      (∀ x ∈ s, x ∉ Set.Ioo a b) → ∃ w ∈ t.erase z, a < w ∧ w < b) := by
    intro h
    have hc := Finset.card_le_of_interleaved h
    rw [Finset.card_erase_of_mem hz] at hc
    have hp := Finset.card_pos.mpr ⟨z, hz⟩
    omega
  push Not at hfail
  obtain ⟨a, ha, b, hb, hab, hgap, hnone⟩ := hfail
  have hunique : ∀ w ∈ t, w ∈ Set.Ioo a b → w = z := by
    intro w hw hwi
    by_contra hwz
    exact (hnone w (Finset.mem_erase.mpr ⟨hwz, hw⟩) hwi.1).not_gt hwi.2
  obtain ⟨w, hw, haw, hwb⟩ := hrolle a ha b hb hab hgap
  have hwz := hunique w hw ⟨haw, hwb⟩
  exact ⟨a, ha, b, hb, hwz ▸ haw, hwz ▸ hwb, hgap, hunique⟩

private theorem rolle_new (p : ℝ[X]) (hp : p ≠ 0) (hd : p.derivative ≠ 0)
    (a : ℝ) (ha : a ∈ p.roots.toFinset)
    (b : ℝ) (hb : b ∈ p.roots.toFinset) (hab : a < b)
    (hgap : ∀ x ∈ p.roots.toFinset, x ∉ Set.Ioo a b) :
    ∃ w ∈ p.derivative.roots.toFinset \ p.roots.toFinset, a < w ∧ w < b := by
  rw [Multiset.mem_toFinset, mem_roots hp] at ha hb
  obtain ⟨w, hwi, hw⟩ := exists_deriv_eq_zero hab p.continuousOn (ha.trans hb.symm)
  refine ⟨w, Finset.mem_sdiff.mpr ⟨?_, ?_⟩, hwi⟩
  · rwa [Multiset.mem_toFinset, mem_roots hd, IsRoot, ← p.deriv]
  · exact fun h => hgap w h hwi

/-- Every derivative root not inherited from an old multiple root is simple
and is the unique derivative root in one adjacent open root gap. -/
theorem new_critical_point_gap (p : ℝ[X]) (hs : p.Splits) (hn : 0 < p.natDegree)
    (z : ℝ) (hz : z ∈ p.derivative.roots) (hzp : z ∉ p.roots) :
    p.derivative.rootMultiplicity z = 1 ∧
    ∃ a ∈ p.roots, ∃ b ∈ p.roots,
      a < z ∧ z < b ∧
      (∀ x ∈ p.roots, x ∉ Set.Ioo a b) ∧
      (∀ w ∈ p.derivative.roots, w ∈ Set.Ioo a b → w = z) := by
  classical
  obtain ⟨_, heq, hcard⟩ := derivative_root_budget p hs hn
  have hzt : z ∈ p.derivative.roots.toFinset \ p.roots.toFinset := by
    simp [hz, hzp]
  have hmult : p.derivative.rootMultiplicity z = 1 := by
    rw [← count_roots, heq]
    simp [Multiset.count_add, Multiset.count_sub, hz, hzp]
  have hp : p ≠ 0 := by intro h; simp [h] at hn
  have hd : p.derivative ≠ 0 := by
    intro h
    have := eq_C_of_derivative_eq_zero h
    rw [this] at hn
    simp at hn
  obtain ⟨a, ha, b, hb, haz, hzb, hgap, huniq⟩ :=
    essential_gap _ _ hcard (rolle_new p hp hd) z hzt
  refine ⟨hmult, a, Multiset.mem_toFinset.mp ha, b, Multiset.mem_toFinset.mp hb,
    haz, hzb, ?_, ?_⟩
  · intro x hx
    exact hgap x (Multiset.mem_toFinset.mpr hx)
  · intro w hw hwi
    apply huniq w _ hwi
    exact Finset.mem_sdiff.mpr ⟨Multiset.mem_toFinset.mpr hw,
      fun h => hgap w h hwi⟩

/-- Every adjacent distinct-root gap contains exactly one derivative root;
that root is simple. No squarefreeness hypothesis is imposed on `p`. -/
theorem adjacent_gap_unique (p : ℝ[X]) (hs : p.Splits) (hn : 0 < p.natDegree)
    (a : ℝ) (ha : a ∈ p.roots) (b : ℝ) (hb : b ∈ p.roots)
    (hab : a < b) (hgap : ∀ x ∈ p.roots, x ∉ Set.Ioo a b) :
    ∃! z : ℝ, z ∈ p.derivative.roots ∧ z ∈ Set.Ioo a b ∧
      p.derivative.rootMultiplicity z = 1 := by
  classical
  have hp : p ≠ 0 := by intro h; simp [h] at hn
  have hd : p.derivative ≠ 0 := by
    intro h
    have := eq_C_of_derivative_eq_zero h
    rw [this] at hn
    simp at hn
  obtain ⟨z, hz, haz, hzb⟩ := rolle_new p hp hd a
    (Multiset.mem_toFinset.mpr ha) b (Multiset.mem_toFinset.mpr hb) hab
    (fun x hx => hgap x (Multiset.mem_toFinset.mp hx))
  obtain ⟨hzd, hzp⟩ := Finset.mem_sdiff.mp hz
  have hzroot := Multiset.mem_toFinset.mp hzd
  obtain ⟨hmult, c, hc, d, hdroot, hcz, hzd', hgap', huniq⟩ :=
    new_critical_point_gap p hs hn z hzroot
      (fun h => hzp (Multiset.mem_toFinset.mpr h))
  have hac : a = c := le_antisymm
    (le_of_not_gt (fun h => hgap' a ha ⟨h, haz.trans hzd'⟩))
    (le_of_not_gt (fun h => hgap c hc ⟨h, hcz.trans hzb⟩))
  have hbd : b = d := le_antisymm
    (le_of_not_gt (fun h => hgap d hdroot ⟨haz.trans hzd', h⟩))
    (le_of_not_gt (fun h => hgap' b hb ⟨hcz.trans hzb, h⟩))
  refine ⟨z, ⟨hzroot, ⟨haz, hzb⟩, hmult⟩, ?_⟩
  intro w hw
  apply huniq w hw.1
  simpa [← hac, ← hbd] using hw.2.1

end Collinear
