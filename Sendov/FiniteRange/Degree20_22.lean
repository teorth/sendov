/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.FiniteRange.Batch
import Sendov.FiniteRange.PackBridge

/-!
# The batch 20 to 22

`Sendov.R_le_batch` bounds every `R n α` for `20 ≤ n ≤ 22` by the elementary part and
moment at `n₀ = 20` together with the prefactor at `n₁ = 22`, so one moment and one
certificate serve all 3 degrees.  The certificate has degree 18, set by `n₀` rather
than `n₁`.

Feasibility at `n₀` is proved rather than assumed: for `n ≥ 36` it follows from
`0 ≤ α ≤ 17`, since `A - c²` increases with `n`.  This matters because feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`.
-/

-- Generated numerals cannot be wrapped, so the long-line linter is off in this file.
set_option linter.style.longLine false
set_option maxRecDepth 4000000

namespace Sendov

namespace B20_22

lemma M_lo : M 20 = 19 := by norm_num [M]

lemma M_hi : M 22 = 21 := by norm_num [M]

lemma A_lo (α : ℝ) : A 20 α = 1 - 2 * α / 19 := by rw [A, M]; push_cast; ring

lemma A_hi (α : ℝ) : A 22 α = 1 - 2 * α / 21 := by rw [A, M]; push_cast; ring

lemma c_lo {α : ℝ} (hα : 0 ≤ α) : c 20 α = (114 + 13 * α - 2 * α ^ 2) / (38 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring

/-- `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
which for `n₀ < 36` does not follow from `α ≤ 17`. -/
lemma c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 21 / 2) : 0 ≤ c 20 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

def Lc : ℤ := 232792560

def betac : ℤ := 4131209409209679854788987576321

def tauc : ℤ := 44775284788996865642893254679922271778917421122771510633920083377417225592961214127138545037980122454589072908657663380807599570953499350023955756845650273335369910042414392837789684225435587469649384627401365137215111142493529834089724868392831219963919558050105735619336220634358348775620366460327078867856343356142091112197183816351904389560191323401011583801350056642509421229073471652965690556344130689616076286735679016586779542709253460049049834200030423394619361068308927407924992768190982659511467666364074304423376770648009486446989819845183327368715672103880903585609634804230071151638268944708950497970217303849145427269129679404213103006562198768221354213524467878675079767978766859201415554409852677086782888653509986106731604823282151130888540570232939710702306888786166273

/-- The moment numerator at `n₀ = 20`, `k = 8`. -/
def Nmomc : List ℤ :=
  [342652681018715139072, 1290458050152354091008, 2243577184611827226624, 2399637756691021787136, 1783512729454695095808, 996976999580720707584, 454864090944105851904, 197832256724748957696, 157260237317474747904, 14092143950522867712, 885156618381127680, 38940288112115712, 1195127971889152, 25104659120128, 344544313344, 2787377152, 10092544]

theorem pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 20) (gg1 20) (gg2 20) 8)) α := by
  refine pev_wsum_eq_of_packed (gg0 20) (gg1 20) (gg2 20) 8 25 Lc betac
    tauc Nmomc (by norm_num [betac]) (by norm_num [tauc]) ?_ ?_ ?_ ?_ ?_ ?_ α
  · refine rowZ_bound (gg0 20) (gg1 20) (gg2 20) 8 3 betac tauc
      (by norm_num [betac]) (by simp) (by simp) (by simp) ?_
    norm_num [gg0, gg1, gg2, l1, betac, tauc]
  · decide
  · refine wsum_bound (gg0 20) (gg1 20) (gg2 20) 8 Lc betac
      (by norm_num [Lc]) ?_
    norm_num [gg0, gg1, gg2, l1, Lc, betac]
  · decide
  · exact wsum_length_le Lc _ 0
      (qrow_entry_length_le (gg0 20) (gg1 20) (gg2 20) 3 (by simp) (by simp) (by simp) 8)
  · rfl

theorem integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 20 α t ^ 8)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 20 * (3 + α)) ^ 8) :=
  integral_moment_packed 20 8 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)

set_option maxHeartbeats 2000000 in
-- the degree-18 Bernstein identity exceeds the default budget
/-- The certificate: `17 ^ 18 * P α` is a positive combination of `αʲ (17-α)^(18-j)`. -/
lemma P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 21 / 2) :
    0 < 721140310389707127738 + 2170180610909239016088 * α + 2889750967198268814324 * α ^ 2 + 2227128338977232972904 * α ^ 3 + 1085997068794302710391 * α ^ 4 + 339049376116278228288 * α ^ 5 + 60509700204282383346 * α ^ 6 - 1038039442012938636 * α ^ 7 - 14060791839010189905 * α ^ 8 + 1774506642858471852 * α ^ 9 + 45855210342618468 * α ^ 10 + 226538249017920 * α ^ 11 - 222291771124416 * α ^ 12 - 18538380993792 * α ^ 13 - 787852835840 * α ^ 14 - 20286313472 * α ^ 15 - 320448768 * α ^ 16 - 2874368 * α ^ 17 - 11264 * α ^ 18 := by
  have hu : (0 : ℝ) ≤ 21 - 2 * α := by linarith
  have hid : (21 : ℝ) ^ 18 * (721140310389707127738 + 2170180610909239016088 * α + 2889750967198268814324 * α ^ 2 + 2227128338977232972904 * α ^ 3 + 1085997068794302710391 * α ^ 4 + 339049376116278228288 * α ^ 5 + 60509700204282383346 * α ^ 6 - 1038039442012938636 * α ^ 7 - 14060791839010189905 * α ^ 8 + 1774506642858471852 * α ^ 9 + 45855210342618468 * α ^ 10 + 226538249017920 * α ^ 11 - 222291771124416 * α ^ 12 - 18538380993792 * α ^ 13 - 787852835840 * α ^ 14 - 20286313472 * α ^ 15 - 320448768 * α ^ 16 - 2874368 * α ^ 17 - 11264 * α ^ 18) = 721140310389707127738 * (21 - 2 * α) ^ 18 + 71534844003123475936416 * α ^ 1 * (21 - 2 * α) ^ 17 + 3265227002682133966779372 * α ^ 2 * (21 - 2 * α) ^ 16 + 90905348441621278719467208 * α ^ 3 * (21 - 2 * α) ^ 15 + 1724899809677710491069520311 * α ^ 4 * (21 - 2 * α) ^ 14 + 23603549699659251265167149604 * α ^ 5 * (21 - 2 * α) ^ 13 + 240138761499155563910895585654 * α ^ 6 * (21 - 2 * α) ^ 12 + 1837366344267267569709080196468 * α ^ 7 * (21 - 2 * α) ^ 11 + 10104702475479597929008103413095 * α ^ 8 * (21 - 2 * α) ^ 10 + 37641802639366180553916149163576 * α ^ 9 * (21 - 2 * α) ^ 9 + 88449061215859475411346373536264 * α ^ 10 * (21 - 2 * α) ^ 8 + 113640861426905556745222707601920 * α ^ 11 * (21 - 2 * α) ^ 7 + 55669273871103476657042199021792 * α ^ 12 * (21 - 2 * α) ^ 6 + 99281941699214882417362945572096 * α ^ 13 * (21 - 2 * α) ^ 5 + 654986082897929475911576119281408 * α ^ 14 * (21 - 2 * α) ^ 4 + 1538940561324052318678745687107584 * α ^ 15 * (21 - 2 * α) ^ 3 + 1719020178639381082845279983473152 * α ^ 16 * (21 - 2 * α) ^ 2 + 910135906460129539245476343896064 * α ^ 17 * (21 - 2 * α) ^ 1 + 165769381149578270034391223083008 * α ^ 18 := by
    ring
  -- All coefficients are checked by positivity. The last summand is positive for α > 0;
  -- at α = 0 the first summand is positive. The identity above checks every coefficient.
  apply (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < (21 : ℝ) ^ 18)).mp
  rw [hid]
  rcases lt_or_eq_of_le hα with hpos | hzero
  · positivity
  · have hu_pos : (0 : ℝ) < 21 - 2 * α := by linarith
    positivity

set_option maxHeartbeats 2000000 in
-- clearing denominators across the batch identity exceeds the default budget
/-- **The batch `20 ≤ n ≤ 22`.** -/
theorem finite_range {n : ℕ} (h0 : 20 ≤ n) (h1 : n ≤ 22) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 21 / 2 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (22 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (22 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 20) (n := n) (n₁ := 22) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((20 : ℕ) : ℝ) - 4 = 16 by norm_num] at hb
  rw [show (16 : ℝ) / 2 = ((8 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 19) + 1 / (4 * 19 * (3 + α))
      + (1 - 2 * α / 21) ^ 2 * 22 * 21 * (22 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 19 * (3 + α)) ^ 8))
      = 1 - (721140310389707127738 + 2170180610909239016088 * α + 2889750967198268814324 * α ^ 2 + 2227128338977232972904 * α ^ 3 + 1085997068794302710391 * α ^ 4 + 339049376116278228288 * α ^ 5 + 60509700204282383346 * α ^ 6 - 1038039442012938636 * α ^ 7 - 14060791839010189905 * α ^ 8 + 1774506642858471852 * α ^ 9 + 45855210342618468 * α ^ 10 + 226538249017920 * α ^ 11 - 222291771124416 * α ^ 12 - 18538380993792 * α ^ 13 - 787852835840 * α ^ 14 - 20286313472 * α ^ 15 - 320448768 * α ^ 16 - 2874368 * α ^ 17 - 11264 * α ^ 18) / (53913369794124204 * (3 + α) ^ 9) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  have hq : 0 < (721140310389707127738 + 2170180610909239016088 * α + 2889750967198268814324 * α ^ 2 + 2227128338977232972904 * α ^ 3 + 1085997068794302710391 * α ^ 4 + 339049376116278228288 * α ^ 5 + 60509700204282383346 * α ^ 6 - 1038039442012938636 * α ^ 7 - 14060791839010189905 * α ^ 8 + 1774506642858471852 * α ^ 9 + 45855210342618468 * α ^ 10 + 226538249017920 * α ^ 11 - 222291771124416 * α ^ 12 - 18538380993792 * α ^ 13 - 787852835840 * α ^ 14 - 20286313472 * α ^ 15 - 320448768 * α ^ 16 - 2874368 * α ^ 17 - 11264 * α ^ 18) / (53913369794124204 * (3 + α) ^ 9) := div_pos hP (by positivity)
  linarith

end B20_22

end Sendov
