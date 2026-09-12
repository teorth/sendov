/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.FiniteRange.Batch
import Sendov.FiniteRange.PackBridge
import Sendov.Common.BernsteinCert

/-!
# The batch 18 to 20

`Sendov.R_le_batch` bounds every `R n α` for `18 ≤ n ≤ 20` by the elementary part and
moment at `n₀ = 18` together with the prefactor at `n₁ = 20`, so one moment and one
certificate serve all 3 degrees.  The certificate has degree 16, set by `n₀` rather
than `n₁`.

Feasibility at `n₀` is proved rather than assumed: for `n ≥ 36` it follows from
`0 ≤ α ≤ 17`, since `A - c²` increases with `n`.  This matters because feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`.
-/

-- Generated numerals cannot be wrapped, so the long-line linter is off in this file.
set_option linter.style.longLine false
set_option maxRecDepth 4000000

namespace Sendov

namespace B18_20

lemma M_lo : M 18 = 17 := by norm_num [M]

lemma M_hi : M 20 = 19 := by norm_num [M]

lemma A_lo (α : ℝ) : A 18 α = 1 - 2 * α / 17 := by rw [A, M]; push_cast; ring

lemma A_hi (α : ℝ) : A 20 α = 1 - 2 * α / 19 := by rw [A, M]; push_cast; ring

lemma c_lo {α : ℝ} (hα : 0 ≤ α) : c 18 α = (102 + 11 * α - 2 * α ^ 2) / (34 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring

/-- `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
which for `n₀ < 36` does not follow from `α ≤ 17`. -/
lemma c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 19 / 2) : 0 ≤ c 18 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

def Lc : ℤ := 12252240

def betac : ℤ := 175927662917225332359966721

def tauc : ℤ := 358483832023654241638315162089194303184230572320526650607274337745620624638936275643757889347744511177653609383831346364707120039183150206364616435398207395719060972709006144830720087322332895913982687118230996245850245160708643412112175024743903798686289485089015224938759859379750541156419506275337584501638157246946150682644437302655829353348979444821042370136731772238800566165427866451094788337835108013894151378044974961647775374731862145935889517758974312266434672837815042172397866699143848730300875843409734000578209410972334682764700002022390759745948434344742136442797552789219566126849

/-- The moment numerator at `n₀ = 18`, `k = 7`. -/
def Nmomc : List ℤ :=
  [114983435331692928, 401488164091808640, 646936588267361280, 643985937083510784, 451960609895464320, 248282531980689024, 125596226938129920, 108748744491770880, 9970165621984512, 614458050662400, 25497772633088, 704123822080, 12428021760, 127074304, 573440]

theorem pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 18) (gg1 18) (gg2 18) 7)) α := by
  refine pev_wsum_eq_of_packed (gg0 18) (gg1 18) (gg2 18) 7 22 Lc betac
    tauc Nmomc (by norm_num [betac]) (by norm_num [tauc]) ?_ ?_ ?_ ?_ ?_ ?_ α
  · refine rowZ_bound (gg0 18) (gg1 18) (gg2 18) 7 3 betac tauc
      (by norm_num [betac]) (by simp) (by simp) (by simp) ?_
    norm_num [gg0, gg1, gg2, l1, betac, tauc]
  · decide
  · refine wsum_bound (gg0 18) (gg1 18) (gg2 18) 7 Lc betac
      (by norm_num [Lc]) ?_
    norm_num [gg0, gg1, gg2, l1, Lc, betac]
  · decide
  · exact wsum_length_le Lc _ 0
      (qrow_entry_length_le (gg0 18) (gg1 18) (gg2 18) 3 (by simp) (by simp) (by simp) 7)
  · rfl

theorem integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 18 α t ^ 7)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 18 * (3 + α)) ^ 7) :=
  integral_moment_packed 18 7 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)

set_option maxHeartbeats 2000000 in
-- the degree-16 Bernstein identity exceeds the default budget
/-- The certificate: `17 ^ 16 * P α` is a positive combination of `αʲ (17-α)^(16-j)`. -/
lemma P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 19 / 2) :
    0 < 1996938880799635773 + 5327542416376042533 * α + 6168567333266685756 * α ^ 2 + 4015726419901684032 * α ^ 3 + 1568562341575363317 * α ^ 4 + 336439630979056719 * α ^ 5 - 5059047712773960 * α ^ 6 - 94154641040290584 * α ^ 7 + 14305270642714822 * α ^ 8 + 337895936432856 * α ^ 9 - 7990669279488 * α ^ 10 - 2592154628256 * α ^ 11 - 177335477376 * α ^ 12 - 6421337472 * α ^ 13 - 134803968 * α ^ 14 - 1555968 * α ^ 15 - 7680 * α ^ 16 := by
  have hu : (0 : ℝ) ≤ 19 - 2 * α := by linarith
  have hid : (19 : ℝ) ^ 16 * (1996938880799635773 + 5327542416376042533 * α + 6168567333266685756 * α ^ 2 + 4015726419901684032 * α ^ 3 + 1568562341575363317 * α ^ 4 + 336439630979056719 * α ^ 5 - 5059047712773960 * α ^ 6 - 94154641040290584 * α ^ 7 + 14305270642714822 * α ^ 8 + 337895936432856 * α ^ 9 - 7990669279488 * α ^ 10 - 2592154628256 * α ^ 11 - 177335477376 * α ^ 12 - 6421337472 * α ^ 13 - 134803968 * α ^ 14 - 1555968 * α ^ 15 - 7680 * α ^ 16) = 1996938880799635773 * (19 - 2 * α) ^ 16 + 165125350096733152863 * α ^ 1 * (19 - 2 * α) ^ 15 + 6222082647427442972766 * α ^ 2 * (19 - 2 * α) ^ 14 + 141355820787428498073516 * α ^ 3 * (19 - 2 * α) ^ 13 + 2157735283869217913370909 * α ^ 4 * (19 - 2 * α) ^ 12 + 23307179713209861652797525 * α ^ 5 * (19 - 2 * α) ^ 11 + 181491504176132704398182238 * α ^ 6 * (19 - 2 * α) ^ 10 + 947234591820259386271884708 * α ^ 7 * (19 - 2 * α) ^ 9 + 3056114849066116568052366478 * α ^ 8 * (19 - 2 * α) ^ 8 + 5409419472435810969555104008 * α ^ 9 * (19 - 2 * α) ^ 7 + 3773674627041183640344074704 * α ^ 10 * (19 - 2 * α) ^ 6 + 2563877062588931411214853312 * α ^ 11 * (19 - 2 * α) ^ 5 + 27502208508532453123433891776 * α ^ 12 * (19 - 2 * α) ^ 4 + 85133541744770676359382205696 * α ^ 13 * (19 - 2 * α) ^ 3 + 113617195875176526046213373440 * α ^ 14 * (19 - 2 * α) ^ 2 + 68841959775014032750000000000 * α ^ 15 * (19 - 2 * α) ^ 1 + 13908254927398975000000000000 * α ^ 16 := by
    ring
  -- The certificate checks coefficient signs. The last summand is positive for α > 0;
  -- at α = 0 the first summand is positive. The identity above checks every coefficient.
  bernstein_cert α (19 - 2 * α) using hid

set_option maxHeartbeats 2000000 in
-- clearing denominators across the batch identity exceeds the default budget
/-- **The batch `18 ≤ n ≤ 20`.** -/
theorem finite_range {n : ℕ} (h0 : 18 ≤ n) (h1 : n ≤ 20) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 19 / 2 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (20 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (20 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 18) (n := n) (n₁ := 20) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((18 : ℕ) : ℝ) - 4 = 14 by norm_num] at hb
  rw [show (14 : ℝ) / 2 = ((7 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 17) + 1 / (4 * 17 * (3 + α))
      + (1 - 2 * α / 19) ^ 2 * 20 * 19 * (20 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 17 * (3 + α)) ^ 7))
      = 1 - (1996938880799635773 + 5327542416376042533 * α + 6168567333266685756 * α ^ 2 + 4015726419901684032 * α ^ 3 + 1568562341575363317 * α ^ 4 + 336439630979056719 * α ^ 5 - 5059047712773960 * α ^ 6 - 94154641040290584 * α ^ 7 + 14305270642714822 * α ^ 8 + 337895936432856 * α ^ 9 - 7990669279488 * α ^ 10 - 2592154628256 * α ^ 11 - 177335477376 * α ^ 12 - 6421337472 * α ^ 13 - 134803968 * α ^ 14 - 1555968 * α ^ 15 - 7680 * α ^ 16) / (454875191212728 * (3 + α) ^ 8) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  exact hb.trans_lt (sub_lt_self _ (div_pos hP (by positivity)))

end B18_20

end Sendov
