/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.FiniteRange.Batch
import Sendov.FiniteRange.PackBridge
import Sendov.Common.BernsteinCert

/-!
# The batch 22 to 24

`Sendov.R_le_batch` bounds every `R n α` for `22 ≤ n ≤ 24` by the elementary part and
moment at `n₀ = 22` together with the prefactor at `n₁ = 24`, so one moment and one
certificate serve all 3 degrees.  The certificate has degree 20, set by `n₀` rather
than `n₁`.

Feasibility at `n₀` is proved rather than assumed: for `n ≥ 36` it follows from
`0 ≤ α ≤ 17`, since `A - c²` increases with `n`.  This matters because feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`.
-/

-- Generated numerals cannot be wrapped, so the long-line linter is off in this file.
set_option linter.style.longLine false
set_option maxRecDepth 4000000

namespace Sendov

namespace B22_24

lemma M_lo : M 22 = 21 := by norm_num [M]

lemma M_hi : M 24 = 23 := by norm_num [M]

lemma A_lo (α : ℝ) : A 22 α = 1 - 2 * α / 21 := by rw [A, M]; push_cast; ring

lemma A_hi (α : ℝ) : A 24 α = 1 - 2 * α / 23 := by rw [A, M]; push_cast; ring

lemma c_lo {α : ℝ} (hα : 0 ≤ α) : c 22 α = (126 + 15 * α - 2 * α ^ 2) / (42 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring

/-- `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
which for `n₀ < 36` does not follow from `α ≤ 17`. -/
lemma c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 23 / 2) : 0 ≤ c 22 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

def Lc : ℤ := 232792560

def betac : ℤ := 5774500618193131865874939367342081

def tauc : ℤ := 52113403406617399568675768890198434300892440730552860468456457359822812916403957981341978999482593278271409269805645884496135649846419759057009193613300612144616769946235123570814826138813253665092373673643274802319253928901325155969193585802030603998557856484812350076171944041251538965089353404668598911589180101281800066659429973404184827536244361717247282601231552544467258823560691375175811619171316787642443135211274745052812281973726028703612636651711022615997355506630751683900551998989656240038929214649085265235953918608516395993601881499081882159387466173626361142174157279677614740584272959889365094896808211158507170847555638174887653568352512765279104934288526037600114288775668310037707312009671168290779571054910498924756815599827889354729460340914561182011034734511085509420346820352631874830950754461420175060450633533746353185246669199140615772136375726619739932952117888587198162177055098653469266065620379085335980107485574263048810931409342867852289

/-- The moment numerator at `n₀ = 22`, `k = 9`. -/
def Nmomc : List ℤ :=
  [63683904221147656083456, 258124956324931816114176, 484131886524725672024064, 558778379485145387968512, 446247743318805044026368, 264110065181693649515520, 122458189294350124959744, 47704848438469830322176, 18201381357540629025792, 13524983241127074966528, 1177792095898695426048, 74548634146090795008, 3411779294798364672, 112771637948841984, 2668046408810496, 44104655831040, 484339875840, 3177971712, 9437184]

theorem pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 22) (gg1 22) (gg2 22) 9)) α := by
  refine pev_wsum_eq_of_packed (gg0 22) (gg1 22) (gg2 22) 9 28 Lc betac
    tauc Nmomc (by norm_num [betac]) (by norm_num [tauc]) ?_ ?_ ?_ ?_ ?_ ?_ α
  · refine rowZ_bound (gg0 22) (gg1 22) (gg2 22) 9 3 betac tauc
      (by norm_num [betac]) (by simp) (by simp) (by simp) ?_
    norm_num [gg0, gg1, gg2, l1, betac, tauc]
  · decide
  · refine wsum_bound (gg0 22) (gg1 22) (gg2 22) 9 Lc betac
      (by norm_num [Lc]) ?_
    norm_num [gg0, gg1, gg2, l1, Lc, betac]
  · decide
  · exact wsum_length_le Lc _ 0
      (qrow_entry_length_le (gg0 22) (gg1 22) (gg2 22) 3 (by simp) (by simp) (by simp) 9)
  · rfl

theorem integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 22 α t ^ 9)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 22 * (3 + α)) ^ 9) :=
  integral_moment_packed 22 9 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)

set_option maxHeartbeats 2000000 in
-- the degree-20 Bernstein identity exceeds the default budget
/-- The certificate: `17 ^ 20 * P α` is a positive combination of `αʲ (17-α)^(20-j)`. -/
lemma P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 23 / 2) :
    0 < 72676691260477709153931 + 243335498910644300539743 * α + 365647629606098581621152 * α ^ 2 + 324203560761134112575706 * α ^ 3 + 187220150267586036026391 * α ^ 4 + 72995868351568741088853 * α ^ 5 + 18997181712653091143742 * α ^ 6 + 2912276075526675669294 * α ^ 7 - 47524187765551795452 * α ^ 8 - 572344038827543054862 * α ^ 9 + 60958599043408078986 * α ^ 10 + 1608150216459380292 * α ^ 11 + 37160884428953616 * α ^ 12 - 4770728942909184 * α ^ 13 - 508194774105984 * α ^ 14 - 24843494479104 * α ^ 15 - 745526594304 * α ^ 16 - 14490071808 * α ^ 17 - 179034112 * α ^ 18 - 1285120 * α ^ 19 - 4096 * α ^ 20 := by
  have hu : (0 : ℝ) ≤ 23 - 2 * α := by linarith
  have hid : (23 : ℝ) ^ 20 * (72676691260477709153931 + 243335498910644300539743 * α + 365647629606098581621152 * α ^ 2 + 324203560761134112575706 * α ^ 3 + 187220150267586036026391 * α ^ 4 + 72995868351568741088853 * α ^ 5 + 18997181712653091143742 * α ^ 6 + 2912276075526675669294 * α ^ 7 - 47524187765551795452 * α ^ 8 - 572344038827543054862 * α ^ 9 + 60958599043408078986 * α ^ 10 + 1608150216459380292 * α ^ 11 + 37160884428953616 * α ^ 12 - 4770728942909184 * α ^ 13 - 508194774105984 * α ^ 14 - 24843494479104 * α ^ 15 - 745526594304 * α ^ 16 - 14490071808 * α ^ 17 - 179034112 * α ^ 18 - 1285120 * α ^ 19 - 4096 * α ^ 20) = 72676691260477709153931 * (23 - 2 * α) ^ 20 + 8503784125363927278571329 * α ^ 1 * (23 - 2 * α) ^ 19 + 461337107467492327306312350 * α ^ 2 * (23 - 2 * α) ^ 18 + 15398943675157072979676921186 * α ^ 3 * (23 - 2 * α) ^ 17 + 353905086689575653155085657243 * α ^ 4 * (23 - 2 * α) ^ 16 + 5938058763785413089179396251875 * α ^ 5 * (23 - 2 * α) ^ 15 + 75246714147642299181739714271832 * α ^ 6 * (23 - 2 * α) ^ 14 + 734384442923791787182437424591542 * α ^ 7 * (23 - 2 * α) ^ 13 + 5562914983973677901584481691318984 * α ^ 8 * (23 - 2 * α) ^ 12 + 31773805113877239761694178561183806 * α ^ 9 * (23 - 2 * α) ^ 11 + 130856587563539007907893649077192702 * α ^ 10 * (23 - 2 * α) ^ 10 + 369427721563914607645637465073374604 * α ^ 11 * (23 - 2 * α) ^ 9 + 659851634553627022861170989844737856 * α ^ 12 * (23 - 2 * α) ^ 8 + 615817039503279914009940077569822464 * α ^ 13 * (23 - 2 * α) ^ 7 + 195270527269368587749778342774288064 * α ^ 14 * (23 - 2 * α) ^ 6 + 857988173853242270013037467185126784 * α ^ 15 * (23 - 2 * α) ^ 5 + 4220624235641254987215180793015588608 * α ^ 16 * (23 - 2 * α) ^ 4 + 8094967304722603824961003917794419968 * α ^ 17 * (23 - 2 * α) ^ 3 + 7807057971748984716263131834792835072 * α ^ 18 * (23 - 2 * α) ^ 2 + 3677240872883486972453388075862686720 * α ^ 19 * (23 - 2 * α) ^ 1 + 610286593660503076943530707277762560 * α ^ 20 := by
    ring
  -- The certificate checks coefficient signs. The last summand is positive for α > 0;
  -- at α = 0 the first summand is positive. The identity above checks every coefficient.
  bernstein_cert α (23 - 2 * α) using hid

set_option maxHeartbeats 2000000 in
-- clearing denominators across the batch identity exceeds the default budget
/-- **The batch `22 ≤ n ≤ 24`.** -/
theorem finite_range {n : ℕ} (h0 : 22 ≤ n) (h1 : n ≤ 24) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 23 / 2 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (24 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (24 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 22) (n := n) (n₁ := 24) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((22 : ℕ) : ℝ) - 4 = 18 by norm_num] at hb
  rw [show (18 : ℝ) / 2 = ((9 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 21) + 1 / (4 * 21 * (3 + α))
      + (1 - 2 * α / 23) ^ 2 * 24 * 23 * (24 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 21 * (3 + α)) ^ 9))
      = 1 - (72676691260477709153931 + 243335498910644300539743 * α + 365647629606098581621152 * α ^ 2 + 324203560761134112575706 * α ^ 3 + 187220150267586036026391 * α ^ 4 + 72995868351568741088853 * α ^ 5 + 18997181712653091143742 * α ^ 6 + 2912276075526675669294 * α ^ 7 - 47524187765551795452 * α ^ 8 - 572344038827543054862 * α ^ 9 + 60958599043408078986 * α ^ 10 + 1608150216459380292 * α ^ 11 + 37160884428953616 * α ^ 12 - 4770728942909184 * α ^ 13 - 508194774105984 * α ^ 14 - 24843494479104 * α ^ 15 - 745526594304 * α ^ 16 - 14490071808 * α ^ 17 - 179034112 * α ^ 18 - 1285120 * α ^ 19 - 4096 * α ^ 20) / (1789880961368575530 * (3 + α) ^ 10) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  exact hb.trans_lt (sub_lt_self _ (div_pos hP (by positivity)))

end B22_24

end Sendov
