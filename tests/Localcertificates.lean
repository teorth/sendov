import Sendov.Common.BernsteinList
import Sendov.Common.DistillationFinite

namespace Localcertificates

open BernsteinCert Sendov

example (cs : List ℕ) (i : ℕ) (x y : ℝ) :
    (coeffTree cs i).eval x y = x ^ i * (coeffTree cs 0).eval x y :=
  coeffTree_eval_shift cs i x y

example (c : ℕ) (cs : List ℕ) (x y : ℝ) :
    (coeffTree (c :: cs) 0).eval x y =
      (c : ℝ) * y ^ cs.length + x * (coeffTree cs 0).eval x y :=
  coeffTree_eval_cons c cs x y

example (x y : ℝ) : (coeffTree [] 0).eval x y = 0 :=
  coeffTree_eval_nil x y

example (x y : ℝ) : (coeffTree [7] 0).eval x y = 7 := by
  simp only [coeffTree_eval_cons, coeffTree_eval_nil, List.length_nil, Nat.cast_ofNat]
  ring1

example (x y : ℝ) : (coeffTree [2, 0, 3] 0).eval x y = 2 * y ^ 2 + 3 * x ^ 2 := by
  simp only [coeffTree_eval_cons, coeffTree_eval_nil,
    List.length_cons, List.length_nil, Nat.cast_ofNat]
  ring1

example : (coeffTree [2, 0, 3] 0).eval 0 1 = 2 ∧
    (coeffTree [2, 0, 3] 0).eval 1 0 = 3 := by
  norm_num [coeffTree_eval_cons, coeffTree_eval_nil]

example : (coeffTree [] 0).edge true = false ∧
    (coeffTree [] 0).edge false = false := by decide

example : (coeffTree [0, 1] 0).edge true = false ∧
    (coeffTree [1, 0] 0).edge false = false := by decide

example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : 0 < x ^ 2 + (1 - x) ^ 2 := by
  refine coeffs_pos [1, 0, 1] (lo := 0) (hi := 1) (s := 1)
    (by norm_num) (by norm_num) hx (by decide) (by decide) ?_
  simp only [coeffTree_eval_cons, coeffTree_eval_nil,
    List.length_cons, List.length_nil]
  ring1

theorem critical0_identity (x : ℝ) :
    117649 * -distillCritical0 5 x =
      (coeffTree [3667054680, 133443712440, 939063315600, 3006831250944,
        5267101731840, 5254197895040, 2819499598080, 635350144000] 0).eval
        (x - 3 / 4) (5 / 2 - x) := by
  unfold distillCritical0
  simp only [coeffTree_eval_cons, coeffTree_eval_nil,
    List.length_cons, List.length_nil, Nat.cast_ofNat]
  ring1

theorem critical1_identity (x : ℝ) :
    4782969 * distillCritical1 5 x =
      (coeffTree [12259473776, 1574964910352, 13907088807648, 52400775960064,
        105639358896640, 119707352275200, 72226624540160, 18128870144000] 0).eval
        (x - 1 / 4) (5 / 2 - x) := by
  unfold distillCritical1
  simp only [coeffTree_eval_cons, coeffTree_eval_nil,
    List.length_cons, List.length_nil, Nat.cast_ofNat]
  ring1

theorem critical2_identity (x : ℝ) :
    -distillCritical2 5 x =
      (coeffTree [129600, 462240, 574680, 277028, 34872] 0).eval (x - 0) (1 / 2 - x) := by
  unfold distillCritical2
  simp only [coeffTree_eval_cons, coeffTree_eval_nil,
    List.length_cons, List.length_nil, Nat.cast_ofNat]
  ring1

example (x : ℝ) (hx : x ∈ Set.Icc 0 (1 / 2)) : 0 < -distillCritical2 5 x := by
  exact coeffs_pos [129600, 462240, 574680, 277028, 34872]
    (lo := 0) (hi := 1 / 2) (s := 1) (by norm_num) (by norm_num)
    hx (by decide) (by decide) (by simpa only [one_mul] using critical2_identity x)

-- A changed interior coefficient preserves both endpoint values and supports.
-- The complete identity must still fail, not merely a frontend shape check.
example (x : ℝ) : x = x := by
  fail_if_success
    have h : -distillCritical2 5 x =
        (coeffTree [129600, 462240, 574681, 277028, 34872] 0).eval
          (x - 0) (1 / 2 - x) := by
      unfold distillCritical2
      simp only [coeffTree_eval_cons, coeffTree_eval_nil,
        List.length_cons, List.length_nil, Nat.cast_ofNat]
      ring1
  rfl

example : (coeffTree [129600, 462240, 574681, 277028, 34872] 0).edge true = true ∧
    (coeffTree [129600, 462240, 574681, 277028, 34872] 0).edge false = true := by decide

example : ¬ (∀ x : ℝ, -distillCritical2 5 x =
    (coeffTree [129600, 462240, 574681, 277028, 34872] 0).eval (x - 0) (1 / 2 - x)) := by
  intro h
  have hq := h (1 / 4)
  norm_num [distillCritical2, coeffTree, Cert.eval] at hq

example (x : ℝ) : x = x := by
  fail_if_success
    have h : 2 * -distillCritical2 5 x =
        (coeffTree [129600, 462240, 574680, 277028, 34872] 0).eval
          (x - 0) (1 / 2 - x) := by
      unfold distillCritical2
      simp only [coeffTree_eval_cons, coeffTree_eval_nil,
        List.length_cons, List.length_nil, Nat.cast_ofNat]
      ring1
  fail_if_success
    have h : -distillCritical2 5 x =
        (coeffTree [34872, 277028, 574680, 462240, 129600] 0).eval
          (x - 0) (1 / 2 - x) := by
      unfold distillCritical2
      simp only [coeffTree_eval_cons, coeffTree_eval_nil,
        List.length_cons, List.length_nil, Nat.cast_ofNat]
      ring1
  fail_if_success
    have h : -distillCritical2 5 x =
        (coeffTree [129600, 462240, 574680, 277028] 0).eval (x - 0) (1 / 2 - x) := by
      unfold distillCritical2
      simp only [coeffTree_eval_cons, coeffTree_eval_nil,
        List.length_cons, List.length_nil, Nat.cast_ofNat]
      ring1
  fail_if_success
    have h : -distillCritical2 5 x =
        (coeffTree [129600, 462240, 574680, 277028, 34872] 0).eval (x - 0) (3 / 4 - x) := by
      unfold distillCritical2
      simp only [coeffTree_eval_cons, coeffTree_eval_nil,
        List.length_cons, List.length_nil, Nat.cast_ofNat]
      ring1
  rfl

example (x y : ℝ) : (x + y) ^ 2 = y ^ 2 + 2 * x * y + x ^ 2 := by
  bernstein_ring x y

example (α : ℝ) (hα : 0 ≤ α) (hd : α ≤ 5 / 2) :
    distillT1 5 α ≤ 191 / 1000 :=
  CriticalRow5.component1 α hα hd

example (α : ℝ) (hα : 0 ≤ α) (hd : α ≤ 17) :
    distillT1 46 α ≤ 153 / 1000 :=
  CriticalRow46.component1 α hα hd

example (α : ℝ) (hα : 0 ≤ α) (hd : α ≤ 17) :
    distillT0 61 α ≤ 57 / 250 ∧ distillT1 61 α ≤ 13 / 250 ∧
      distillT2 61 α ≤ 81 / 250 :=
  ⟨CriticalRow61.component0 α hα hd, CriticalRow61.component1 α hα hd,
    CriticalRow61.component2 α hα hd⟩

example {m : ℕ} (hm : 5 ≤ m) (hm60 : m ≤ 60) {α : ℝ} (hα : 0 ≤ α)
    (hαm : α ≤ (m : ℝ) / 2) (h17 : α ≤ 17) :
    distillEBudget m + distillT0 m α + distillT1 m α + distillT2 m α < 199 / 200 :=
  distillFinite_components hm hm60 hα hαm h17

example {m : ℕ} (hm : 5 ≤ m) (hm60 : m ≤ 60) {α : ℝ} (hα : 0 < α)
    (hαm : α ≤ (m : ℝ) / 2) (h17 : α ≤ 17) :
    scalarObstruction m α (cubicPolarEnvelope α) < 199 / 200 :=
  distillFinite_scalar hm hm60 hα hαm h17

example : distillEBudget 61 + distillT0 61 17 + distillT1 61 17 + distillT2 61 17 <
    199 / 200 :=
  (distillFinite_61 17 (by norm_num) le_rfl).trans_lt distillFiniteBound_61

end Localcertificates
