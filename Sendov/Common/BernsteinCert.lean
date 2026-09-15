import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace BernsteinCert
/-- An addition tree of natural-coefficient bivariate monomials. -/
inductive Cert where
  | mono (c i j : ℕ)
  | add (a b : Cert)

def Cert.eval : Cert → ℝ → ℝ → ℝ
  | .mono c i j, x, y => (c : ℝ) * x^i * y^j
  | .add a b, x, y => a.eval x y + b.eval x y

/-- `true` selects a positive pure-y term; `false` selects a positive pure-x term. -/
def Cert.edge (left : Bool) : Cert → Bool
  | .mono c i j => (0 < c) && ((if left then i else j) == 0)
  | .add a b => a.edge left || b.edge left

theorem Cert.nonneg (a : Cert) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ a.eval x y := by
  induction a with
  | mono c i j =>
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg c) (pow_nonneg hx i))
      (pow_nonneg hy j)
  | add a b ha hb => exact add_nonneg ha hb

theorem Cert.pos_left (a : Cert) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y)
    (h : a.edge true = true) : 0 < a.eval x y := by
  induction a with
  | mono c i j =>
    simp only [edge, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h
    rcases h with ⟨hc, rfl⟩
    simpa only [eval, pow_zero, mul_one] using
      mul_pos (Nat.cast_pos.mpr hc : (0 : ℝ) < c) (pow_pos hy j)
  | add a b ha hb =>
    simp only [edge, Bool.or_eq_true] at h
    rcases h with h | h
    · exact add_pos_of_pos_of_nonneg (ha h) (b.nonneg hx hy.le)
    · exact add_pos_of_nonneg_of_pos (a.nonneg hx hy.le) (hb h)

theorem Cert.pos_right (a : Cert) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (h : a.edge false = true) : 0 < a.eval x y := by
  induction a with
  | mono c i j =>
    simp only [edge, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h
    rcases h with ⟨hc, rfl⟩
    simpa only [eval, pow_zero, mul_one] using
      mul_pos (Nat.cast_pos.mpr hc : (0 : ℝ) < c) (pow_pos hx i)
  | add a b ha hb =>
    simp only [edge, Bool.or_eq_true] at h
    rcases h with h | h
    · exact add_pos_of_pos_of_nonneg (ha h) (b.nonneg hx.le hy)
    · exact add_pos_of_nonneg_of_pos (a.nonneg hx.le hy) (hb h)

/-- The reusable core: nonnegative coordinates with positive sum and both endpoint supports. -/
theorem Cert.pos (a : Cert) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : 0 < x + y) (hl : a.edge true = true) (hr : a.edge false = true) :
    0 < a.eval x y := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · exact a.pos_left le_rfl (by simpa only [zero_add] using hxy) hl
  · exact a.pos_right hx hy hr

theorem scaled_pos (a : Cert) {x y s P : ℝ}
    (hid : s * P = a.eval x y) (hs : 0 < s) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : 0 < x + y) (hl : a.edge true = true) (hr : a.edge false = true) : 0 < P := by
  have hp : 0 < s * P := hid.symm ▸ a.pos hx hy hxy hl hr
  exact (mul_pos_iff_of_pos_left hs).mp hp

open Lean Meta Elab Tactic
-- Heterogeneous operation notation has six arguments; its last two are the operands.
private def binary? (e : Expr) (n : Name) : Option (Expr × Expr) :=
  if e.isAppOfArity n 6 then some (e.getArg! 4, e.getArg! 5) else none

private partial def factors (e : Expr) : Array Expr :=
  match binary? e ``HMul.hMul with
  | some (a,b) => factors a ++ factors b
  | none => #[e]

private def natSyntax (n : Nat) : TSyntax `term := ⟨Syntax.mkNumLit (toString n)⟩

-- Homogeneity is a frontend restriction; the soundness theorem also covers mixed degrees.
private partial def reify (e x y : Expr) : TacticM (TSyntax `term × Nat) := do
  if let some (a,b) := binary? e ``HAdd.hAdd then
    let (ca, da) ← reify a x y
    let (cb, db) ← reify b x y
    unless da == db do throwError "bernstein_cert: mixed total degrees {da} and {db}"
    return (← `(Cert.add $ca $cb), da)
  let mut c := 1
  let mut i := 0
  let mut j := 0
  let mut seenC := false
  for f in factors e do
    if ← isDefEq f x then i := i+1
    else if ← isDefEq f y then j := j+1
    else if f.isAppOfArity ``HPow.hPow 6 then
      let base := f.getArg! 4
      let some n ← getNatValue? (f.getArg! 5)
        | throwError "bernstein_cert: exponent must be numeral"
      if ← isDefEq base x then i := i+n
      else if ← isDefEq base y then j := j+n
      else throwError "bernstein_cert: unknown power base"
    else
      unless f.isAppOfArity ``OfNat.ofNat 3 do
        throwError "bernstein_cert: coefficient must be a natural numeral, got {f}"
      let some n ← getNatValue? (f.getArg! 1)
        | throwError "bernstein_cert: invalid numeral"
      if seenC then throwError "bernstein_cert: multiple coefficients unsupported"
      c := n
      seenC := true
  return (← `(Cert.mono $(natSyntax c) $(natSyntax i) $(natSyntax j)), i+j)

elab "bernstein_cert " x:term:max y:term:max " using " hid:term : tactic => withMainContext do
  let xe ← elabTerm x (some (mkConst ``Real))
  let ye ← elabTerm y (some (mkConst ``Real))
  let he ← elabTerm hid none
  let ht ← inferType he
  unless ht.isAppOfArity ``Eq 3 do throwError "bernstein_cert: expected equality"
  let lhs := ht.getArg! 1
  let some (s, _) := binary? lhs ``HMul.hMul
    | throwError "bernstein_cert: identity LHS must be scale * target"
  let (c, _) ← reify (ht.getArg! 2) xe ye
  let st ← Term.exprToSyntax s
  evalTactic (← `(tactic|
    refine BernsteinCert.scaled_pos $c (x := $x) (y := $y) (s := $st)
      ?_ ?_ ?_ ?_ ?_ (by decide) (by decide)))
  focus do
    let h := mkIdent (← mkFreshUserName `hBernsteinIdentity)
    evalTactic (← `(tactic| have $h := $hid))
    -- Normalize the identity and certificate once; reflexive goals need no `exact`.
    evalTactic (← `(tactic| simp only [Cert.eval, Nat.cast_ofNat, Nat.cast_zero,
      Nat.cast_one, pow_zero, pow_one, mul_one, one_mul, mul_assoc] at $h ⊢))
    unless (← getGoals).isEmpty do
      evalTactic (← `(tactic| exact $h))
  evalTactic (← `(tactic| all_goals first | assumption | positivity | linarith))

end BernsteinCert
