/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sendov contributors
-/
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

/-!
# Bernstein identities through homogeneous Horner form

`bernstein_ring x y` proves an equality whose right side is a homogeneous sum
of natural-coefficient monomials in `x` and `y`. It builds a Horner intermediate
in `y`, verifies the original left side against that intermediate with `ring1`,
and verifies the complete original right side after making `y` an independent
atom. The parser only suggests an intermediate: both equalities are proved by
Mathlib's proof-producing ring tactic. No evaluation point is used.
Coordinates must elaborate unambiguously in the goal's carrier; the supported
right side uses addition, multiplication, natural numerals and natural powers
of those two coordinates, with a common total degree.
-/

namespace Sendov.BernsteinRing

open Lean Meta Elab Tactic

private def binary? (e : Expr) (n : Name) : Option (Expr × Expr) :=
  if e.isAppOfArity n 6 then some (e.getArg! 4, e.getArg! 5) else none

private partial def flatten (e : Expr) (op : Name) : Array Expr :=
  match binary? e op with
  | some (a, b) => flatten a op ++ flatten b op
  | none => #[e]

private def numeral (n : Nat) : TSyntax `term := ⟨Syntax.mkNumLit (toString n)⟩

private def monomial (e x y : Expr) : TacticM (Nat × Nat × Nat) := do
  let mut c := 1
  let mut i := 0
  let mut j := 0
  for f in flatten e ``HMul.hMul do
    if ← isDefEq f x then i := i + 1
    else if ← isDefEq f y then j := j + 1
    else if f.isAppOfArity ``HPow.hPow 6 then
      let some n ← getNatValue? (f.getArg! 5)
        | throwError "bernstein_ring: expected natural exponent"
      if ← isDefEq (f.getArg! 4) x then i := i + n
      else if ← isDefEq (f.getArg! 4) y then j := j + n
      else throwError "bernstein_ring: unsupported power base"
    else if f.isAppOfArity ``OfNat.ofNat 3 then
      let some n ← getNatValue? (f.getArg! 1)
        | throwError "bernstein_ring: expected natural coefficient"
      c := c * n
    else throwError "bernstein_ring: unsupported monomial factor {f}"
  return (c, i, j)

/-- Verify the supplied equality through homogeneous Horner form; keep the statement intact. -/
elab "bernstein_ring " x:term:max y:term:max : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some (ty, _, rhs) := target.eq?
    | throwError "bernstein_ring: expected equality"
  let xe ← elabTerm x (some ty)
  let ye ← elabTerm y (some ty)
  let terms ← (flatten rhs ``HAdd.hAdd).mapM (monomial · xe ye)
  let (_, i, j) := terms[0]!
  let degree := i + j
  let mut cs := Array.replicate (degree + 1) 0
  for (c, i, j) in terms do
    unless i + j == degree do throwError "bernstein_ring: mixed total degrees"
    cs := cs.modify i (· + c)
  let mut h := numeral cs[0]!
  -- After step i, h = ∑ k ≤ i, cs[k] * x^k * y^(i-k).
  for i in [1:degree + 1] do
    h ← `($h * $y + $(numeral cs[i]!) * $x ^ $(numeral i))
  evalTactic (← `(tactic| trans $h))
  focus do evalTactic (← `(tactic| ring1))
  focus do
    let atom := mkIdent (← mkFreshUserName `bernsteinCoordinate)
    evalTactic (← `(tactic| generalize $y = $atom))
    evalTactic (← `(tactic| ring1))

end Sendov.BernsteinRing
