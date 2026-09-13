import Lean
import Solution
import Sendov.Common.DistillationFinite
import Sendov.LargeDegree.DistillationTailBound

/-!
Run after building the selected proof with `lake env lean scripts/axioms.lean`.
This separate audit checks the two exact public conjecture statements and their
active finite/tail seams, not retired intermediate names.

Only `propext`, `Classical.choice` and `Quot.sound` are permitted. In particular,
`sorryAx` and `Lean.ofReduceBool` are not permitted. These assertions do not
replace the complete build, kernel replay or theorem-type contract check.
-/

namespace SendovAudit
open Lean Elab Command

-- collectAxioms is transitive, including imported declarations. Check existence
-- first: collecting an unknown name alone can silently return an empty array.
syntax "#sendov_axioms " ident : command
elab_rules : command
  | `(#sendov_axioms $decl:ident) => do
    let env := (← getEnv).setExporting false
    let name := decl.getId
    unless (env.find? name).isSome do
      throwError "missing audit declaration {name}"
    let axioms ← withEnv env <| Lean.collectAxioms name
    let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
    unless axioms.all allowed.contains do
      throwError "unexpected mathematical premise in {name}: {axioms}"
    logInfo m!"SENDOV_AXIOMS {(Json.mkObj [("name", toJson name.toString),
      ("axioms", toJson (axioms.map Name.toString))]).compress}"

end SendovAudit

#sendov_axioms SendovConjecture.sendov
#sendov_axioms SendovConjecture.phelps_rodriguez
#sendov_axioms Sendov.distillFinite_components
#sendov_axioms Sendov.distillFinite_scalar
#sendov_axioms Sendov.distillFiniteTailBase
#sendov_axioms Sendov.distillComponents_lt_two_thirds
#sendov_axioms Sendov.distillScalar_lt_two_thirds
#sendov_axioms Sendov.polar_origin_incompatible
