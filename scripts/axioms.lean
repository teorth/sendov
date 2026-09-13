import Lean
import Solution

/-!
Run after building the selected proof with `lake env lean scripts/axioms.lean`.
This separate audit checks the two exact public conjecture statements and their
active full-domain alpha estimates, not retired degree-certificate interfaces.

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
#sendov_axioms Sendov.distillScalar_lt_one_real
#sendov_axioms Sendov.distillScalar_lt_one
#sendov_axioms Sendov.polar_origin_incompatible
#sendov_axioms Sendov.scalarObstruction_zero
#sendov_axioms Sendov.distillScalar_lt_one_small_alpha
#sendov_axioms Sendov.distillScalar_lt_one_middle_alpha
#sendov_axioms Sendov.distillScalar_lt_one_alpha_le_two
#sendov_axioms Sendov.distillScalar_lt_one_peak_strip
#sendov_axioms Sendov.distillScalar_le_total_sub_loss
#sendov_axioms Sendov.distillChordTotal_lt_one
#sendov_axioms Sendov.distillScalar_le_elementary_components
#sendov_axioms Sendov.distillScalar_le_rationalPeak
#sendov_axioms Sendov.distillRationalPeak_lt_one
#sendov_axioms Sendov.PeakClosure.gap1_identity
#sendov_axioms Sendov.PeakClosure.LowHomogeneous.gapH_identity
#sendov_axioms Sendov.PeakClosure.HighHomogeneous.gapH_identity
