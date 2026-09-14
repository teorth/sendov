import Solution

-- Exact elaborated public contracts: run against both frozen baseline objects
-- and freshly compiled candidate objects, then compare complete JSON records.
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  for name in #[`Sendov.eval_prod_at, `Sendov.eval_deriv_prod_at,
      `Sendov.half_le_re_inv_one_sub, `Sendov.boundary_reciprocal,
      `Sendov.rubinstein_one, `Sendov.sendov_boundary_one,
      `Sendov.phelps_rodriguez, `Sendov.sendov,
      `SendovConjecture.phelps_rodriguez, `SendovConjecture.sendov] do
    let some info := env.find? name | throwError "missing contract {name}"
    logInfo m!"BOUNDARY_CONTRACT {(Json.mkObj [
      ("name", toJson name.toString),
      ("levels", toJson (repr info.levelParams).pretty),
      ("type", toJson (repr info.type).pretty)]).compress}"
