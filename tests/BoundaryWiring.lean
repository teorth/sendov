import Sendov.Boundary

-- This environment contract must fail against v1 before retirement/rewiring.
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  if (env.find? `Sendov.all_q_eq_one).isSome then
    throwError "retired pointwise wrapper remains: Sendov.all_q_eq_one"
  logInfo "BOUNDARY_POINTWISE_RETIRED"

-- Direct proof-value use, not merely a transitive path through the old adapter.
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let some info := env.find? `Sendov.rubinstein_one | throwError "missing rubinstein_one"
  let some value := info.value? (allowOpaque := true) | throwError "missing proof value"
  let used := value.getUsedConstants
  unless used.contains `Sendov.all_q_eq_one_of_sum_norm_sq_le do
    throwError "rubinstein_one does not directly consume average boundary rigidity"
  if used.contains `Sendov.all_q_eq_one then
    throwError "rubinstein_one still directly consumes the retired wrapper"
  logInfo "BOUNDARY_DIRECT_AVERAGE_CONSUMER"
