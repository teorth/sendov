import scripts.axioms

#sendov_axioms Sendov.sum_norm_sub_one_sq
#sendov_axioms Sendov.all_eq_one_of_sum_norm_sq_le_card
#sendov_axioms Sendov.all_q_eq_one_of_sum_norm_sq_le
#sendov_axioms Sendov.rubinstein_one
#sendov_axioms Sendov.sendov_boundary_one

-- Follow actual proof values, including opaque and private declarations, using
-- the repository's tests/NoFiniteRows.lean traversal pattern. A type reference
-- alone is deliberately not accepted as evidence of consumption.
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let targets := #[`Sendov.rubinstein_one,
    `Sendov.all_q_eq_one_of_sum_norm_sq_le, `Sendov.all_eq_one_of_sum_norm_sq_le_card,
    `Sendov.sum_norm_sub_one_sq]
  for name in targets do
    unless (env.find? name).isSome do throwError "missing boundary target {name}"
  for root in #[`SendovConjecture.sendov, `SendovConjecture.phelps_rodriguez] do
    let mut pending := [root]
    let mut visited : Std.HashSet Name := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      unless visited.contains name do
        visited := visited.insert name
        let some info := env.find? name | throwError "missing closure declaration {name}"
        if let some value := info.value? (allowOpaque := true) then
          for used in value.getUsedConstants do
            pending := used :: pending
    for target in targets do
      unless visited.contains target do
        throwError "missing actual boundary consumption: {root} -> {target}"
      logInfo m!"BOUNDARY_VALUE {root} -> {target}"
    if visited.contains `Sendov.all_q_eq_one then
      throwError "retired pointwise wrapper consumed by {root}"
    logInfo m!"BOUNDARY_NO_RETIRED_VALUE {root}"
    logInfo m!"BOUNDARY_CLOSURE {root}: {visited.size}"
  for retired in #[`Sendov.all_q_eq_one, `Sendov.eq_one_of_re_eq_one_of_norm_le_one,
      `Sendov.eq_zero_of_sum_eq_zero, `Sendov.sum_le_card_mul,
      `Sendov.card_mul_le_sum, `Sendov.sum_map_one_sub_re] do
    if (env.find? retired).isSome then throwError "retired boundary helper remains: {retired}"
  logInfo "BOUNDARY_RETIRED_ABSENT"
