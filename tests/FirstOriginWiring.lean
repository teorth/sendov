import Solution

-- The small-degree route must be a real proof consumer, not an unused import.
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let some info := env.find? `Sendov.sendov_interior | throwError "missing interior theorem"
  let some value := info.value? (allowOpaque := true) | throwError "missing interior proof"
  for target in #[`Sendov.FirstOriginSmall.first_origin_polar_six_seven,
      `Sendov.FirstOriginSmall.norm_integral_Fprod_le_of_factorization] do
    unless value.getUsedConstants.contains target do
      throwError "interior does not directly consume {target}"
    logInfo m!"FIRST_ORIGIN_INTERIOR_DIRECT {target}"
  for root in #[`SendovConjecture.sendov, `SendovConjecture.phelps_rodriguez] do
    let mut pending := [root]
    let mut visited : Std.HashSet Name := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      unless visited.contains name do
        visited := visited.insert name
        let some ci := env.find? name | throwError "missing closure declaration {name}"
        if let some v := ci.value? (allowOpaque := true) then
          for used in v.getUsedConstants do pending := used :: pending
    for target in #[`Sendov.FirstOriginSmall.first_origin_polar_six_seven,
        `Sendov.FirstOriginSmall.norm_integral_Fprod_le_of_factorization,
        `Sendov.FirstOriginBudget.near_contradiction,
        `Sendov.PaperNearClosure.near_endpoint_D,
        `Sendov.FirstOriginBudget.uniform_contradiction,
        `Sendov.PaperUniform.uniform_D] do
      unless visited.contains target do
        throwError "missing final-root consumption {root} -> {target}"
      logInfo m!"FIRST_ORIGIN_SOLUTION_VALUE {root} -> {target}"
    if visited.contains `Collinear.diameter_moment then
      throwError "real-collinear theorem unexpectedly consumed by complex Solution"
    logInfo m!"COLLINEAR_NOT_IN_SOLUTION_VALUE {root}"
