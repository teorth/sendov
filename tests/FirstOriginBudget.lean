import Sendov.Analytic.FirstOriginBudget

#print axioms Sendov.FirstOriginBudget.lower_budget
#print axioms Sendov.FirstOriginBudget.near_contradiction
#print axioms Sendov.FirstOriginBudget.uniform_contradiction

-- Verify proof-value independence, not merely an import or a theorem name.
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  for root in #[`Sendov.FirstOriginBudget.near_contradiction,
      `Sendov.FirstOriginBudget.uniform_contradiction,
      `Sendov.FirstOriginSmall.first_origin_polar_six_seven] do
    let mut pending := [root]
    let mut seen : Std.HashSet Name := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      unless seen.contains name do
        seen := seen.insert name
        let some ci := env.find? name | throwError "missing declaration {name}"
        if let some value := ci.value? (allowOpaque := true) then
          for used in value.getUsedConstants do pending := used :: pending
    for forbidden in #[`Sendov.second_origin_identity, `Sendov.centroid_identity,
        `Sendov.origin_exact, `Sendov.polar_origin_incompatible] do
      if seen.contains forbidden then
        throwError "unexpected old-channel dependency {root} -> {forbidden}"
    logInfo m!"FIRST_ORIGIN_ONLY {root}"
