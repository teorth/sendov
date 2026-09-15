import Sendov.Analytic.FirstOriginSmall

/-! Metadata-only audit adapted from the frozen tests/NoFiniteRows.lean traversal.
Every reachable proof value is followed, including private and imported constants.
This module contributes no mathematical assumptions. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  for (root, required) in #[
      (`Sendov.FirstOriginSmall.first_origin_polar_six_seven,
        #[`Sendov.one_le_tri, `Sendov.one_le_integral_Ppolar,
          `Sendov.FirstOriginSmall.polar_mean_gt_half_add_one,
          `Sendov.FirstOriginSmall.direct_budget_five,
          `Sendov.FirstOriginSmall.direct_budget_six,
          `Sendov.FirstOriginSmall.five_halves_majorant,
          `Sendov.FirstOriginSmall.fifth_sixth_majorant,
          `Sendov.FirstOriginSmall.integral_quadratic_cube,
          `Sendov.FirstOriginSmall.norm_Fprod_le]),
      (`Sendov.FirstOriginSmall.norm_integral_Fprod_le_of_factorization,
        #[`Sendov.first_origin_identity,
          `Sendov.FirstOriginSmall.norm_integral_Fprod_le_of_first_origin])] do
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
    for name in visited do
      let text := name.toString
      for forbidden in #["centroid_identity", "second_origin_identity", "origin_exact",
          "alpha_le_seventeen", "OriginExact", "Jsum", "scalarObstruction",
          "distillScalar", "Distillation", "polar_origin_incompatible", "Worigin",
          "sorryAx", "native_decide"] do
        if (text.splitOn forbidden).length > 1 then
          throwError "forbidden proof-value dependency: {root} -> {name}"
      if let some idx := env.getModuleIdxFor? name then
        let owner := env.header.moduleNames[idx.toNat]!.toString
        for forbidden in #["OriginExact", "Jsum", "Distillation", "LargeDegree",
            "Reduction.Contradiction", "Reduction.Scalar", "Interior"] do
          if (owner.splitOn forbidden).length > 1 then
            throwError "forbidden proof-value owner: {root} -> {name} in {owner}"
    for target in required do
      unless visited.contains target do
        throwError "missing positive proof consumption: {root} -> {target}"
      logInfo m!"FIRST_ORIGIN_POSITIVE {root} -> {target}"
    let axioms ← withEnv env <| Lean.collectAxioms root
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "unexpected axioms for {root}: {axioms}"
    logInfo m!"FIRST_ORIGIN_CLOSURE {root}: {visited.size}; axioms {axioms}"
    logInfo m!"FIRST_ORIGIN_PROJECT_VALUES {root}: {(visited.toArray.filter fun n =>
      n.toString.startsWith "Sendov." || n.toString.startsWith "_private.Sendov.").map
        Name.toString}"

#print axioms Sendov.FirstOriginSmall.first_origin_polar_six_seven
#print axioms Sendov.FirstOriginSmall.norm_integral_Fprod_le_of_first_origin
#print axioms Sendov.FirstOriginSmall.norm_integral_Fprod_le_of_factorization
