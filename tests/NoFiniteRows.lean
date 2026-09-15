import Solution

/-! Full proof-value traversal: imported and private constants are not pruned. -/
open Sendov

example {n : ℕ} (hn : 6 ≤ n) {α : ℝ} (hα : 0 < α)
    (h17 : α ≤ 17) (hhalf : 2 * α ≤ M n) :
    scalarObstruction (M n) α (cubicPolarEnvelope α) < 1 :=
  distillScalar_lt_one hn hα h17 hhalf

example {m : ℝ} (hm : 5 ≤ m) :
    scalarObstruction m (7 / 5) (cubicPolarEnvelope (7 / 5)) < 1 :=
  distillScalar_lt_one_real hm (by norm_num) (by norm_num) (by linarith)

example {m : ℝ} (hm : 5 ≤ m) :
    scalarObstruction m 2 (cubicPolarEnvelope 2) < 1 :=
  distillScalar_lt_one_real hm (by norm_num) (by norm_num) (by linarith)

example {m : ℝ} (hm : 34 ≤ m) :
    scalarObstruction m 17 (cubicPolarEnvelope 17) < 1 :=
  distillScalar_lt_one_real (by linarith) (by norm_num) (by norm_num) (by linarith)

example {α : ℝ} (hα : 5 / 2 ≤ α) (h17 : α ≤ 17) :
    scalarObstruction (2 * α) α (cubicPolarEnvelope α) < 1 :=
  distillScalar_lt_one_real (by linarith) (by linarith) h17 le_rfl

example : scalarObstruction (11 / 2) (19 / 10) (cubicPolarEnvelope (19 / 10)) < 1 :=
  distillScalar_lt_one_real (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example (m : ℝ) : scalarObstruction m 0 (cubicPolarEnvelope 0) = 1 / (2 * m) :=
  scalarObstruction_zero m

example : ¬ 2 * (17 : ℝ) ≤ 5 := by norm_num

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let retiredModule := fun (name : Name) =>
    let text := name.toString
    text.startsWith "Sendov.DistillationFinite." ||
      text.startsWith "Sendov.LargeDegree." ||
      #["Sendov.Common.DistillationCritical", "Sendov.Common.DistillationCriticalFinite",
        "Sendov.Common.DistillationFinite", "Sendov.Common.DistillationMajorant"].contains text
  for name in env.header.moduleNames do
    if retiredModule name then throwError "retired imported module: {name}"
  for root in #[`Sendov.distillScalar_lt_one_real, `Sendov.distillScalar_lt_one,
      `SendovConjecture.sendov, `SendovConjecture.phelps_rodriguez] do
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
      if let some idx := env.getModuleIdxFor? name then
        let owner := env.header.moduleNames[idx.toNat]!
        if retiredModule owner then
          throwError "retired proof-value owner: {root} -> {name} in {owner}"
      let text := name.toString
      for forbidden in #["CriticalRow", "distillFinite", "DistillationFinite",
          "DistillationCritical", "distillCritical", "DistillationTail",
          "interval_55_61", "_le_61", "_antitone_55", "distillComponents_lt_199_200",
          "distillScalar_lt_199_200", "distillKappa_rpow_interval",
          "distillKappa_rpow_antitone", "distillT0_le_of_critical",
          "distillT1_le_of_critical", "distillT2_le_of_critical",
          "distillScalar_le_components", "distillScalar_le_majorant",
          "hasDerivAt_distillTotal", "distillScalar_lt_one_alpha_seventeen",
          "distillFiniteTailBase", "distillComponents_le_64", "_le_81",
          "distillScalar_lt_two_thirds", "distillComponents_lt_two_thirds"] do
        if (text.splitOn forbidden).length > 1 then
          throwError "retired proof-value dependency: {root} -> {name}"
    for target in #[`Sendov.distillScalar_lt_one_small_alpha,
        `Sendov.distillScalar_lt_one_middle_alpha, `Sendov.distillScalar_lt_one_peak_strip,
        `Sendov.distillScalar_le_total_sub_loss,
        `Sendov.distillScalar_le_elementary_components,
        `Sendov.PeakClosure.gap1_identity,
        `Sendov.PeakClosure.LowHomogeneous.gapH_identity,
        `Sendov.PeakClosure.HighHomogeneous.gapH_identity] do
      unless visited.contains target do
        throwError "missing positive proof consumption: {root} -> {target}"
      logInfo m!"NO_ROWS_POSITIVE {root} -> {target}"
    let axioms ← withEnv env <| Lean.collectAxioms root
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "unexpected axioms for {root}: {axioms}"
    logInfo m!"NO_ROWS_CLOSURE {root}: {visited.size}; axioms {axioms}"
    logInfo m!"NO_ROWS_PROJECT_VALUES {root}: {(visited.toArray.filter fun n =>
      n.toString.startsWith "Sendov." || n.toString.startsWith "_private.Sendov.").map
        Name.toString}"
