import Lean
import Solution

open Sendov

namespace EarlierTailTest

example {m : ℕ} (hm : 5 ≤ m) : (5 ≤ m ∧ m ≤ 60) ∨ 61 ≤ m := by omega

example {m : ℕ} (hm : 5 ≤ m) (hm60 : m ≤ 60) :
    distillEBudget m + distillT0 m 0 + distillT1 m 0 + distillT2 m 0 < 199 / 200 :=
  distillFinite_components hm hm60 (by norm_num) (by positivity) (by norm_num)

example {m α : ℝ} (hm : 61 ≤ m) (hα : 0 ≤ α) (h17 : α ≤ 17) :
    distillEBudget m + distillT0 m α + distillT1 m α + distillT2 m α < 199 / 200 :=
  distillComponents_lt_199_200 hm hα h17

example {m α : ℝ} (hm : 61 ≤ m) (hα : 0 < α) (h17 : α ≤ 17) :
    scalarObstruction m α (cubicPolarEnvelope α) < 1 :=
  (distillScalar_lt_199_200 hm hα h17).trans (by norm_num)

example :
    distillEBudget 61 + distillT0 61 0 + distillT1 61 0 + distillT2 61 0 < 199 / 200 :=
  distillComponents_lt_199_200 (by norm_num) (by norm_num) (by norm_num)

example :
    scalarObstruction 61 0 (cubicPolarEnvelope 0) = 1 / 122 := by
  rw [scalarObstruction_zero]
  norm_num

example :
    distillEBudget (123 / 2) + distillT0 (123 / 2) 17 +
      distillT1 (123 / 2) 17 + distillT2 (123 / 2) 17 < 199 / 200 :=
  distillComponents_lt_199_200 (by norm_num) (by norm_num) (by norm_num)

example {n : ℕ} (hn : 6 ≤ n) {α : ℝ}
    (hα : 0 < α) (h17 : α ≤ 17) (hhalf : 2 * α ≤ M n) :
    scalarObstruction (M n) α (cubicPolarEnvelope α) < 1 :=
  distillScalar_lt_one hn hα h17 hhalf

example : scalarObstruction (M 6) (5 / 2) (cubicPolarEnvelope (5 / 2)) < 1 :=
  distillScalar_lt_one (by norm_num) (by norm_num) (by norm_num) (by norm_num [M])

example : scalarObstruction (M 61) 17 (cubicPolarEnvelope 17) < 1 :=
  distillScalar_lt_one (by norm_num) (by norm_num) (by norm_num) (by norm_num [M])

example : scalarObstruction (M 62) 17 (cubicPolarEnvelope 17) < 1 :=
  distillScalar_lt_one (by norm_num) (by norm_num) (by norm_num) (by norm_num [M])

example : scalarObstruction (M 64) 17 (cubicPolarEnvelope 17) < 1 :=
  distillScalar_lt_one (by norm_num) (by norm_num) (by norm_num) (by norm_num [M])

example : scalarObstruction (M 65) 17 (cubicPolarEnvelope 17) < 1 :=
  distillScalar_lt_one (by norm_num) (by norm_num) (by norm_num) (by norm_num [M])

open Polynomial in
example {p : ℂ[X]} (hdeg : 2 ≤ p.natDegree)
    (hzeroes : ∀ w : ℂ, p.eval w = 0 → ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ ≤ 1 :=
  SendovConjecture.sendov hdeg hzeroes hpa

open Polynomial in
example {p : ℂ[X]} (hdeg : 2 ≤ p.natDegree)
    (hzeroes : ∀ w : ℂ, p.eval w = 0 → ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    (∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ < 1) ∨
      (‖a‖ = 1 ∧ ∃ c : ℂ, c ≠ 0 ∧
        p = C c * (X ^ p.natDegree - C (a ^ p.natDegree))) :=
  SendovConjecture.phelps_rodriguez hdeg hzeroes hpa

end EarlierTailTest

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  for (consumer, targets) in #[
      (`Sendov.distillComponents_lt_199_200,
        #[`Sendov.distillComponents_le_61, `Sendov.distillFinite_61,
          `Sendov.distillFiniteBound_61]),
      (`Sendov.distillScalar_lt_199_200,
        #[`Sendov.distillScalar_le_majorant, `Sendov.distillComponents_lt_199_200]),
      (`Sendov.distillScalar_lt_one,
        #[`Sendov.distillFinite_scalar, `Sendov.distillScalar_lt_199_200]),
      (`Sendov.polar_origin_incompatible, #[`Sendov.distillScalar_lt_one]),
      (`Sendov.sendov_interior, #[`Sendov.polar_origin_incompatible]),
      (`Sendov.sendov_interior_real, #[`Sendov.sendov_interior]),
      (`Sendov.phelps_rodriguez, #[`Sendov.sendov_interior_real]),
      (`Sendov.sendov, #[`Sendov.phelps_rodriguez]),
      (`SendovConjecture.sendov, #[`Sendov.sendov]),
      (`SendovConjecture.phelps_rodriguez, #[`Sendov.phelps_rodriguez])] do
    let some info := env.find? consumer | throwError "missing declaration {consumer}"
    let some value := info.value? (allowOpaque := true) | throwError "missing proof {consumer}"
    for target in targets do
      unless value.getUsedConstants.contains target do
        throwError "not an actual proof consumer: {consumer} -> {target}"
      logInfo m!"EARLIER_TAIL_CONSUMER {consumer} -> {target}"
  for target in #[`Sendov.distillComponents_lt_199_200, `Sendov.distillScalar_lt_199_200,
      `Sendov.distillScalar_lt_one, `SendovConjecture.sendov,
      `SendovConjecture.phelps_rodriguez] do
    let axioms ← withEnv env <| Lean.collectAxioms target
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "unexpected axiom in {target}: {axioms}"
    logInfo m!"EARLIER_TAIL_AXIOMS {target}: {axioms}"

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let retired := #[
    `Sendov.distillFiniteTailBase, `Sendov.distillComponents_lt_two_thirds,
    `Sendov.distillScalar_lt_two_thirds, `Sendov.distillComponents_lt_two_thirds_of_base,
    `Sendov.distillEBudget_le_81, `Sendov.distillT0_le_81, `Sendov.distillT1_le_81,
    `Sendov.distillT2_le_81, `Sendov.distillComponents_le_81, `Sendov.distillTail_polynomial_pos,
    `Sendov.distillComponents_le_64]
  for name in retired do
    if env.contains name then throwError "retired declaration still imported: {name}"
  -- Only project values can reference project cases: earlier imported libraries
  -- cannot depend on declarations introduced later by Sendov.
  for (root, upper) in #[(`Sendov.distillFinite_components, 60),
      (`SendovConjecture.sendov, 61), (`SendovConjecture.phelps_rodriguez, 61)] do
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
            let text := used.toString
            if text.startsWith "Sendov." || text.startsWith "SendovConjecture." ||
                text.startsWith "_private.Sendov." then
              pending := used :: pending
    for m in [5:82] do
      for stem in ["distillFinite_", "distillFiniteBound_"] do
        let name := Name.str `Sendov s!"{stem}{m}"
        unless visited.contains name == (m ≤ upper) do
          throwError "wrong actual case closure: {root}, {name}"
        if 62 ≤ m && env.contains name then
          throwError "retired case still imported: {name}"
      for j in [0:3] do
        let name := Name.str (Name.str `Sendov s!"CriticalRow{m}") s!"component{j}"
        unless visited.contains name == (m ≤ upper) do
          throwError "wrong actual component closure: {root}, {name}"
        if 62 ≤ m && env.contains name then
          throwError "retired component still imported: {name}"
    for name in visited do
      let text := name.toString
      if retired.contains name || (text.splitOn "two_thirds").length > 1 ||
          (text.splitOn "_le_81").length > 1 then
        throwError "retired tail in actual value closure: {root}, {name}"
    logInfo m!"K61_VALUE_CLOSURE {root}: 5..{upper}, three components, no retired names"
