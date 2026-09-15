import Sendov.Analytic.FirstOriginMargins

/-! Expanded-signature regression tests: no named predicate conceals an assumption.
The norm is of the entire complex multiple of the actual product integral.
No first-origin identity, no polynomial data, and no upper bound on this norm.
-/
namespace Sendov.FirstOriginMargins.Tests

/-- Full expanded six-degree statement, including the definition of Fprod. -/
theorem six_expanded
    (a : ℝ) (q : Multiset ℂ)
    (ha0 : 0 < a) (ha1 : a < 1)
    (hqcard : q.card = 5)
    (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    1 + (3 / 40 : ℝ) * (1 - a) ≤
      ‖(6 : ℂ) * (∫ t in (0 : ℝ)..1,
        (q.map (fun v => 1 - (a : ℂ) * (t : ℂ) * v)).prod)‖ := by
  exact norm_J_six ha0 ha1 hqcard hq1 hstar

/-- Full expanded seven-degree statement, including the definition of Fprod. -/
theorem seven_expanded
    (a : ℝ) (q : Multiset ℂ)
    (ha0 : 0 < a) (ha1 : a < 1)
    (hqcard : q.card = 6)
    (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    1 + (31 / 160 : ℝ) * (1 - a) ≤
      ‖(7 : ℂ) * (∫ t in (0 : ℝ)..1,
        (q.map (fun v => 1 - (a : ℂ) * (t : ℂ) * v)).prod)‖ := by
  exact norm_J_seven ha0 ha1 hqcard hq1 hstar

-- The scalar inequalities also retain the actual integral, rather than U5 or U6.
example {a x : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hx : (1 + a) / 2 ≤ x) (hx1 : x ≤ 1) :
    QQ (a * x) (a ^ 2) 1 ^ (5 / 2 : ℝ) + 5 * a ^ 2 *
      (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (2 : ℕ)) ≤
        1 - 5 * a / 6 - a * (1 - a) / 16 := by
  have h := T_five_gap ha0 ha1 hx hx1
  norm_num [T, Real.rpow_natCast] at h
  exact h

example {a x : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hx : (1 + a) / 2 ≤ x) (hx1 : x ≤ 1) :
    QQ (a * x) (a ^ 2) 1 ^ (3 : ℕ) + 6 * a ^ 2 *
      (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (5 / 2 : ℝ)) ≤
        1 - 6 * a / 7 - (93 / 560) * a * (1 - a) := by
  have h := T_six_gap ha0 ha1 hx hx1
  norm_num [T, Real.rpow_natCast] at h
  exact h

-- Endpoint values are valid for the polynomial certificates (unlike final a-domain).
example : 1 / 16 ≤ A5 0 := A5_lower (by norm_num) (by norm_num)
example : 1 / 16 ≤ A5 1 := A5_lower (by norm_num) (by norm_num)
example : 93 / 560 ≤ A6 0 := A6_lower (by norm_num) (by norm_num)
example : 93 / 560 ≤ A6 1 := A6_lower (by norm_num) (by norm_num)

end Sendov.FirstOriginMargins.Tests

#check @Sendov.FirstOriginMargins.Tests.six_expanded
#check @Sendov.FirstOriginMargins.Tests.seven_expanded
#check @Sendov.FirstOriginMargins.norm_J_lower

#print axioms Sendov.FirstOriginMargins.A5_lower
#print axioms Sendov.FirstOriginMargins.A6_lower
#print axioms Sendov.FirstOriginMargins.T_five_gap
#print axioms Sendov.FirstOriginMargins.T_six_gap
#print axioms Sendov.FirstOriginMargins.lower_budget_norm
#print axioms Sendov.FirstOriginMargins.norm_J_lower
#print axioms Sendov.FirstOriginMargins.norm_J_six
#print axioms Sendov.FirstOriginMargins.norm_J_seven

/-! Traverse all reachable proof values, including imported/private ones. Verify
positive use of the quantitative certificates and prohibit the old contradiction
and first-origin-bound consumers. Standard logical axioms are the only allowlist.
-/
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  for (root, required) in #[
      (`Sendov.FirstOriginMargins.norm_J_six,
        #[`Sendov.FirstOriginMargins.A5_remainder,
          `Sendov.FirstOriginMargins.A5_lower,
          `Sendov.FirstOriginMargins.upper_five_gap_identity,
          `Sendov.FirstOriginMargins.T_five_gap,
          `Sendov.FirstOriginMargins.lower_budget_norm,
          `Sendov.FirstOriginSmall.polar_mean_gt_half_add_one,
          `Sendov.one_le_integral_Ppolar, `Sendov.one_le_tri,
          `Sendov.FirstOriginSmall.norm_Fprod_le]),
      (`Sendov.FirstOriginMargins.norm_J_seven,
        #[`Sendov.FirstOriginMargins.A6_remainder,
          `Sendov.FirstOriginMargins.A6_lower,
          `Sendov.FirstOriginMargins.upper_six_gap_identity,
          `Sendov.FirstOriginMargins.T_six_gap,
          `Sendov.FirstOriginMargins.lower_budget_norm,
          `Sendov.FirstOriginSmall.five_halves_majorant,
          `Sendov.FirstOriginSmall.polar_mean_gt_half_add_one,
          `Sendov.one_le_integral_Ppolar, `Sendov.one_le_tri,
          `Sendov.FirstOriginSmall.norm_Fprod_le]),
      (`Sendov.FirstOriginMargins.norm_J_lower,
        #[`Sendov.FirstOriginMargins.lower_budget_norm,
          `Sendov.one_le_tri, `Sendov.FirstOriginSmall.norm_Fprod_le])] do
    let mut pending := [root]
    let mut visited : Std.HashSet Name := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      unless visited.contains name do
        visited := visited.insert name
        let some info := env.find? name | throwError "missing closure declaration {name}"
        if let some value := info.value? (allowOpaque := true) then
          for used in value.getUsedConstants do pending := used :: pending
    for name in visited do
      let text := name.toString
      for forbidden in #["centroid_identity", "second_origin_identity", "first_origin_identity",
          "origin_exact", "alpha_le_seventeen", "OriginExact", "Jsum",
          "scalarObstruction", "distillScalar", "Distillation", "polar_origin_incompatible",
          "Worigin", "sorryAx", "native_decide", "first_origin_polar_six_seven",
          "norm_integral_Fprod_le_of_first_origin", "norm_integral_Fprod_le_of_factorization",
          "FirstOriginBudget.lower_budget", "near_contradiction", "direct_budget_five",
          "direct_budget_six", "Sendov.FirstOriginSmall.upper_five_gap",
          "Sendov.FirstOriginSmall.upper_six_gap"] do
        if (text.splitOn forbidden).length > 1 then
          throwError "forbidden margin proof dependency: {root} -> {name}"
      if let some idx := env.getModuleIdxFor? name then
        let owner := env.header.moduleNames[idx.toNat]!.toString
        for forbidden in #["OriginExact", "Jsum", "Distillation", "LargeDegree",
            "Reduction.Contradiction", "Reduction.Scalar", "Interior"] do
          if (owner.splitOn forbidden).length > 1 then
            throwError "forbidden margin proof owner: {root} -> {name} in {owner}"
    for target in required do
      unless visited.contains target do
        throwError "missing positive quantitative consumption: {root} -> {target}"
      logInfo m!"MARGIN_POSITIVE {root} -> {target}"
    let axioms ← withEnv env <| Lean.collectAxioms root
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "unexpected axioms for {root}: {axioms}"
    logInfo m!"MARGIN_CLOSURE {root}: {visited.size}; axioms {axioms}"
