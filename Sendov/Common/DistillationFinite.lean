import Sendov.DistillationFinite.Rows5_12
import Sendov.DistillationFinite.Rows13_20
import Sendov.DistillationFinite.Rows21_28
import Sendov.DistillationFinite.Rows29_36
import Sendov.DistillationFinite.Rows37_44
import Sendov.DistillationFinite.Rows45_52
import Sendov.DistillationFinite.Rows53_55
import Sendov.DistillationFinite.Rows61_61
import Sendov.LargeDegree.DistillationTailBound

/-! Exact finite-domain critical-bracket closure. Fixed original paper budgets;
see DistillationCriticalFinite for attribution. No sampled truth or global T grid. -/
namespace Sendov

theorem distillFinite_components {m : ℕ} (hm : 5 ≤ m) (hm60 : m ≤ 60)
    {α : ℝ} (hα : 0 ≤ α) (hαm : α ≤ (m : ℝ) / 2) (h17 : α ≤ 17) :
    distillEBudget m + distillT0 m α + distillT1 m α + distillT2 m α < 199 / 200 := by
  by_cases hinterval : 55 ≤ m
  · exact distillComponents_interval_55_61
      ⟨by exact_mod_cast hinterval, by exact_mod_cast (show m ≤ 61 by omega)⟩ hα h17
  have hm54 : m ≤ 54 := by omega
  interval_cases m
  · exact (distillFinite_5 α hα (by linarith)).trans_lt distillFiniteBound_5
  · exact (distillFinite_6 α hα (by linarith)).trans_lt distillFiniteBound_6
  · exact (distillFinite_7 α hα (by linarith)).trans_lt distillFiniteBound_7
  · exact (distillFinite_8 α hα (by linarith)).trans_lt distillFiniteBound_8
  · exact (distillFinite_9 α hα (by linarith)).trans_lt distillFiniteBound_9
  · exact (distillFinite_10 α hα (by linarith)).trans_lt distillFiniteBound_10
  · exact (distillFinite_11 α hα (by linarith)).trans_lt distillFiniteBound_11
  · exact (distillFinite_12 α hα (by linarith)).trans_lt distillFiniteBound_12
  · exact (distillFinite_13 α hα (by linarith)).trans_lt distillFiniteBound_13
  · exact (distillFinite_14 α hα (by linarith)).trans_lt distillFiniteBound_14
  · exact (distillFinite_15 α hα (by linarith)).trans_lt distillFiniteBound_15
  · exact (distillFinite_16 α hα (by linarith)).trans_lt distillFiniteBound_16
  · exact (distillFinite_17 α hα (by linarith)).trans_lt distillFiniteBound_17
  · exact (distillFinite_18 α hα (by linarith)).trans_lt distillFiniteBound_18
  · exact (distillFinite_19 α hα (by linarith)).trans_lt distillFiniteBound_19
  · exact (distillFinite_20 α hα (by linarith)).trans_lt distillFiniteBound_20
  · exact (distillFinite_21 α hα (by linarith)).trans_lt distillFiniteBound_21
  · exact (distillFinite_22 α hα (by linarith)).trans_lt distillFiniteBound_22
  · exact (distillFinite_23 α hα (by linarith)).trans_lt distillFiniteBound_23
  · exact (distillFinite_24 α hα (by linarith)).trans_lt distillFiniteBound_24
  · exact (distillFinite_25 α hα (by linarith)).trans_lt distillFiniteBound_25
  · exact (distillFinite_26 α hα (by linarith)).trans_lt distillFiniteBound_26
  · exact (distillFinite_27 α hα (by linarith)).trans_lt distillFiniteBound_27
  · exact (distillFinite_28 α hα (by linarith)).trans_lt distillFiniteBound_28
  · exact (distillFinite_29 α hα (by linarith)).trans_lt distillFiniteBound_29
  · exact (distillFinite_30 α hα (by linarith)).trans_lt distillFiniteBound_30
  · exact (distillFinite_31 α hα (by linarith)).trans_lt distillFiniteBound_31
  · exact (distillFinite_32 α hα (by linarith)).trans_lt distillFiniteBound_32
  · exact (distillFinite_33 α hα (by linarith)).trans_lt distillFiniteBound_33
  · exact (distillFinite_34 α hα h17).trans_lt distillFiniteBound_34
  · exact (distillFinite_35 α hα h17).trans_lt distillFiniteBound_35
  · exact (distillFinite_36 α hα h17).trans_lt distillFiniteBound_36
  · exact (distillFinite_37 α hα h17).trans_lt distillFiniteBound_37
  · exact (distillFinite_38 α hα h17).trans_lt distillFiniteBound_38
  · exact (distillFinite_39 α hα h17).trans_lt distillFiniteBound_39
  · exact (distillFinite_40 α hα h17).trans_lt distillFiniteBound_40
  · exact (distillFinite_41 α hα h17).trans_lt distillFiniteBound_41
  · exact (distillFinite_42 α hα h17).trans_lt distillFiniteBound_42
  · exact (distillFinite_43 α hα h17).trans_lt distillFiniteBound_43
  · exact (distillFinite_44 α hα h17).trans_lt distillFiniteBound_44
  · exact (distillFinite_45 α hα h17).trans_lt distillFiniteBound_45
  · exact (distillFinite_46 α hα h17).trans_lt distillFiniteBound_46
  · exact (distillFinite_47 α hα h17).trans_lt distillFiniteBound_47
  · exact (distillFinite_48 α hα h17).trans_lt distillFiniteBound_48
  · exact (distillFinite_49 α hα h17).trans_lt distillFiniteBound_49
  · exact (distillFinite_50 α hα h17).trans_lt distillFiniteBound_50
  · exact (distillFinite_51 α hα h17).trans_lt distillFiniteBound_51
  · exact (distillFinite_52 α hα h17).trans_lt distillFiniteBound_52
  · exact (distillFinite_53 α hα h17).trans_lt distillFiniteBound_53
  · exact (distillFinite_54 α hα h17).trans_lt distillFiniteBound_54

theorem distillFinite_scalar {m : ℕ} (hm : 5 ≤ m) (hm60 : m ≤ 60)
    {α : ℝ} (hα : 0 < α) (hαm : α ≤ (m : ℝ) / 2) (h17 : α ≤ 17) :
    scalarObstruction m α (cubicPolarEnvelope α) < 199 / 200 := by
  have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm
  exact (distillScalar_le_majorant hmR hα (by linarith)).trans_lt
    (distillFinite_components hm hm60 hα.le hαm h17)

end Sendov
