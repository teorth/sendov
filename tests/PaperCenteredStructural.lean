import Sendov.Analytic.PaperCenteredEndpoint

#print axioms Sendov.PaperCenteredTail.normalized_H_integral
#print axioms Sendov.PaperCenteredTail.majorant_term_integral
#print axioms Sendov.PaperCenteredTail.majorant_block_le_integral
#print axioms Sendov.PaperCenteredEndpoint.endpoint_power_order
#print axioms Sendov.PaperCenteredEndpoint.norm_endpoint_half_of_rawPolar
#print axioms Sendov.PaperCenteredEndpoint.zero_variance_C_near

-- Mean powers cancel for a nonreal mean and every degree, not just k=m.
example (a μ : ℂ) (hμ : μ ≠ 0) :
    Sendov.PaperCentered.H 8 3 (a * μ) / (((8 : ℕ).choose 3 : ℂ) * μ ^ 3) =
      (9 * a ^ 4 * μ) *
        (∫ t in (0 : ℝ)..1, (t : ℂ)^3 * (1-a*μ*t)^5) := by
  convert Sendov.PaperCenteredTail.normalized_H_integral 8 3 (by decide) a μ hμ using 1 <;> norm_num
