# Formalization scope and mathematical status

## Obtained local results

The acceptance inventory contains 92 normalized result families from 14 local
reports/notes. A family may contain several paired inequalities or a finite
list of certified examples; **92 is not a count of atomic propositions**.
Repeated historical cutoffs are identified rather than counted as new proof
methods. Every obtained family is mapped in `ACCEPTANCE.json`.

The final three corollary modules turn the previously prose-only composition
recipes into public Lean contracts:

- `PaperOriginCorollaries`: actual derivative/residual and full polar hierarchy.
- `PaperMomentCorollaries`: exact finite moments, deficits and polar consequences.
- `PaperRegionCorollaries`: historical cutoffs, margins and all original ray bands.

The main accepted mathematical result is `Sendov.PaperUniform.uniform_D`:
all natural m≥256, all 0<a<1, closed −1≤x≤1, and the actual raw-polar integral
imply the strict bound on the actual beta integral. The n=m+1 production
consumer is used by both public Solution theorem proofs. The near-endpoint
result covers every m≥7 with m(1-a)≤2/5, with gap >(1-a)/1000. Stronger
historical quantitative margins and estimates are separately retained.

## Explicit correction of asymptotic evidence labels

Three groups of formulas in the exploratory reports were not supplied with
complete mathematical proofs. They are **not obtained theorems**, and are not
part of the 92 proved families:

- **AS01:** fixed-m expansion of the polar integral/root as a→1. The report
  computes coefficients but does not prove the required remainder bound and
  degenerate-root inversion/existence statement.
- **AS02:** parameter derivatives of T at the boundary and the gap expansion
  along the polar root. Parameter differentiation, remainder control and root
  substitution were not fully justified in the report.
- **AS04:** fixed-scale m→∞ convergence of the polar integral, mT and mB.
  The report states limits without a full domination/scaled-tail convergence
  proof. The finite Laplace estimates do not by themselves constitute that proof.

These remain heuristic/diagnostic calculations needing proof. No Lean theorem,
uniform limit, or O-term estimate is claimed for them. By contrast AS03
(fixed-degree small-a exclusion) and AS05 (the entire limiting-model inequality,
without asserting convergence to that model) have actual formal contracts.

## Open research, not missing formalization of obtained proofs

- Uniform D for the residual domain 7≤m<256, m(1-a)>2/5 beyond the sufficient
  secant gate remains open in this work. No general m≥7 all-a theorem is claimed.
- The centered finite expansion and conditional majorant C-budget are proved;
  the geometric hypotheses do not yet force that budget throughout C-near.
- Universal positivity of Fsec is not asserted. A feasible negative gate is
  formally exhibited; its failure is not a counterexample to D.
- Complex-collinear affine transport and general collinear equality were not
  locally completed. The recovered third-party papers supply separate blueprints;
  they are not being called globally unknown, nor silently adopted as checked.
- Tao's external averaged-L2 working proof and the entirety of downloaded PDFs
  are outside this local obtained-results inventory. This deliverable does not
  claim to formalize every theorem in those documents.

The existing full-domain endgame remains in the public proof for the remaining
finite-degree/radius region. It cannot be deleted on the strength of the new
partial-domain route. The two public mathematical statements and their strict
or extremal alternatives are unchanged.

## Evidence levels

Source-contract review, Lean elaboration, independent Lean kernel replay, and
Python witness generation are separate evidence. Python generators are
untrusted convenience tools; exact emitted arithmetic and its binding to the
actual complex families/integrals are proved by Lean. Uncertified floating-point
screens and timing displays do not become theorems.
