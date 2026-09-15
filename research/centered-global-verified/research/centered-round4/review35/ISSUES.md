# Issues and blockers

## No blocking gap in (M), (T), or the conditional paper cutoff m>=35

The independent audit accepts the two new main statements, with the frozen raw-polar and cutoff-45 results as declared dependencies. No Lean/kernel closure or proof of the remaining original domain is supplied by this audit.

## LOW: strict intermediate inequalities after multiplication by v

Locations in reviewed `math-polar/PROOF.md`:

- §5, display (5.3), line 255: `Tail <= A v < (433/1000)v`;
- §6, display (6.1), line 267: `Gamma <= G v < (61/1000)v`;
- §6, display (6.2), line 281: strict final `< (20/1000)v`.

The strict comparisons between positive **constants** are true, but their products with v are only weakly ordered if v=0. Thus these displays, if read literally on the entire claimed domain, contain `0<0` at zero variance.

### Exact feasible witness

Take m=35, a=9/10, and every q_j=1. Then

- all pointwise norms equal 1;
- actual mu=u=x=s=1 and v=0;
- d=19/100;
- FULLpolar integral is exactly

  `[((109/100)^36-(9/10)^36)/(36*(19/100))]`

  and equals approximately `3.24980944906985717237... >1`;
- every positive-degree C coefficient, Tail, and Gamma is zero.

The exact rational value and its `>1` check are saved in `evidence.json`, field `local_strict_sign_issue`. This is a counterexample **only to the intermediate strict displays**, not to the final original majorant inequality or margin theorem.

### Minimal correction

Use `Tail<=(433/1000)v`, `Gamma<=(61/1000)v`, and `Gamma|B2|<=(20/1000)v` uniformly. Optionally state that each comparison is strict when v>0. All later calculations already use weak inequalities, and h>0 supplies strictness in the final target, including v=0. No constant, cutoff, or final margin changes.

The source already explicitly discusses including v=0, so this is a local notation error rather than a missing zero-variance case in its reasoning. Reviewed sources were not edited.

## Scope clarifications, not mathematical defects

- “Continuous degree band 35<=m<=44” means the scalar inequalities are uniform over that real band; the original product, binomial tail, and theorem remain indexed by integer m. There is no defined original m-factor object for noninteger m.
- The single endpoint moment proof is genuinely a rational Bernstein **certificate**, not a certificate-free analytic proof. Its 88 coefficient inequalities index h-basis coefficients, not 88 original degrees.
- The new theorem does not follow from raw-polar constraints alone: the stronger actual norm moment needed in (M) is derived from FULLpolar. The proof retains this premise correctly.
- The finite and extended chord-consumer obstructions are valid exact FULLpolar-feasible examples, but they are not counterexamples to the original-C target. The independent exact interval replay certifies the original target on that family.

## Execution issues

No runtime blocker or missing dependency remained. The audit uses only the Python standard library. No reviewed source/cache writes, commit, or push were performed.
