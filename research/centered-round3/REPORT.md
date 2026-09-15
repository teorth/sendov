# Round 3 checkpoint: certify the loss before changing the majorant

Status: CONTINUING. Parent integration now independently compiles and kernel-checks the complete original-C theorem for lambda<=1/3, with margin 37h/819 and no tail-budget premise. The eight integrated modules (near extension plus mean/Gamma geometry) passed 16 focused compile/kernel checks and27 axiom audits. `integrated/VERIFICATION.json` records the actual checks. The new paper cutoff35 passed the parent's 112-check exact replay and analytic review; a further independent audit and residual-domain extension are active in isolated round4 directories. Uniform C-near remains open.

## Exact auxiliary obstruction, on original feasible data

Take m=44, a=9/10, with 22 copies of each

    q± = [(9999+200i)/10001] * [(21±20i)/29].

All pointwise squared norms are exactly 1. The actual mean is

    mu=(209979+4200i)/290029,

so this is not a real-mean example. The actual norm u=21/29 and variance v=1-u² are retained. Exact rational finite-product integration proves FULLpolar: its complex integral has squared norm greater than 1, with display margin about 0.21688425. Exact radical enclosures certify the ORIGINAL square-root majorant E_fin/h<0.236 and E_fin+Gamma<1-au.

But the whole-interval norm-chord replacement is provably too large. Set

    b=1-2a Re(mu)+a²,
    d=1-sqrt(b),
    S_m=9/4-2/(m-1)-1/(2m(m-1)), D=m(m-1)(m-2).

The proposed finite chord tail envelope is

    sqrt(S_m D) (m+1)a^4 u v^(3/2)
      * integral_0^1 t^3 (1-dt)^(m-3) dt.

An exact rational lower enclosure for this expression is more than

    2.0517316767 * (1-au).

This already exceeds the entire budget before adding the nonnegative endpoint/Gamma terms. The integral is evaluated with its finite upper endpoint; extending it to 1/d is NOT the reason for failure. It is the whole-interval loss of quadratic curvature.

**This is a counterexample to the auxiliary chord budget, NOT to original C-near.** It rules out repairing that global chord route solely by strengthening the feasibility premise to FULLpolar or retaining its finite endpoint.

### Feasible correction on the same witness

Keep beta(t)=1-2a Re(mu)t+a²t² instead of the norm chord. Since the actual second moment is 1, this is the actual moment quadratic, not a changed premise. On [0,1], 0<=beta<=1, so for m=44 the true exponent 41/2 obeys beta^(41/2)<=beta^20. Exact polynomial integration and radical enclosures now give

    E0 + Gamma(1+|B2|) + quadratic-tail upper
       < 0.175543 * (1-au).

This is a sufficient corrected budget for this witness, not a claim of minimality or a per-degree proof of global C-near. It demonstrates that retaining curvature alone can recover ample slack without changing C or removing endpoints.

Replay the full literal witness, exact FULLpolar, original C budget, failed chord envelope, and corrected quadratic budget with standard-library Python:

    cd diagnostics
    python3 -B certify_chord.py

All assertions passed. Full rational values and both q multiplicities are saved in `diagnostics/chord_obstruction.json`.

## New kernel-checked mean/Gamma geometry

`lean-geometry/Sendov/Analytic/CenteredMeanBudget.lean` proves

    |mu|²+b = 1+|mu-a|²,
    |mu|² >= 1-b,
    Gamma <= v/[(m-1)(1-b)].

Combining the existing raw-polar rational endpoint bound with the original a>=9/10 yields the all-degree consequence

    Gamma <= [(m+30)/(30(m-1))] v.

`Sendov.CenteredMeanBudget.Gamma_le_fullpolar_degree` consumes the original actual-mean equation, pointwise unit-disk constraints, and FULLpolar integral directly, with no externally assumed Gamma budget. Nonreal means are unrestricted. This is a Gamma estimate, not the final C-near theorem.

The source and audit module passed four compile/leanchecker checks. Seven selected theorem axiom audits contain only propext, Classical.choice and Quot.sound. Private source/object stage; prior frozen sources/caches and sibling stages untouched.

## Numerical diagnostics, separately labeled

The search ranged over integer m in 7..44, lambda in [1/3,m/10], actual-compatible moment tuples, and nonreal means. It is a search over necessary moment relaxations, NOT a FULLpolar q-family search and NOT a global maximum certificate.

Twelve local/global-heuristic optimizer runs compared the original C expression and the factorial quadratic envelope R under three nested necessary conditions:

1. only rational raw-polar endpoint/moment consequences;
2. additionally the polar endpoint-norm chord integral >=1;
3. additionally the polar moment norm integral >=1.

The observed R ratios were below 1 (worst observed about 0.879144 in the weakest relaxation); this does not prove R everywhere. All twelve literal optimizer inputs were replayed at 80 and 140 decimal digits, with agreement better than 1e-65. Six further chord-envelope optimizations confirmed large failures even in the strongest moment relaxation. One actual FULLpolar witness was then independently reconstructed and certified as above.

`relaxation.py` uses cancellation-safe moment identities to avoid a spurious negative variance at boundary points; 32 boundary parameter cases passed. No invalid optimizer point is treated as a mathematical certificate. The exact witness is specified independently and is not a silently repaired optimizer input.

Numerical replay requires the task-local venv with scipy, numpy and mpmath:

    diagnostics/.venv/bin/python diagnostics/relaxation.py
    diagnostics/.venv/bin/python diagnostics/chord_probe.py
    diagnostics/.venv/bin/python diagnostics/replay.py

## Still open

Uniform C-near is still open. The new parent-reviewed paper argument leaves 7<=m<=34, 1/3<lambda<=m/10, v>h/m², intersected with original FULLpolar and pointwise feasibility. Its cutoff35 is paper-level and still under an additional independent audit; it is not a new kernel-covered domain. The complete kernel-covered near domain is now lambda<=1/3, alongside the prior all-lambda thin variance strip. No per-degree certificate table, new global theorem, commit, or remote publication is claimed.
