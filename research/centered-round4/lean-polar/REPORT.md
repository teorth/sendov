# Actual FULLpolar moment — checked structural interface

`Sendov.CenteredActualPolar.actual_variance_moment_of_fullpolar` now proves directly from FULLpolar and the actual mean equation:

    1 <= integral_0^1
      [a²+2a(1-a²) Re(mu)t
        +(1-a²)² (actual centered variance+|mu|²)t²]^(m/2) dt.

The second-moment coefficient is computed from the actual q, not an independent scalar or a silently imposed s=1 condition. The proof establishes the exact quadratic-mean identity, applies finite AM–GM to norm squares, and moves the complex integral norm inward. The second moment is exactly decomposed into centered variance plus squared mean norm. Pointwise bounds are needed only for the separate secondMoment<=1 lemma, not for this stronger norm-integral implication itself.

This is a structural necessary condition, NOT sufficiency of moment feasibility and NOT a global C-near conclusion.

## Verification

Source and audit compile; both independent leanchecker runs passed. Seven theorem axiom audits use only propext, Classical.choice, Quot.sound. See VERIFICATION.json and receipts/.

Replay:

    python3 check.py Sendov.Analytic.CenteredActualPolar
    python3 check.py Sendov.Analytic.CenteredActualPolar --kernel
    python3 check.py tests.ActualPolarAudit
    python3 check.py tests.ActualPolarAudit --kernel

The supplied pinned config and immutable round2-verified object closure are read-only. The new source, objects, logs and receipts are private to this directory. Nonblocking style/unused-tactic linter warnings remain. No commit or publication was performed.
