# Centered route — round 2 verified report

## 1. Result: genuine positive-variance domains, not a global closure

Let `h=1-a`, `lambda=mh`, `mu=mean(q)`, `u=|mu|`, and `v=mean(|q-mu|²)`. The target remains the **original square-root-C finite majorant**, with every complex H endpoint:

    E_fin + Gamma < 1-a*u,   Gamma=v/((m-1)u²).

Every theorem below retains the pointwise conditions `|q_j|<=1`, the actual mean and variance, and the original **FULLpolar complex integral**. There is no real-mean restriction, first-origin feasibility assumption, alpha upper cutoff, or change to C. Where an additional regime condition is needed, it is stated explicitly.

### Fully kernel-checked, with all tail hypotheses discharged

**Quarter-lambda domain:** for all natural m≥7 and `0<a<1`,

    lambda <= 1/4
    => E_fin+Gamma <= 1-a*u - (79/504)h < 1-a*u.

The exported theorem is

    Sendov.CenteredQuarterTheorem.C_near_fullpolar_quarter.

The a-range is automatically within the original near-a domain. Positive variance and nonreal means are unrestricted. The final statement has **no error-budget, coefficient-bound, or tail-bound premise**. The supplied exact chord-tail inequality is proved for the original C sum and consumed in the final theorem.

`norm_J_gt_one_fullpolar_quarter` also proves the direct first-origin norm obstruction `|(m+1)I|>1` on this domain.

**Thin actual-variance strip:** for all m≥7 and `9/10<=a<1`, without any lambda cutoff,

    v <= h/m²
    => E_fin+Gamma <= 1-a*u - (19/840)h < 1-a*u.

This is

    Sendov.CenteredThinVariance.C_near_fullpolar_strip.

The variance-strip condition is an explicit restriction of the proved domain, not a silently added premise in a claim about global C-near.

The earlier `lambda<=4/39` result remains available with its separate stronger comparison against h. It has been superseded in covered lambda range by the quarter theorem, not deleted or mislabeled as the global result.

### Larger paper-proved domains, independently reviewed and exactly checked

The paper arguments additionally prove:

- **All variances for `lambda<=1/3`:**
  `E_fin+Gamma <= 1-a*u-(37/819)h`.
- **All original a and all variances for `m>=45`:**
  `E_fin+Gamma <= h/15+(891/2000)v`
  `<= 1-a*u-(14/15)h-(9/2000)v < 1-a*u`.

The cutoff m≥45 has a complete analytic argument: a new continuous-degree estimate for `45<=m<=170` is combined with the unbounded m≥170 argument. Its constants and derivative algebra were independently replayed. **The cutoff 45 and the extension from lambda 1/4 to 1/3 are not newly kernel-checked theorems.**

No certified counterexample was found or asserted. **The global original C-near target is still open.**

## 2. Exact remaining mathematical frontier

Combining the reviewed paper proofs and the kernel-checked strip leaves

    natural 7 <= m <= 44,
    1/3 < lambda <= m/10,
    a=1-lambda/m,
    v > h/m²,

intersected with the original pointwise/FULLpolar feasible set. Equivalently,

    7 <= m <= 44,
    9/10 <= a < 1-1/(3m),
    v > (1-a)/m².

Thus lambda≤22/5 on the remaining set. This description does not assert that every listed moment tuple is feasible, nor that C-near fails there. The kernel-only coverage is narrower than this paper frontier; the result metadata keeps that distinction explicit.

## 3. What changed mathematically

### A. The formerly paper-only coefficient and factorial steps now compile

The binomial integer-mean mode argument proves, uniformly for natural m,k and nonnegative v,

    C_(m,k)(v)² <= (2k+1) binom(m,k) v^k.

The implementation consumes the existing `PaperCenteredBound.C`, including the top-degree and out-of-range branches. It does not replace C by the actual elementary coefficient.

`FirstMoment`, `BinomialMode`, and `CoefficientBound` prove the finite first-moment bound, unnormalized binomial mode, and the actual-C consequence. `PaperFactorialTail` proves the exact factorial/binomial moment, weighted Cauchy–Schwarz, the terminal corrections in the weight sums, and the constants 9/4 and 5/9. The real half-exponent is not truncated by natural division.

### B. The tail is connected to the original E_fin

`CenteredActualTail.majorantTail_le_cubicIntegral` combines those bounds with the all-degree H/mean cancellation. It keeps the variance of the actual centered multiset and discharges the coefficient hypothesis. The subsequent s≤1 relaxation is proved from the actual-statistic constraint.

`CenteredChordGeneral.majorantTail_le_chordScalar` gives, for a justified chord slope c,

    Tail <= 9 a^4 u sqrt(v³) / [c^4 sqrt(m(m-1)(m-2))].

This is the original square-root majorant tail, not a new definition of its error. The quarter theorem supplies c=13/18 and consumes this proved bound, completing the formal chain.

### C. The available budget is larger than h

The useful retained-mean inequality is

    1-a*u = h+a(1-u) >= h+(a/2)v.

It follows from `v<=1-u²<=2(1-u)`. Using this actual-variance contribution, rather than replacing the entire right side by h, allows the quarter-lambda and larger paper regimes to close without proving the stronger intermediate assertion E_fin≤h/2.

### D. The cutoff proof retains the a-factor and integrates from a midpoint

For `45<=m<=170`, rational polar gives `b<=m/(m+30)`. Set

    d_m=(18m+2040)/(85(m+30)).

A square-root tangent at **(17/20)²** proves

    sqrt(beta_s(1/2)) <= 1-(5/9)a*d_m.

The midpoint norm chord then has slope `(10/9)a*d_m`; its fourth power cancels the a^4 factor in the structural tail. Discarding a^4 first would lose this improvement.

The other half of the integral is controlled with `r_m=m/(m+30)`. The functions N(m), J(m), K(m) are bounded by proved real-variable monotonicity/convexity and a few exact endpoint comparisons. The dependence of r_m on m is differentiated correctly.

**This is not a per-degree certificate table:** no separate budget is generated for every degree. The scalar derivative signs and interval-cover argument prove entire continuous ranges, which are then restricted to natural m.

## 4. Verification and evidence levels

The final frozen bundle contains **22 Lean modules**, including three prior-round dependencies and audit modules. The fresh `--rebuild` exited 0: **all 44 compile/leanchecker checks passed** in a private complete object stage. The four selected audit modules contain **36 axiom-audit entries**; these are audit entries, not a count of distinct mathematical theorems. They contain only

    propext, Classical.choice, Quot.sound.

The final receipts bind the source SHA-256 values. There is no `sorry`, `admit`, `native_decide`, custom axiom declaration, or weakened public theorem in the checked source.

The parent independently reran all three paper checkers:

- `math-bound/verify.py`: 53 exact rational/algebraic checks;
- `math-middle/verify.py`: 48 exact rational checks;
- `math-cutoff45/verify.py`: 62 exact rational/algebra checks.

These check constants, derivative numerators, shifted polynomial identities, and exact positive comparisons. **They do not kernel-check the remaining calculus and logarithmic arguments.** Those arguments are written in the associated PROOF.md files and were reviewed separately; finite arithmetic checks are not substituted for a quantified theorem.

An additional exact witness lies inside the newly proved strip but outside both near-lambda regions: m=100, a=19/20, hence lambda=5, with 98 copies of 1 and the rational unit-circle pair

    999999/1000001 ± i·2000/1000001.

Its actual positive variance satisfies v≤h/m². The original FULLpolar integral has an exact lower rectangle greater than one, and the unchanged E_fin budget is reconstructed with rational radical enclosures. This is a nonvacuity/implementation diagnostic, not a degree certificate used by the proof.

## 5. Files and replay

Main integrated exports:

- `Sendov/Analytic/CenteredQuarterTheorem.lean` — final quarter-domain FULLpolar theorem and norm obstruction;
- `Sendov/Analytic/CenteredThinVariance.lean` — all-lambda variance strip;
- `Sendov/Analytic/CenteredActualTail.lean` and `CenteredChordGeneral.lean` — original-C tail assembly;
- `CoefficientBound.lean` and `PaperFactorialTail.lean` — uniform coefficient and factorial machinery;
- `math-cutoff45/PROOF.md` — final reviewed paper cutoff;
- `math-middle/PROOF.md` — near extension to 1/3 and the high-degree dependency;
- `math-bound/PROOF.md` — earlier complete regime arguments.

The child proof notes preserve their creation-time formalization labels. The final integrated `REPORT.md` and `RESULT.json` are authoritative about which of their consumers are now kernel checked.

Replay stored source/receipt consistency and the exact arithmetic with:

```sh
python3 verify_round2.py
```

For a fresh compile plus independent kernel check of every bundled module:

```sh
CENTERED_PROJECT=/path/to/compatible/project \
CENTERED_CONFIG=/path/to/pinned/config.json \
python3 verify_round2.py --rebuild
```

The supplied project/cache is based on HEAD `a28fce8f970c3c4f50a9f6e194e0491775e75d4b`. The checker uses a private `.lake/paper/objects` stage and unlinks target symlinks before writing. The default command verifies saved receipts rather than claiming a new Lean execution. No package install or global Lake build is needed.

The exact intermediate-strip witness has its own replay:

```sh
python3 -B verify_intermediate_witness.py
```

## 6. Scope of delivery

This round made no new broad random scan. It produced uniform proofs, actual-C formal assembly, exact arithmetic replays, and an explicit smaller residual domain. Existing global endgames were not removed; no main proof replacement, fresh whole-repository release, commit, or remote publication is claimed. The previous frozen artifact and baseline source/cache were kept read-only during the isolated work.

**Still required for global closure:** a proof or certified counterexample on the residual domain in §2. The cutoff 45 and near extension to 1/3 also remain to be migrated to Lean before being described as kernel-checked coverage.
