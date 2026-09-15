# Original-C near extension to lambda ≤ 1/3 — COMPLETE

## Result

`Sendov.CenteredThird.C_near_fullpolar_third` is compiled and independently kernel-checked. For a complex multiset `q`, it assumes exactly:

- `7 ≤ q.card`;
- `0 < a < 1` (so in particular it applies to the requested `9/10 ≤ a < 1` domain);
- `q.sum = q.card * μ`;
- `∀ z ∈ q, ‖z‖ ≤ 1`;
- the original FULLpolar inequality
  `1 ≤ ‖∫ t in 0..1, (q.map (fun z => a + t*(1-a²)*z)).prod‖`;
- `PaperPolar.lambda q.card a ≤ 1/3`.

Writing `r = q.map (fun z => z-μ)`, the theorem proves both

```
majorant_Efin r μ (a*μ) + Gamma r μ ≤ 1-a*‖μ‖-37*(1-a)/819
majorant_Efin r μ (a*μ) + Gamma r μ < 1-a*‖μ‖.
```

Here `majorant_Efin`, `Gamma`, `C`, `H`, and `variance` are the existing frozen definitions, not replacements. The original square-root `C` remains in the finite tail. There is **no tail-budget premise, coefficient-bound premise, external variance premise, real-mean restriction, or saturated-second-moment assumption** in the final consumer. Zero variance is included.

Also completed: `Sendov.CenteredThird.norm_J_gt_one_fullpolar_third`, giving

```
1 < ‖(q.card+1) * ∫ t in 0..1, (q.map (fun z => 1-a*t*z)).prod‖.
```

There are no remaining proof premises to discharge within the requested lambda ≤ 1/3 regime. This stage makes no claim for lambda > 1/3 and does not implement the separate large-degree cutoff.

## Proof route

1. `CenteredThirdTail.lean` uses the frozen exact `PaperFactorialTail.weight3_sum` to retain
   `S_m = 9/4 - 2/(m-1) - 1/(2m(m-1))`.
   The original `C` coefficient bound is discharged with `PaperBinomialMode.C_sq_le_binomial`. The exact weight passes through the pointwise sum and normalized-H integral, then the chord integral gives
   `Tail ≤ 9*eta_m*a^4*‖μ‖*sqrt(v^3)/(c^4*sqrt(m(m-1)(m-2)))`.
   Here `eta_m=(2/3)*sqrt(S_m)`. Neither eta nor a^4 is discarded.
2. `CenteredThirdScalar.lean` proves `eta_m ≤ 1-4/(9m)`, the fourth-power saving, and
   `eta_m*a^4 ≤ 1-13/(10m)` on `1/4 ≤ m*h ≤ 1/3`.
   It also derives `u*sqrt(v) ≤ 3/10` from `u²+v≤1`, `0≤v≤1/10`.
3. The tail coefficient is exactly
   `A=9*(3/10)*(5/12)*(60/41)^4`; the Gamma coefficient is
   `G=(31/30)*(120/113)^2`.
   The unfrozen relation `a=1-h` is retained when proving
   `m*(Q-a/2) ≤ 3`. This yields the combined tail/Gamma allowance
   `a*v/2+(12/13)*h` without dividing by v. The endpoint contributes at most `(2/63)*h`, giving the total `a*v/2+(782/819)*h` and the margin `37*h/819`.
4. `CenteredThirdActual.lean` proves all needed bounds from actual statistics and RawPolar: `h≤1/21`, `u≥113/120`, `b≤1/10`, `v≤1/10`, `v*(3+m*h)≤m*h`, and `‖1-a*μ‖≤19/60`.
5. `CenteredThirdEndpoint.lean` keeps all three B₂ triangle-bound terms. Its envelope is
   `(19/60)^(m-1)*[(19/60)^2+(m+1)*(19/60)+m(m+1)/2]`.
   A uniform induction from m=7 proves `‖B₂‖≤1/30`; no degree table is used.
6. `CenteredThirdTheorem.lean` assembles the closed interval `[1/4,1/3]`, joins it to the frozen quarter theorem, and converts FULLpolar to RawPolar using the existing complex-integral theorem.

The tail proof uses the safe upper quadratic `PaperPolar.beta` after the actual inequality `v≤1-‖μ‖²`; this is an inequality, not an assumption that the second moment equals one. The actual-statistics improvement `u*sqrt(v)≤3/10` is then retained in the scalar tail bound.

## Verification

`python3 /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round3/lean-third/replay.py`

Actual replay result: **PASS**.

- Five substantive new modules and one audit module compile: six successful compilation receipts.
- All six modules pass independent `leanchecker`: six successful kernel receipts.
- All **20 new lemmas/theorems** are covered by `#print axioms`; every result lists only `propext`, `Classical.choice`, `Quot.sound`.
- New Lean sources contain no `sorry`, `admit`, `native_decide`, or custom axiom declarations.
- Source and object SHA-256 values are recorded in `receipts/`; `VERIFICATION.json` aggregates results and source hashes.
- All **178 entries** in the frozen input manifest match before and after replay.
- Toolchain: Lean `v4.34.0-rc1`, using the supplied config and original root's direct checker. No broad project rebuild was performed.
- Some source-format/unused-variable linter warnings remain; there are no compilation or kernel failures in the final replay.

Frozen manifest SHA-256:
`2596154664f43c295954283a91183a3d634fd6fc23c2a9bcc774810e1c3e5a36`

Reviewed `math-middle/PROOF.md` SHA-256:
`41e381086f706a026b8d8bc223b179e4524bc542b1cc900bd8440b9824b05410`

## Artifacts and ownership

All authored files and build outputs are under this `lean-third` directory:

- `Sendov/Analytic/CenteredThird{Tail,Scalar,Actual,Endpoint,Theorem}.lean`
- `tests/CenteredThirdAudit.lean`
- `check.py`, `replay.py`
- `REPORT.md`, `WORKFLOW.md`, `VERIFICATION.json`
- `receipts/*.json`
- `.lake/paper/logs/*`, private `.lake/paper/objects/*`, and private setup files.

`check.py` has an explicit original `PROJECT` path, uses the frozen object's complete overlay as its baseline, and unlinks target outputs before compilation. It rejects a kernel check unless the current source and object hashes agree with a successful compilation receipt. Imported objects are read-only symlinks; compiled targets are private regular files.

No frozen source, original-root source, sibling source/cache, Git commit, or remote was modified. The new five-module import target for integration is `Sendov.Analytic.CenteredThirdTheorem`.
