# Actual-mean centered route: investigation report

## Verdict

**Uniform C-near is neither proved nor disproved by this investigation. No certified counterexample to the actual square-root majorant was found.** In particular, this is not permission to replace the existing positive-variance endgame by C-near.

The work produced three independently checked Lean modules, a finite structural high-k envelope, and replayable exact/high-precision diagnostics. The whole budget is now proved on the **zero actual variance** domain for all m≥7 and 0<a<1. The positive-variance domain remains open.

The frozen deliverable is `research/centered-verified/`, based on checkout HEAD `a28fce8f970c3c4f50a9f6e194e0491775e75d4b`. The exploratory directory `research/centered/` is not the immutable verification target. No existing production theorem was weakened, no old endgame was removed, and no remote write or commit was performed.

## 1. Exact question tested

All actual-family diagnostics use natural multiplicities summing to m, each |qⱼ|≤1 as the intended exact constraint, and

    |∫₀¹ ∏ⱼ(a+(1−a²)tqⱼ) dt| ≥ 1.

The mean μ and centered variance v are computed from these same qⱼ. The majorant is the square-root expression implemented in `Sendov.Analytic.PaperCenteredBound.majorant_Efin`, including every complex Hₘ,ₖ endpoint. The objective is

    gap = majorant_Efin + Γ − (1−a|μ|),
    Γ = v/((m−1)|μ|²).

A positive gap would invalidate this sufficient target; it would not by itself be a Sendov polynomial counterexample. First-origin, centroid identities, α≤17, a real-mean assumption, or an averaged-only replacement of the pointwise domain were not added to feasibility.

`MATH_NOTE.md` specifies the formulas, exact versus relaxed constraints, and all structural inequalities.

## 2. Numerical and exact evidence

### Search and optimization

- **2,400** saved boundary-search configurations: m∈{7,8,12,20,50,100,256,512}, a∈{0.9,0.95,0.99,0.999,0.999999}, two-, three-, and four-modal families, unbalanced natural multiplicities, nonreal means, and interior radial factors.
- **13,068** evaluations in deterministic stochastic local optimization, with **27** stored objective finalists. Objectives include E/h, the relative C-budget ratio, and gap/h; optimizing only the unscaled gap near a=1 obscures relative budget stress. This is not a global optimization certificate.
- **7,777** separate raw-polar moment-disk configurations and **6,060** structural-envelope configurations. These scans use a deliberately larger, weaker feasibility domain and are not counted as FULLpolar-certified q families.

### High precision does not silently validate rounded premises

There are **30 cases replayed at two precisions**, hence **60 evaluations**, with precision ranging from 90 to 324 decimal digits. Full complex-product quadrature is compared with independent finite polynomial integration.

The first 23 literal floating candidates exposed an important feasibility issue: **6 fail FULLpolar at higher precision and 21 have a literal pointwise norm above one** after decimalization. These counts overlap. Those candidates are not certified feasible, despite passing the floating generator. They were not normalized and then relabeled as the same input.

Distinct inward rational witnesses were constructed and checked instead. The frozen collection contains **13 distinct rational q families** for which:

- natural cardinality and every pointwise squared norm are checked exactly;
- actual mean and variance are reconstructed;
- the full complex polar polynomial integral has squared modulus strictly greater than one;
- radical bounds use rational intervals checked by exact squaring;
- both E≤h/2 and E+Γ<1−a|μ| hold by rational comparisons.

The highest E/h among these exact witnesses is approximately **0.3113551**. The highest high-precision E/h among replayed candidates is approximately **0.3128250**, near m=24, a=0.9. These are attained sample values, not certified global suprema.

### Large degree and a→1

Two nonreal-mean, unbalanced families at **m=2048** were replayed at 240 and 320 digits:

- a=0.9: E/h≈0.00138117061315 and |K|≈6.53513140188×10¹⁹;
- a=0.999999999999: E/h≈3.63508154523×10⁻⁸ and |K|−1≈4.92885333176×10⁻¹⁹.

Their input coordinates are finite rationals with exact pointwise feasibility. The polar and majorant values in these large cases are high-precision numerical evidence, **not rational interval certificates**.

### Numerical false alarms

A descending complex binomial-tail evaluation can leave cancellation residue in low-degree H and manufacture huge false majorant failures. The corrected evaluator uses 1−B for low degrees and the finite tail for high degrees, with independent high-precision replay. Nothing from that unstable evaluation is presented as a mathematical counterexample.

## 3. Structural progress

### Kernel-checked: inverse mean powers cancel at every degree

For μ≠0 and 0≤k≤m,

    Hₘ,ₖ(aμ)/(binom(m,k)μᵏ)
      = (m+1)aᵏ⁺¹μ ∫₀¹tᵏ(1−aμt)ᵐ⁻ᵏdt.

`PaperCenteredTail` proves the identity, its exact norm form, the integral upper bound, and the finite block bound. This works for nonreal means and retains the top endpoint.

### Paper-proved: one factorial-weighted high-k bound

A binomial-mode/first-moment argument gives, uniformly in k,

    Cₘ,ₖ(v)² ≤ (2k+1)binom(m,k)vᵏ.

Factorial-weighted Cauchy–Schwarz then gives one integral bound T_K for every k≥K together. It uses the actual identity

    |1−aμt|²+a²vt² = 1−2axt+a²s t²,
    s = mean |qⱼ|² = |μ|²+v.

There is no per-degree certificate table. The constants are S₃=9/4 and S₄=5/9, with explicit finite endpoint corrections. The complete proof and formulas are in `MATH_NOTE.md` §3. **This factorial tail theorem is not yet formalized in Lean.**

The coarse T₃ envelope plus Γ reached a sampled maximum of about **0.3455327 times the actual C-budget** on the raw-moment scan. Keeping the square-root k=3 term and applying T₄ to the rest reached about **0.4424590 h**, below h/2 on the scan.

Conversely, the coarser T₃ envelope itself reached about **0.5256533 h**. That shows why blindly insisting on h/2 for a further relaxed envelope can lose information. It is **not** a counterexample to the original square-root majorant, which is smaller.

A rational m=13 family checks the single structural T₃ budget exactly, with envelope-plus-Γ approximately **0.3186235 times its C-budget**. This is one diagnostic application of the structural formula, not an all-degree proof.

### Kernel-checked: the zeroth endpoint and zero-variance domain

Raw polar gives 3β≤mh(1−β), with |1−aμ|²≤β. A single finite binomial term proves

    3ᴸ binom(m+1,L) βᵐ⁺¹ ≤ (mh)ᴸ.

The L=2 consumer proves |1−aμ|ᵐ⁺¹≤h/2 uniformly. When the actual variance is zero, Γ and every positive-degree C term vanish, so the entire strict C-near budget follows. This holds for all 0<a<1, m≥7, not merely a≥9/10.

### Kernel-checked: variance and the second endpoint are coupled

`PaperCenteredVarianceEndpoint` proves for the actual centered multiset

    |1−aμ|²+a²v ≤ β,
    N a²v |1−aμ|²ᴺ⁻² ≤ βᴺ  (every natural N≥1).

These prevent independent maximization of variance and endpoint radius, which would falsely suggest uncontrolled polynomial-in-m growth in the second endpoint. They are substantive input lemmas, not a completed global B₂/tail budget.

## 4. Verification boundaries

The frozen sources contain:

- `Sendov/Analytic/PaperCenteredTail.lean`;
- `Sendov/Analytic/PaperCenteredEndpoint.lean`;
- `Sendov/Analytic/PaperCenteredVarianceEndpoint.lean`;
- two small audit/test modules.

All five were compiled and independently checked with `leanchecker` in a private object stage: **10 successful checks**. The audited exported lemmas use only `propext`, `Classical.choice`, and `Quot.sound`. Source SHA-256 values and receipts are in `lean_verification.json` and `lean-logs/`.

The final aggregate `verify.py --full-rational` also exited 0 after reconstructing all thirteen rational witnesses and their radical bounds; its receipt is `verification_receipt.json`.

This is focused verification of the new modules against the pinned existing import cache. It is not a fresh whole-repository release build, nor integration into `Interior` or replacement of the old proof.

## 5. Remaining mathematical obligation

The positive-variance uniform claim is still unresolved. One precise route is to prove, on the original domain (or a justified larger moment domain), either

    E_end+T₃+Γ < 1−a|μ|,

or

    E_end+Q₃+T₄ ≤ h/2.

Here E_end retains the finite B₂ endpoint, Q₃ is the exact square-root k=3 term, and T_K is the single structural envelope. The current estimates and scans do not prove either inequality for every integer m and every parameter between sample points.

Because no certified counterexample to the **actual** majorant was found, no changed-premise or “corrected budget” is advertised as necessary. Retaining k=3 is a useful refinement of the new envelope, not a repair claimed to be minimal or forced by a counterexample.

## 6. Replay

From this frozen directory:

```sh
python3 verify.py --quick
python3 verify.py --full-rational
# Use a Python environment containing mpmath for numerical replay:
python verify.py --full-numeric
python3 verify_lean.py --project /path/to/the/project --config /path/to/pinned/config.json
```

`--quick` checks record consistency, exact stored feasibility comparisons, paired numerical agreement, structural algebra, and frozen source hashes. It does **not** reconstruct all radical bounds. `--full-rational` reconstructs all thirteen exact witnesses and their majorants. `--full-numeric` reruns the two-precision diagnostics and remains numerical evidence.

Exploration is reproducible with `search.py --count 60`, `optimize.py`, `scalar_scan.py`, and `envelope.py`. Raw exploration is not an acceptance test for the theorem. `RESULT.json` provides machine-readable counts and explicit OPEN status; `MATH_NOTE.md` contains the structural argument.
