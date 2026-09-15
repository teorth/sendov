# REPORT — FULLpolar / original C-near

## Outcomes

- **Closed the entire continuous band `35<=m<=44`**, all original `9/10<=a<1`, all actual variances and nonreal means:

      E+Gamma <= 1-au-(107/250)(1-a).

  With the frozen cutoff45 theorem, this lowers the paper cutoff to **m>=35**. The still-unresolved complement from these results is `7<=m<=34`, `lambda>1/3`, `v>h/m^2`, with FULLpolar still required.

- **New actual-statistic moment consequence**, uniformly for `7<=m<=44`:

      Re(mu) > 7/10 + (1-a^2)(1-s)/(3a).

  More generally, FULLpolar implies `N_m(a,x,s)>=1` and

      N_m(a,x-(1-a^2)(1-s)/(3a),1)>=1,

  where `N_m=int_0^1[a^2+2a(1-a^2)xt+(1-a^2)^2st^2]^(m/2)dt`.
  The auxiliary s=1 evaluation is a proved domination, **not** an s=1 assumption.

- **Exact actual-s endpoint condition**: for `B=1-2ax+a^2s` and the unique polar-chord root `r_*>1`,

      B <= s-(r_*^2-1)/(1-a^2),
      r_*^(m+1)=a^(m+1)+(m+1)(r_*-a).

  The norm-integral boundary has slope `d/(3a)<=-X'(s)<=d/(2a)`, `d=1-a^2`, wherever defined with positive mean.

- **Exact FULLpolar-feasible obstruction to BOTH whole-interval tail norm chords.** At `m44,a9/10`, take 22 copies each of `(177 ± i sqrt(31171))/250`. The exact full complex integral exceeds 1; budget is `0.3628`. Certified lower bounds for the finite and extended chord tail consumers are respectively `0.9511606591...` and `0.9544132796...`, each already exceeding the entire budget. Actual numerical chord tails are about `0.9990`, versus original-beta structural tail `0.04328` and original C tail `0.02777`. **This is not an original-C counterexample.** It confirms that retaining beta curvature, rather than merely retaining the finite chord endpoint, matters.

## Verification / limitations

- `verify.py`: **112 exact rational checks passed**; standard library only. It reconstructs the moment polynomial, Bernstein coefficients, structural integral, endpoint constants, final margin, and actual-family feasibility/chord obstruction.
- The uniform mean theorem uses **one exponent-44 continuous-h Bernstein certificate** (88 coefficients), then Lyapunov monotonicity for every m<=44. The tail proof uses **one polynomial integral** and uniform bounds over `[35,44]`. No per-m certificate table or quadrature certificate is used. This is a paper proof with exact algebra replay, **not kernel checked**.
- `compare.py`: original C and all H endpoints checked through two representations at **90 and 160 digits**, with identical displayed 60-digit results. Numerical comparisons are explicitly not interval certificates; exact feasibility and chord obstructions do not depend on them.
- No entire-residual proof; no Lean work; no source modifications, commit, or push.

## Artifacts / replay

- `PROOF.md`: complete paper proof and exact obstruction.
- `verify.py`, `cache/exact-verification.json`: exact reconstruction and evidence.
- `compare.py`, `cache/tail-comparison.json`: original-C/structural/chord comparison.
- `probe.py`, `chord_probe.py`, `probe-results.json`: exploratory necessary-moment diagnostics; not proof dependencies.
- Private `.venv/`: numerical dependencies. Exact proof replay does not need it.

Run:

    python3 /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round3/math-polar/verify.py

    /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round3/math-polar/.venv/bin/python /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round3/math-polar/compare.py

Frozen dependency SHA-256:

- `math-middle/PROOF.md`: `41e381086f706a026b8d8bc223b179e4524bc542b1cc900bd8440b9824b05410`
- `math-cutoff45/PROOF.md`: `43c6fe329039cc235037cb2b2c4b31a3c65ba1ad3892aecee17863bb8acf84eb`
