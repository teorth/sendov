# Outcome

For the ORIGINAL square-root-C centered majorant, with actual complex mean and actual variance, full complex-integral feasibility, m>=7 and 9/10<=a<1, write h=1-a and lambda=mh.

| Continuous proved domain | Certified paper bound |
|---|---|
| lambda<=1/4, all allowed v | E+Gamma <= 1-au-(79/504)h |
| lambda>=100, all allowed v; no upper cutoff | E+Gamma <= h/15+(157/1000)v <= 1-au-(14/15)h-(293/1000)v |
| Any lambda, provided v<=h/m^2 | E+Gamma <= (821/840)h <= 1-au-(19/840)h |

The remaining open region is exactly the complement of this coverage: **1/4<lambda<100 and v>h/m^2**. No counterexample or global resolution is claimed.

## Main new mechanisms

- Use the actual-variance contribution to the target: `1-au >= h+av/2`. This permits a tail bound linear in v and substantially enlarges the low-lambda regime.
- Recover a logarithmic endpoint constraint from the raw-polar integral, not just the older rational b bound. For `R^2=1+(1-a^2)(1-b)` and `L=(m+1)h`, norm convexity gives `R^(m+1)>=L`, hence

      b^((m-3)/2) <= L^(-(m-3)/((m+1)(1-a^2))).

  For lambda>=100 this yields `m^(5/2)b^((m-3)/2)<=320/lambda^2`. Split the structural integral at t=1/4 to obtain the uniform unbounded-lambda result.

The parent's lambda<=4/39 derivation was independently checked and is valid, including the endpoint constant 15680/15944049<1/1000 and total 8909/9000<99/100.

## Files and verification

- `PROOF.md`: complete paper arguments, exact domains, all constants, parent-proof check, and explicit unproved complement.
- `verify.py`: standard-library-only exact Fraction/integer replay; no floating arithmetic or grids, no filesystem writes.
- `VERIFICATION.txt`: execution receipt.

Executed `python3 /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round2/math-bound/verify.py` successfully: **53 exact checks passed, exit 0**. This includes two actual positive-variance full-complex-integral feasible witnesses, one lying only in the new large-lambda domain.

These are paper proofs plus exact constant/identity checks, **not newly kernel-checked Lean theorems**. The structural-tail proof and the scalar/logarithmic analytic arguments remain to be formalized. No other source, cache, or directory was intentionally edited.
