# Uniform binomial coefficient bound — verified

## Outcome

The full requested coefficient inequality is proved for the actual imported
`Sendov.PaperCenteredBound.C`, including its top and out-of-range branches:

```lean
theorem Sendov.PaperBinomialMode.C_sq_le_binomial
    (m k : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    Sendov.PaperCenteredBound.C m k v ^ 2 ≤
      (2 * (k : ℝ) + 1) * (m.choose k : ℝ) * v ^ k
```

There are no degree restrictions, tables, custom axioms, or unproved premises.
The coefficient assembly itself has no missing steps. Integration into project
root modules and the subsequent high-degree Cauchy–Schwarz tail estimate are not
performed by this isolated task.

## Sources and theorem names

All theorem names below have prefix `Sendov.PaperBinomialMode.`.

- `FirstMoment.lean`: `ramp_sum`, `first_moment_mass_bound`,
  `probability_max_mass`.
- `BinomialMode.lean`: definition `weight`; theorems `weight_nonneg`,
  `weight_sum`, `weight_adjacent`, `weight_mode`, `weight_first_moment_succ`.
- `CoefficientBound.lean`: `integer_mean_identity`,
  `entropy_coefficient_bound`, `C_sq_le_binomial`.

`probability_max_mass` says that if a finite nonnegative distribution on any
finite subset of naturals has total mass 1 and mean k, any nonnegative upper
bound P on all masses satisfies `1 / (2*k+1) ≤ P`.

Its homogeneous form `first_moment_mass_bound` proves `T ≤ (2*k+1)*P` when total
mass is T and first moment is k*T. The proof truncates the signed ramp at 2*k+1
and sums it exactly, so it does not assume the support size is controlled by k.

The binomial proof uses the unnormalized masses

    weight m x y j = choose(m,j) * x^j * y^(m-j).

At x=k and y=m-k (real subtraction), the adjacent identity is

    (j+1)*(m-k)*weight(j+1) = (m-j)*k*weight(j).

It implies increase before k and decrease after k, hence the universal mode
lemma for `0<k<m` and `j≤m`. Total mass is m^m and first moment k*m^m.
The homogeneous first-moment theorem therefore yields the entropy estimate
without introducing normalized-probability denominators. The final theorem
handles the actual C interior by `Real.sq_sqrt`, the top branch directly, and
all remaining branches by zero/nonnegativity.

## Verification and receipts

Run:

```sh
python3 /home/v-zhouziyu/work/sendov-paper-formalization-20260914-remaining-centered/research/centered-round2/lean-mode/verify.py
```

The final run freshly elaborated all three modules and separately ran
`leanchecker` on each, serially. All six processes exited 0, with no final
compiler warnings. All printed axiom sets are exactly
`[propext, Classical.choice, Quot.sound]`.

- `VERIFIED.json`: source/object SHA-256 hashes, theorem inventory, six receipt paths.
- `.lake/paper/logs/verified-{FirstMoment,BinomialMode,CoefficientBound}.json`:
  final elaboration command, pinned environment, timing and exit code.
- Corresponding `.log` files: actual axiom-audit stdout.
- `.lake/paper/logs/verified-*-kernel.json`: independent kernel-check receipts.

The private object directory was seeded with a complete recursive set of 439
per-file symlinks from the supplied read-only project cache, with no broken
links. `run.py` unlinks every target object/output before each elaboration and
uses the provided project runner with its pinned configuration. No Lake build,
package installation, project-root source edit, or sibling-directory edit was
performed. Earlier failed iteration logs are retained but are not acceptance
receipts; only the `verified-*` receipts bind the final source.
