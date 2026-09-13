# Active proof generators

Use Python 3.10+; only `gen_sinh.py` needs SymPy (tested with 1.13.1).
`gen_distillation.py`, its exact-data validator and bundler use only the standard
library. Run these commands from the repository root:

```sh
python3 -m pip install 'sympy==1.13.1'  # if not already installed
python3 -B scripts/gen_sinh.py --output /tmp/sendov-Sinh.lean
python3 -B scripts/gen_distillation.py --output /tmp/sendov-distillation-new
python3 -B -m unittest discover -s tests -v
```

The finite output directory must be new or empty. The generator emits all
`m = 5,...,55,61`, components `0,1,2`, with the unchanged selected table records.
Rows are grouped in contiguous batches of at most eight, ending in `Rows53_55`
and `Rows61_61`; a group never spans a gap in retained degrees. The finite
aggregate covers 5–60 using rows 5–54 and the real interval theorem 55–61,
whose base is the original row 55. The real tail starts at 61 and uses the original row-61
`<199/200` budget from that same group. The output contains exactly these
eight row modules and `Sendov/Common/DistillationFinite.lean`. No second per-row
source tree is published. `bundle_rows.py` is the source-packaging helper, not a
certificate checker or an alternative proof route.

`--output` is required for distillation; there is no subset/mutation CLI or
workspace restriction. Paths can be absolute or relative to the caller's cwd.
`--table /path/to/table.json` explicitly overrides the default project-local
`data/paper_certificate_table.json`; the same exact schema, ordered coverage,
bracket, sign, squared-envelope and budget checks apply. Editing that input
changes a proposed certificate, not the proof trust base. Keep the shipped table
unchanged to reproduce the selected source. `distillation_data.py` is the explicit
range authority, paired with `distillComponents_lt_199_200`; truncated inputs
cannot select a different cutoff. In particular, missing55, missing61, reintroduced56, extra62, duplicate
or reordered rows, and duplicate/reordered/mismatched components are rejected.

All data validation and exact row rendering finish before staging. The complete
grouped snapshot is then staged beside the target and committed by one directory
rename. Nonempty targets, regular files and symlinks are rejected; handled
render/write/rename failures leave prior target contents intact and clean private
staging. This is an atomic publication guarantee on a local filesystem with a
trusted parent directory, **not** a power-loss durability guarantee or protection
against malicious concurrent same-user namespace changes. Interrupted runs may
leave private `.distillation-*` staging; no partially published Lean tree is used.

Sinh's optional default is `Sendov/Common/Sinh.lean` relative to the script's
repository, not the caller's cwd. Its existing atomic single-file writer replaces
that file only after complete rendering. Imports perform no generation; `-B`
suppresses Python's own bytecode cache writes. Explicit outputs are recommended.

**Python生成≠Lean验收** — exact Python checks and byte-identical regeneration are
not Lean elaboration or kernel replay. After integrating the generated modules
into the selected proof and building it with the pinned project toolchain, run:

```sh
lake env lean scripts/axioms.lean
sh scripts/audit.sh
```

The two public conjectures and the finite/tail seams are queried, not retired
route names. The shell audit fails if the Lean query itself fails. Full Lean
build/kernel replay and the two headline type contracts remain separate gates.

## Attribution and licenses

- Sinh, its analytic tail and the retained proof templates derive from Terence
  Tao's Sendov development (Apache-2.0); original notices are preserved.
- Mathematical table/route: Senjian An, *Proof Distillation for Sendov's
  Conjecture*, [fixed revision e8ae601491ec171ab4f7f8456113dd6a047aa85d](https://github.com/SJanPerth/Sendov-Proof-Distillation/tree/e8ae601491ec171ab4f7f8456113dd6a047aa85d).
  Retained records are an unchanged ordered subset, not the full donor table;
  see `../data/README.md` for CC BY 4.0 attribution.
- The rational envelope checks in `distillation_data.py` adapt that revision's
  explicitly MIT-licensed `verification/verify_paper.py`; the original Senjian An
  copyright/permission notice is retained in `LICENSE-DISTILLATION-MIT.txt`.
  This is licensed adaptation, not copying code from an unlicensed donor.
- New renderer, schema/CLI integration, bundling and test changes are Apache-2.0;
  see the project `LICENSE` and the retained `LICENSE-APACHE-2.0.txt` copy.
