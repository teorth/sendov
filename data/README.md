# Exact mathematical table

`paper_certificate_table.json` is the unchanged ordered subset of records
`m = 5,...,64` (60 records) from Senjian An's mathematical certificate table,
*Proof Distillation for Sendov's Conjecture*,
[SJanPerth/Sendov-Proof-Distillation](https://github.com/SJanPerth/Sendov-Proof-Distillation/blob/e8ae601491ec171ab4f7f8456113dd6a047aa85d/verification/paper_certificate_table.json),
fixed revision **e8ae601491ec171ab4f7f8456113dd6a047aa85d**.

The mathematical paper/table is attributed under
[Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/);
`LICENSE-PAPER.txt` retains the source's notice and legal-code link. No table
values, retained row order, component IDs/order or budgets were changed. Records
65 through 81 were removed because the proved real-parameter tail now starts
at 64 and uses the original row-64 budget. This is a selected subset, not a
verbatim copy of the complete donor table. The project generates
its own Lean certificate source; the table itself is not a formal proof.

The upstream verification **code** has a separate MIT license. The small rational
checks adapted in `scripts/distillation_data.py` retain its notice in
`scripts/LICENSE-DISTILLATION-MIT.txt`; this does not relicense the mathematical
table as MIT or imply adoption of an upstream formal proof.
