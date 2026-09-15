# Degree-uniform endgame: review material

Local contribution: **subfish-zhou (GitHub)**. Original authorship and mathematical
attributions are retained in the note and repository notices.

- [Mathematical review note](MATHEMATICAL_NOTE.md): scalar theorem, inherited inputs,
  the degree-ray argument and the limits of this exposition.
- [Exact coefficient data](CERTIFICATES.json): three complete identities of degrees
  53/47/47 and their low-degree homogeneous factors.
- [Replay script](check_note_certificates.py) and [local result](CERTIFICATE_REPLAY.json).

The note describes mathematical source commit
`c7f25171a07b916a678b0df1dbd32ee55eb5e4df`. These accompanying documents do not change
that proof. The later 9/9/18 experiment is not included.

With Python and SymPy 1.13.1 available, run from the repository root:

```sh
python docs/degree-uniform/check_note_certificates.py
```

The script reads the adjacent note and data, reconstructs the complete rational
polynomial identities, and rejects three internal-coefficient mutations. It writes
`CERTIFICATE_REPLAY.json` beside itself. This is supplementary exact-arithmetic
verification, not a replacement for the analytic lemmas, Lean's kernel, or the
repository's documented proof audit.

**Intermediate API migration:** `Sendov.polar_origin_incompatible` now requires
`6 <= n`, rather than upstream's `5 <= n`. The final conjecture statements are
unchanged; degree five uses the existing polynomial low-degree argument in
`Interior`. The former standalone scalar interface is not preserved at degree five.
The old `R`/FiniteRange/LargeDegree route is retired, not retained as a second proof.

Tao's original production history remains accessible in the fixed upstream tree:
[README and provenance](https://github.com/teorth/sendov/tree/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d),
[original making-of document](https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/docs/making-of.md).
The new local development does not replace attribution of that original work.
