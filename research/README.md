# Centered C-near research

The current reviewed result is in **[centered-global-verified/REPORT.md](centered-global-verified/REPORT.md)**, with machine-readable status in [RESULT.json](centered-global-verified/RESULT.json) and a [verified archive](centered-global-verified.zip).

For natural `m >= 7` and `9/10 <= a < 1`, the reviewed paper proof establishes

```
E_fin + Gamma <= 1 - a|mu| - (1-a)/20 < 1 - a|mu|
```

under the unchanged original FULLpolar and pointwise unit-disk constraints, using the actual complex mean and centered variance. This is finite-band certificate mathematics, not per-degree majorant testing and not a certificate-free formula.

**Global Lean/kernel closure is not complete.** The archive contains fully checked near/variance-strip consumers and generic structural, moment, Bernstein and band consumers. Concrete global certificate instantiations and the unbounded cutoff remain to be formalized. The final report and receipts distinguish mathematical arguments, exact Python certificates, numerical evidence and kernel-checked domains.

From `centered-global-verified/`:

```sh
python3 -B verify.py
python3 -B verify.py --full-rational
# Requires a compatible pinned project/cache:
CENTERED_PROJECT=/path/to/project CENTERED_CONFIG=/path/to/config.json python3 -B verify.py --rebuild
```

The numbered round directories and earlier `centered*` snapshots preserve the research history, including failed approaches, intermediate claims and diagnostics. Their older OPEN/PENDING descriptions are historical and are superseded by the final report. Exploratory scripts are not the current acceptance entry point. Source, reports, exact evidence and replay scripts are retained; `.lake`, virtual environments and Python caches are intentionally not versioned.
