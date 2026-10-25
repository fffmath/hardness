# hardness

Lean 4 / Mathlib / complexitylib formalisations of NP-hardness results for structured lattices
by Yansong Feng and coauthors.

| Subproject | Paper | Lean root | Status |
|---|---|---|---|
| [`IdealCVP/`](IdealCVP/README.md) | *Exact CVP Is NP-Complete for Principal Cyclotomic Ideals*, arXiv:2608.23828 (ePrint 2026/1793) | `IdealCVP.lean`, modules `IdealCVP.*` | complete: sorry-free, axiom-clean NP-completeness |
| [`Rank2ModuleSVP/`](Rank2ModuleSVP/README.md) | *SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules* (v2, odd primes q; v1 arXiv:2609.01469) | `Rank2ModuleSVP.lean`, modules `Rank2ModuleSVP.*` | done: `Rank2ModuleSVP.moduleSVP_npComplete_of`, NP-complete given the sole named hypothesis `WanPowerSumEstimates` |
| [`Power2ModuleSVP/`](Power2ModuleSVP/README.md) | *Rank-Two Module SVP in Power-of-Two Cyclotomic Rings* | `Power2ModuleSVP.lean`, modules `Power2ModuleSVP.*` | complete: unconditional `Power2ModuleSVP.moduleSVP_npComplete` and `coset_npComplete`, sorry-free, axiom-clean |

Each subproject folder contains its `paper/` (PDF), `README.md`, `NOTES.md`
(paper ↔ Lean map) and `specs/` (plans and status log; the per-round Codex prompts are kept in git history only). `Rank2ModuleSVP` and `Power2ModuleSVP` import
the shared infrastructure from `IdealCVP` (lattice norms, X3C, Sidon sets, complexity encodings,
NP certificate bounds) rather than duplicating it.

## Build

Toolchain `leanprover/lean4:v4.36.0-rc1`, Mathlib `v4.36.0-rc1`, complexitylib pinned at
`ba134c18` (see `lakefile.toml`). From the repository root:

```
timeout 3000 lake build            # all three libraries
lake build IdealCVP                # one library
```

If the toolchain artifact cache is read-only, prefix with `LAKE_CACHE_DIR=/tmp/hardness-lake-cache`.
