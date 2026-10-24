# hardness

Lean 4 / Mathlib / complexitylib formalisations of NP-hardness results for structured lattices
by Jiaqi Liu, Yansong Feng and Yanbin Pan.

| Subproject | Paper | Lean root | Status |
|---|---|---|---|
| [`IdealCVP/`](IdealCVP/README.md) | *Exact CVP Is NP-Complete for Principal Cyclotomic Ideals*, arXiv:2608.23828 (ePrint 2026/1793) | `IdealCVP.lean`, modules `IdealCVP.*` | complete: sorry-free, axiom-clean NP-completeness |
| [`Rank2ModuleSVP/`](Rank2ModuleSVP/README.md) | *SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules*, arXiv:2609.01469 (ePrint 2026/1856) | `Rank2ModuleSVP.lean`, modules `Rank2ModuleSVP.*` | in progress |

Each subproject folder contains its `paper/` (PDF + LaTeX source), `README.md`, `NOTES.md`
(paper ↔ Lean map) and `specs/` (plans, Codex prompts, status log). `Rank2ModuleSVP` imports
the shared infrastructure from `IdealCVP` (lattice norms, X3C, Sidon sets, complexity encodings,
NP certificate bounds) rather than duplicating it.

## Build

Toolchain `leanprover/lean4:v4.36.0-rc1`, Mathlib `v4.36.0-rc1`, complexitylib pinned at
`ba134c18` (see `lakefile.toml`). From the repository root:

```
timeout 3000 lake build            # both libraries
lake build IdealCVP                # one library
```

If the toolchain artifact cache is read-only, prefix with `LAKE_CACHE_DIR=/tmp/hardness-lake-cache`.
