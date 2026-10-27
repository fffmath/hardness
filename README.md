# hardness

Lean 4 / Mathlib / complexitylib formalisations of hardness results for structured lattices
by Yansong Feng and coauthors.

| Subproject | Paper | Lean root | Main result / hypothesis |
| --- | --- | --- | --- |
| [IdealCVP](IdealCVP/README.md) | [Exact CVP Is NP-Complete for Principal Cyclotomic Ideals](IdealCVP/paper/2608.23828.pdf), arXiv:2608.23828 (ePrint 2026/1793) | [IdealCVP.lean](IdealCVP.lean) | Unconditional `IdealCVP.principalCVP_npComplete`, cyclic CVP and rank-two module-SIVP NP-completeness |
| [Rank2ModuleSVP](Rank2ModuleSVP/README.md) | [SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, v2](Rank2ModuleSVP/paper/rank2svp_v2.pdf); v1 arXiv:2609.01469 (ePrint 2026/1856) | [Rank2ModuleSVP.lean](Rank2ModuleSVP.lean) | `Rank2ModuleSVP.moduleSVP_npComplete_of`, conditional on `WanPowerSumEstimates`; NP membership unconditional |
| [Power2ModuleSVP](Power2ModuleSVP/README.md) | [Rank-Two Module SVP in Power-of-Two Cyclotomic Rings](Power2ModuleSVP/paper/power2svp.pdf) | [Power2ModuleSVP.lean](Power2ModuleSVP.lean) | Unconditional `Power2ModuleSVP.moduleSVP_npComplete` and `Power2ModuleSVP.coset_npComplete` |
| [Power2ModuleSVPSubsetSum](Power2ModuleSVPSubsetSum/README.md) | [ModuleSVP^(2)_∞(Z[ζ_(2^k)]) Is NP-Hard](Power2ModuleSVPSubsetSum/paper/power2svp-subsetsum.pdf) | [Power2ModuleSVPSubsetSum.lean](Power2ModuleSVPSubsetSum.lean) | NP-completeness of coefficient ∞-norm rank-two module SVP on Z[X]/(X^n+1), reduction from binary Subset Sum; headline `Power2ModuleSVPSubsetSum.moduleSVP_npComplete`; one-query exact search hardness `moduleSVP_search_turing_npHard` |
| [Power2IdealSVP](Power2IdealSVP/) | [Principal-ideal SVP](Power2IdealSVP/paper/power2-ideal-svp.pdf) | [Power2IdealSVP.lean](Power2IdealSVP.lean) | NP-completeness of coefficient ∞-norm SVP on principal ideals of Z[X]/(X^n+1), reduction from CLIQUE; headline `Power2IdealSVP.idealSVP_npComplete` |

## Layout

Each subproject folder contains a `README.md` with statements and main results, a `NOTES.md`
paper ↔ Lean map, `paper/` with the paper files, `specs/` with scope and research records,
and Lean modules under its matching namespace. Each root import sits at the repository root.
Subproject README file paths are relative to their own folders.

Rank2ModuleSVP also has detailed proof notes in `notes/`. The SVP projects reuse IdealCVP's
lattice, encoding, X3C, Sidon, and certificate infrastructure. Power2ModuleSVP also uses
Rank2ModuleSVP's prime-scan interface.

## Build

Toolchain: `leanprover/lean4:v4.36.0-rc1`, Mathlib `v4.36.0-rc1`, complexitylib pinned at
`ba134c18`; see [lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml), and
[lake-manifest.json](lake-manifest.json). From the repository root:

```sh
/workspace/shared/bin/lake-locked build  # all five libraries (default targets)
/workspace/shared/bin/lake-locked build IdealCVP           # principal-ideal CVP and module-SIVP
/workspace/shared/bin/lake-locked build Rank2ModuleSVP     # odd-prime rank-two module SVP
/workspace/shared/bin/lake-locked build Power2ModuleSVP    # power-of-two rank-two module SVP and principal cosets
/workspace/shared/bin/lake-locked build Power2ModuleSVPSubsetSum
/workspace/shared/bin/lake-locked build Power2IdealSVP
```

Only one Lean build may run on this machine at a time; use the lock wrapper for all builds
and for `env lean` checks.

If the artifact cache is read-only, prefix commands with
`LAKE_CACHE_DIR=/tmp/hardness-lake-cache`.

## Verification

The formalisation uses no proof placeholders or added axioms. Audits of the main theorems
report only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. Rank2ModuleSVP's completeness
result takes `hWan : WanPowerSumEstimates` explicitly; this is a theorem premise, not an added
axiom. IdealCVP, Power2ModuleSVP, and Power2ModuleSVPSubsetSum completeness are unconditional.
IdealCVP's CVPP consequences
assume the stated circuits or polynomial advice and query-time bounds.

The subproject READMEs and `specs/STATUS.md` files describe the theorem scope and verification
records. Native multitape Turing-machine complexity is formalised with complexitylib.
