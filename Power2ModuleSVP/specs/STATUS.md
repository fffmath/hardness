# Power2ModuleSVP — final structure status

Phase 1 restructures the completed proof without changing surviving mathematical statements.
Both unconditional completeness results are in `Main.lean`:
`moduleSVP_npComplete : NPComplete encSVP ModuleSVPLang` and
`coset_npComplete : NPComplete encCoset CosetLang`.
NP membership is in `Membership/NP.lean`.

The reusable anchor and seed interfaces are preserved:
`moduleSVP_npComplete_of`, `rigidAnchorFamily_of_seed`, and
`moduleSVP_npComplete_of_seed`. `Seed/Family.lean` assembles the concrete certified seed.
The obsolete universal full-coloring runtime contract and stale final wrappers are removed.
`SidonAudit.lean` contained only historical prose and was outside the main import closure.
All 181 surviving modules are imported transitively by `Main` and listed in the sorted root.

## Layout and paper map

See [../README.md](../README.md) for the folder layout and proof route,
[../NOTES.md](../NOTES.md) for the paper-to-Lean map, and
[RENAMES.md](RENAMES.md) for every old-to-new path and the dead-code audit.
All Lean modules have titled module docstrings with paper-section references.
PLAN and AUDIT reports retain historical findings and pre-restructure line references;
their opening notes point to the rename map. The old per-job status log remains in git history.

## Verification

Dead-code, structure, and module-docstring full builds passed (8572 jobs each).
Final `/workspace/shared/jobs/hardness-tidy/build.sh Power2ModuleSVP` passed (8572 jobs).
Both headline statements and the three preserved conditional signatures are unchanged.
The Lean-source scan for prohibited proof escapes and scratch commands is empty.
Under the shared lock, `lake env lean /tmp/ht-p2-axioms.lean` reports only
`propext`, `Classical.choice`, and `Quot.sound` for each main theorem.
All root imports and README/NOTES/RENAMES links were checked; no outside Lean module imports
Power2 modules. Logs: `/tmp/ht-p2-final-build.log`, `/tmp/ht-p2-axioms.log`.
Warnings: 339 → 327 including module-system notes; 305 → 293 excluding those notes.
Eleven baseline header warnings disappeared through the earlier shared linter setting;
the newly documented constraints module accounts for the remaining decrease.

## Remaining caveats

Per-file lint polishing is a later phase; this phase preserves existing proof scripts.
The paper's search-approximation consequence is not a separate formal search reduction;
`moduleReduction_gap` proves the integral decision gap on the stored reduction images.
Some historical audit findings describe interfaces discharged or removed by the final assembly.
