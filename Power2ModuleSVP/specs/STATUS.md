# Power2ModuleSVP status

Phase: phase-one research and plan completed by `p2s-plan` on 2026-10-25;
implementation is underway in other jobs. [PLAN.md](PLAN.md) specifies both
languages, reusable APIs, every labelled proof dependency, proposed Lean
interfaces, hypothesis boundaries, audits, and a three-lane work schedule.

Recommended first theorem milestone: unconditional `coset_npComplete` and
`moduleSVP_npComplete_of (hJ : RigidAnchorFamilyHypothesis)`. The hypothesis
must include one uniform native-TM polynomial-time anchor family on unary
degree. If separation remains a hypothesis, both completeness statements
must expose that additional premise.

Existing reusable foundations: the power-of-two quotient/domain and list
arithmetic, polynomial-time ring-determinant checks, integer-preimage witness
bit bounds, canonical Fourier identity, quadratic Sidon positions, and
`ExactThreeSAT` reductions. Reuse imports; earlier prime-ring squared-norm
SVP and two-vector SIVP languages are different problems.

Observed concurrent files (existence only, not a compilation claim by this
job): `BooleanSource*.lean`, `Sidon*.lean`, `NormSeparationAux.lean`,
`NormSeparation.lean`, and the root stub. Lake already has a new library
entry; `defaultTargets` has not yet been extended. These files and Lake
configuration were not changed by the planning job.

Validation: all six private-paper Python checks passed sequentially from
`/tmp`, with bytecode writes disabled. They cover finite source, algebra,
resultant, repair, grid, and analytic-constant checks; they are not formal
proofs. No Lean files were written or compiled by `p2s-plan`. Proposed
signatures in the plan are design contracts, not compiled declarations.

The norm draft currently assembles `elementary_separation` conditional on
`NormSeparationHypothesis`, extending three explicit hypotheses for the
power-sum witness, reciprocal radial-gap bound, and divided-derivative
extraction. A source draft also exposes `RowIsolationHypothesis`. These
remaining fields and their runtime implications must stay visible.

Open work: exact language/encoding API; NP verifiers; full sparse-source map
and its TM certificate; complete Mahler/resultant/multiplicity separation;
parity packing; conditional homogenization and final assembly. Full anchor
analysis, rational coloring and uniform TM complexity are the largest
optional follow-on development. No new fatal mathematical error was found;
the plan records strict prime endpoints, compact variable labels, repeated
factors, small-degree handling, parity, and obsolete audit constants.

Next: freeze the shared interfaces with the source/norm owners; assign at
most three jobs to API/NP/packing, source/runtime, and separation; compile
owned modules one at a time. Preserve the explicit hypotheses until their
proofs and runtime certificates exist.

Dispatcher context retained: round 1 began at 2026-10-25 03:20 UTC+8 with
`p2s-plan` (specs), `p2s-norm` (`NormSeparation*.lean`), and `p2s-sidon`
(`Sidon*/BooleanSource*.lean`). Dependency setup was already performed by the
dispatcher; prompts are in `/workspace/shared/jobs/_p2s`. Before relaunching,
check `cx-status p2s-*`, git status, and this file. Do not update or clean
dependencies or modify shared package trees.
