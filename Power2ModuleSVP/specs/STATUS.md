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

## API/NP (p2s-api)

Completed P0 and P1 on 2026-10-25. All declarations use namespace
`Power2ModuleSVP`; importing `Power2ModuleSVP.Membership` exposes both final
NP theorems. This job created only `Coefficient.lean`, `Problem.lean`,
`MembershipAux.lean`, `MembershipPoly.lean`, `MembershipCert.lean`, and
`Membership.lean`, and appended this status section. Root imports and Lake
configuration remain the dispatcher's integration task.

The section-4 coefficient and language interfaces are implemented exactly:
`Coeff`, `Rd`, `Dyadic`, `Cube`, `Signs`, `Bits`, `EvenCoeffs`,
`SignedMonomial`, `Rigid`, `coeffSup`, `pairSup`, `CosetYes`, `moduleVector`,
`ModuleYes`, both input types/encodings/well-formedness predicates/languages,
`CosetBits`, `ModuleSVPBits`, and `FirstMinimum`. `encCoset_mem_iff` and
`encSVP_mem_iff` identify encoded membership with semantic membership.
Degree zero and malformed lengths are rejected; degree one is included.
The columns follow the specified orientation. Zero is allowed for the coset
point and excluded for the accepted module vector.

Executable checks are `cosetWellFormedCheck`, `moduleWellFormedCheck`,
`listCube`, `listEven`, `cosetVerifier`, and `moduleVerifier`.
`cosetWellFormedCheck_spec`, `moduleWellFormedCheck_spec`,
`cosetVerifier_spec`, and `moduleVerifier_spec` prove their full semantic
specifications. The requested equivalences are proved as
`cosetVerifier_correct (x) : x ∈ CosetLang ↔ ∃ u, cosetVerifier (x,u) = true`
and
`moduleVerifier_correct (x) : x ∈ ModuleSVPLang ↔ ∃ uv, moduleVerifier (x,uv) = true`.
`cosetVerifier_polytime` and `moduleVerifier_polytime` have exactly the
section-4 native multitape-TM encoding signatures. All runtime proofs compose
imported certified list/integer routines, including negacyclic products,
dyadic recognition, determinant checking, and coefficient scans. Parity is
computed as binary `natAbs % 2`, with its equivalence to `Even` proved.

The final unconditional results in `Membership.lean` are:

```lean
theorem coset_mem_NP : CosetLang ∈ Cslib.Complexity.NP encCoset
theorem moduleSVP_mem_NP : ModuleSVPLang ∈ Cslib.Complexity.NP encSVP
```

Certificate bounds reuse the stronger applicable nonsingular-matrix route
from IdealCVP instead of introducing another integer-preimage development.
`Cube.sqNorm_le` gives the bounds `d` and `2d`. The existing
`certificate_coeff_le`, `multiplicationMatrix_det_ne_zero`,
`generalMatrix_det_iff`, `moduleBoundInput_dominates`, and
`cvpCertificateBound_bits` bound the original accepted multipliers.
`Membership.coset_certificate_bound`, `Membership.module_certificate_bound`,
`Membership.coset_certificate_length`, and
`Membership.module_certificate_length` include all signed-binary/list/pair
framing. Auxiliary bound-input maps have native polynomial-time certificates;
their encoding-length polynomials compose with the existing witness
polynomials. The final NP proofs reuse `intBinDecoder.list`, its pair, and
`mem_NP_of_witness`. In particular, no solver runtime or new analytic,
separation, anchor, or resource-bound hypothesis is assumed.

Validation: successful single-module `lake build` checks for all six owned
modules, with final dependencies also rebuilt through
`lake build Power2ModuleSVP.Membership`. A temporary Lean check passed twelve
kernel-computed examples covering degree-one YES instances, zero module
rejection, zero/odd coset generator rejection, singular matrices, excessive
coefficients, zero/nondyadic degree, and malformed arrays.
`#print axioms` for both final NP theorems reports only `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, new axiom, or new
hypothesis structure occurs in these files.

Audit: no mathematical gap was found in the NP argument of the private
reduction section. The paper's rational-elimination verifier can be replaced
by the proved bounded-multiplier verifier because the promised bases are
nonsingular. Squared norms occur only in certificate estimates; acceptance
uses the coefficient sup norm throughout. There are no open P0/P1 proof
obligations. Hardness, homogenization, and root-file integration are outside
this job's ownership and are not claimed here.
