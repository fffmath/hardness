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

## Dispatcher log
- 693f7c8, 1c1e5e1 (local only): plan; Sidon/Boolean source (semantic, 0 sorry); NP membership both languages (0 sorry); Mahler lemma proved (ElementaryMahlerHypothesis discharged in NormMahler.lean).
- Round 2 (04:00 UTC+8): p2s-gap (NormResultant.lean: ReciprocalResultantHypothesis), p2s-divd (NormDivided.lean: DividedDerivativeWitnessHypothesis), p2s-pack (ParityBlock/Packing/Homogenization/Anchor semantic).
- Next: TM poly-time certificates for source map + packing + homogenization (ReductionMap*), Main assembly with RigidAnchorFamilyHypothesis; then decide on anchor construction.
- cec08f1: ReciprocalResultantHypothesis and DividedDerivativeWitnessHypothesis discharged (NormResultant, NormDivided).
- Round 3 (04:10 UTC+8): p2s-pack still running; launched p2s-srcpoly (SourceMap*.lean TM runtime) and p2s-sepfinal (NormFinal.lean unconditional separation).

## Separation integration (p2s-sepfinal)

`NormFinal.lean` now proves `normSeparationHypothesis_holds` by assembling
the proved Mahler, reciprocal-resultant, and divided-derivative inputs.
`elementary_separation_unconditional` and
`elementary_separation_of_eq_unconditional` remove the hypothesis argument;
`bounded_remainder_separation` has the exact section-4 `natDegree` contract.

`sourceModulus` interprets the finite exponent output of
`BooleanSource.threeSATEncode`. `source_modulus_promises` proves monicity,
the exact degree, the cutoff 64, unit constant, and reciprocal-root
exclusion for every CNF. The latter uses an explicit rational-to-integer
evaluation/reversal bridge. `source_separation` therefore gives `e = 0`
under the cubic dimension bound, degree bound, coefficient bound, and
`SeparationCongruence`, with no extra hypothesis structure.

Validation: `lake env lean Power2ModuleSVP/NormFinal.lean` and
`lake build Power2ModuleSVP.NormFinal` both succeeded. All six exported
assembly/source axiom checks report only `propext`, `Classical.choice`,
and `Quot.sound`. No `sorry`, `admit`, or new axiom was introduced.
No new mathematical gap was found in this integration. The source-facing
height bound remains the explicit premise specified in section 4; proving
it for decoded packing remainders belongs to the packing job. No existing
norm/source files, packing files, root import, or Lake configuration were
edited by this job.

## Source runtime (p2s-srcpoly)

Interface: `SourceInput := ℕ × (ℕ × (List ℤ × List ℤ))`, storing
`(L,(T,(P,c)))`. `encSource` uses unary `L,T`, signed binary integers,
and the established list/pair framing. This raw type is definitionally the
same as packing's `AffineInput`; source files do not import the concurrently
owned packing files. The executable function is
`sourceMap : Cslib.Logic.PL.CNF ℕ → SourceInput`.

`SourceMap.lean` compiles: `sourceMap_eq` identifies the output with
`BooleanSource.threeSATEncode`, replacing its exponent set by its `T+1`
coefficient list; the offset list is unchanged. `sourceMap_polynomial`
identifies the coefficient polynomial with the completed semantic `P`.
`sourceMap_solution_iff` identifies the coefficientwise affine predicates,
and `sourceMap_correct` states
`f ∈ ThreeSAT ↔ ∃ x y, SourceAffineSolution (sourceMap f) x y` for every
CNF, including malformed clauses. `sourceMap_lengths` gives exactly `T+1`
and `L` entries; `sourceMap_dimension_bound` reuses
`1125*(7*f.length+17)*(12*f.length+28)^2`.

`SourceMapAux.lean` implements first-occurrence compression and the numbered
selector gadget using ordinary lists/ranges and proves exact agreement with
`normalizeTotal`/`positiveEncoding`. `SourceMapPrime.lean` reuses
`Rank2ModuleSVP.ReductionMap.primeScan` and its native-TM certificate.
`SourceRuntime.positionPrime_eq` and `SourceRuntime.exponentPrime_eq`
prove equality with both original `Nat.find` choices. The executable map
uses only these bounded scans. Input variable magnitudes never become
unary loop bounds: only occurrence indices are converted to unary.

The unconditional theorem in `SourceMapPoly.lean` is:

```lean
theorem sourceMap_polytime :
  Turing.MultiTapeTM.ComputableTidilyInPolyTime sourceMap
    Cslib.Complexity.encCNF encSource
```

The proof reuses `CNF.isPolyTime_compact`, complexitylib's certified
`toExactThreeSAT`, and the existing native-TM range/map/flatten/lookup/Boolean
scan and unary arithmetic combinators. The finite coefficient scans are
polynomial even on arbitrary raw positive inputs. No oracle, asymptotic-only
runtime argument, new hypothesis structure, or unresolved source premise is
used. `sourceMap_eq` also has exactly the right-hand side of packing's
`threeSATToAffine`, definitionally; the dispatcher can transfer the native
certificate by function extensionality without changing either library.

Validation: successful single-module `lake build` checks for
`SourceMapPrime`, `SourceMapAux`, `SourceMap`, and `SourceMapPoly` (the first
two also built as dependencies of later individual targets). The final
`SourceMapPoly` build succeeded in approximately six seconds after cached
imports. Twelve kernel-computed examples passed, covering both prime scans,
large/repeated binary labels, malformed/empty normalization, numbered gadget
sizes, lower/reflected support membership, and priority of negative offsets;
a separate example checks the exact exported TM signature. Axiom inspection of the two prime equalities, exact map agreement,
source correctness, and the final TM theorem reports only `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, or new axiom occurs
in the four files.

Audit: no new mathematical gap was found. The strict prime intervals are
preserved by equality to the least semantic choices, rather than by assuming
a weak-endpoint prime satisfies strict bounds. Variable compression uses
first occurrence positions (with repetitions in the inventory), so binary
label magnitude cannot cause exponential unary allocation. Root tests and
factorization never occur in the executable map. Packing/homogenization
runtime certificates and final reduction assembly remain outside this job;
no source runtime obligation remains.

## Semantic packing and homogenization (p2s-pack)

Completed semantic P4/P5 in `ParityBlock.lean`, `Packing.lean`,
`Homogenization.lean`, and `Anchor.lean`. Existing source, norm, problem,
coefficient, membership, root, and Lake files were not edited.

`packCoset D q` implements a **zero-padded specialization**: the generator
represents `2*(X^L+P)` and the translation represents `S_(2L)-2*c`, with
exactly `D` coefficients. It omits the manuscript's repeated geometric factor
`F`. This works because zero output coordinates are permitted: cube bounds
and parity force the coset point itself to be two sign words followed by
zeros. The monic-division and separation arguments then apply directly.
The original repeated-block map is not claimed as an implementation.
The total program uses only bounded list maps/ranges, `getD`, arithmetic,
and comparisons; it never decides an algebraic promise.

Principal exports, all in namespace `Power2ModuleSVP`:

* `parity_block`: in every positive degree, a cube product by the geometric
  word implies a cube multiplier. `parity_block_one` forces a signed
  constant under congruence to the constant one; `parity_block_even` forces
  zero under even parity. The general signed-shift form is
  `parity_block_bound`/`parity_block_forcing`.
* `AffineInput` is `(L,(T,(P,c)))`, definitionally matching the runtime
  source's raw `SourceInput`. `AffineYes` uses polynomial bits;
  `affineYes_iff_coefficients` proves its equivalence to the shared `Bits`
  coefficient-vector contract. `sourceToAffine_correct` and
  `threeSATToAffine_correct` reuse the completed Boolean source. All
  well-formedness/root promises are proved; no source hypothesis is added.
* `packCoset_wellFormed` and `packCoset_alphabet` prove validity and the
  alphabets `{0,2}` and `{-1,0,1,3}`. `packCoset_correct hSep` proves
  `AffineYes q` iff `packCoset D q in CosetLang`, assuming valid source,
  dyadic `D`, and `16L^3 <= D`. Completeness needs no separation.
  Soundness proves the remainder's degree/height and calls the existing
  `elementary_separation`. `threeSATToCoset_correct` handles every CNF.
* Executable `dyadicCeil`, `packingBlockSize`, `packingDegree`, and
  `modulePackingDegree` have proved dyadic/size bounds. `packing_degrees`
  proves `2L <= m < 4L` and `m | D`; the chosen coset degree is `<32L^3`,
  and the chosen module degree is `<2^k0+32L^3` above both required cutoffs.
  The zero-padded map does not require block division.
* `homogenization` proves `CosetYes g h` iff `ModuleYes (g,0) (h,J)` for
  nonzero even `g` and a rigid sign `J` in dyadic degree.
  `homogenization_firstMinimum_iff` replaces module YES by attained first
  minimum one. `homogenization_minimum` and `packed_module_minimum` prove
  minimum one on YES and norm at least two for every nonzero vector on NO.
* `triangular_independent`, `triangular_free`, and
  `triangularInput_wellFormed` give nonsingularity, a basis through imported
  `generalBasis`, and exact valid list inputs. `triangularInput_correct`
  gives the language equivalence.
* `threeSAT_module_correct` proves the composite 3SAT/module equivalence
  given a rigid sign anchor at the chosen final degree.
  `threeSATToModule_wellFormed` also covers NO formulas.
  `exists_threeSAT_module_reduction` packages the semantic result under
  `RigidAnchorFamilyHypothesis`, defined exactly as PLAN section 5 in
  `Anchor.lean`, including its uniform native-machine certificate.

Validation: successful single-module `lake build` targets for each of the
four new modules. A temporary Lean audit checked fourteen main exports with
`#print axioms`; all use only `propext`, `Classical.choice`, and `Quot.sound`.
Small `#eval` checks confirmed executable packed arrays and dyadic ceiling
at zero, an exact power of two, and the next integer. No `sorry`, `admit`,
or new axiom occurs in the delivered files. Own scratch was removed.

Audit: no new mathematical error was found. Congruence to one means the
constant polynomial. Zero coset points remain permitted, whereas `(E,J)` is
nonzero because a positive-degree sign anchor is nonzero. The remainder
bound uses high coefficients of the correction quotient and does not
assume squarefreeness. Zero padding is an implementation specialization,
not a claim that the manuscript's repetition is incorrect.

Remaining integration: packing/homogenization native-TM certificates and
NP-hardness/NP-completeness assembly. Separation remains explicitly
parameterized by `NormSeparationHypothesis` as requested; the dispatcher can
instantiate it with `Power2ModuleSVP.normSeparationHypothesis_holds` from
`NormFinal.lean`. Constructing a uniform rigid anchor family remains a
separate obligation. No runtime claim for the composite maps is made here.
- f8baa84: packing/homogenization/anchor contract, NormFinal (separation unconditional), SourceMap runtime. 
- Round 4 (04:25 UTC+8): p2s-main (ReductionMap*/Main: coset_npComplete, moduleSVP_npComplete_of hJ), p2s-repair (AnchorSeedSpec/Screen/DisjointTests/Repair), p2s-seed (Bernstein/SineKernel/SeedIntervals/PartialColoring).

## Main assembly (p2s-main)

Completed P5 complexity assembly in `ReductionMap.lean`,
`ReductionMapAux.lean`, `ReductionMapPoly.lean`, and `Main.lean`.
Only these four new Lean files and this appended section were changed by
this job. Existing source, separation, packing, homogenization, membership,
anchor, root, and Lake files were reused without edits.

`sourceMap_eq_threeSATToAffine` proves exact agreement of the executable
source tuple and the semantic affine interface. `cosetReduction` packs
`sourceMap` at `packingDegree L`; `cosetReduction_correct` proves
`f ∈ ThreeSAT ↔ cosetReduction f ∈ CosetLang` for every CNF, with
`normSeparationHypothesis_holds` discharging separation unconditionally.
Well-formedness, coefficient alphabets, and explicit cubic degree bounds
(also composed with the source's clause-count polynomial) are exported.

Native multitape-TM certificates are `dyadicCeil_polytime`,
`packingDegree_polytime`, `modulePackingDegree_polytime`,
`packCoset_polytime`, and `triangularInput_polytime`. They reuse
complexitylib's certified unary logarithmic power, range/map/lookup,
signed-binary arithmetic, and pair/list constructors. The packing
certificate holds on every raw input tuple. It charges the explicit unary
output degree and both coefficient arrays, not merely binary arithmetic
on the degree. `cosetReduction_polytime` composes it with
`sourceMap_polytime`; `threeSAT_polyTimeReducible_coset` packages the
actual total reduction and correctness.

`moduleReductionDegree k0` computes the final module degree in unary;
`moduleReductionDegree_polytime` certifies this function directly from
`encCNF`. `moduleReduction k0 J` packs the affine input at that degree,
runs the supplied uniform anchor program on the same unary degree, and
attaches the anchor with the triangular constructor.
`moduleReduction_polytime` composes all three certificates.
`moduleReduction_eq` and `threeSATToModule_polytime` also expose exact
agreement with the existing semantic map. Correctness, well-formedness,
all four coefficient promises, and polynomial degree bounds are proved.
The only module premise is the existing uniform anchor hypothesis;
`threeSAT_polyTimeReducible_moduleSVP_of` extracts its fixed cutoff,
family, native-machine certificate, and anchor specification.

The final namespace-`Power2ModuleSVP` statements are:

```lean
theorem coset_npHard : NPHard encCoset CosetLang
theorem coset_npComplete : NPComplete encCoset CosetLang
theorem moduleSVP_npHard_of (hJ : RigidAnchorFamilyHypothesis) :
  NPHard encSVP ModuleSVPLang
theorem moduleSVP_npComplete_of (hJ : RigidAnchorFamilyHypothesis) :
  NPComplete encSVP ModuleSVPLang
```

`moduleReduction_gap` states, for any family satisfying the anchor
specification, that the actual stored module columns have attained
`FirstMinimum ... 1` on YES formulas and that every nonzero module vector
has `pairSup ≥ 2` on NO formulas. Integrality and the proved language
equivalence suffice; it introduces no further analytic premise.

Validation: single-module builds for `ReductionMap` and
`ReductionMapAux`, direct Lean checks for `ReductionMapPoly` and `Main`,
and the final single-target `lake build Power2ModuleSVP.Main` compile all
four modules. The five `#print axioms` commands retained in `Main.lean`
report only `propext`, `Classical.choice`, and `Quot.sound`, including both
completeness theorems and the gap theorem. No `sorry`, `admit`, new axiom,
or new hypothesis structure occurs in this job's Lean files.

Audit: no new mathematical gap was found in assembly. The cutoff exponent
is fixed before forming a reduction, so `2^k0` is a constant in its runtime
bound. The anchor machine receives the final degree; no change of quotient
ring by padding an already constructed general coset is assumed. Both
reductions retain the existing total malformed-CNF behavior.

Open work: construct the uniform rigid anchor family to remove the module
hypothesis. Root-file import integration remains the dispatcher's task;
this job did not edit `Power2ModuleSVP.lean` or `lakefile.toml`. Coset
hardness/completeness and all requested composite runtime certificates
have no remaining proof obligation.
