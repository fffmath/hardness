# Power2ModuleSVP status

**Current state (2026-10-25 07:50 UTC+8, local commits only, nothing pushed).**
Working copy: /workspace/shared/projects/hardness. Build: `lake build Power2ModuleSVP`.

Proved, 0 sorry, axioms only propext/Classical.choice/Quot.sound:
- `coset_mem_NP`, `moduleSVP_mem_NP` (Membership.lean)
- `coset_npHard`, `coset_npComplete : NPComplete encCoset CosetLang` (Main.lean), UNCONDITIONAL
  (3SAT -> Sidon sparse source -> principal coset; separation fully proved in Norm*.lean).
- `moduleSVP_npComplete_of (hJ : RigidAnchorFamilyHypothesis)` (Main.lean), `moduleReduction_gap`.
- `rigidAnchorFamily_of_seed`, `moduleSVP_npComplete_of_seed (h : SpectralSeedFamilyHypothesis)`
  (AnchorRepairPoly2.lean): repair semantics + native runtime done.
- `spectralSeedFamily_of A hA hAt hK hP hT` (FlatSeedMain.lean): seed assembly conditional.
  hK (sine kernel) proved (`sineKernelDecompositionHypothesis_holds`);
  partial-coloring semantics proved (`partialColor_correct`, ColoringTrajectory.lean).

Remaining for the unconditional `moduleSVP_npComplete`:
1. Native TM certificates for partialColor / fullColor (`PartialColoringNativeHypothesis`,
   `FullColoringNativeHypothesis partialColor`; per AUDIT2 the old `FullColoringRuntimeHypothesis`
   is unsatisfiable and must NOT be used). p2s-colornative delivered primitives + denominator
   bounds (ColoringNative*.lean, commit 4294034); p2s-colornative2 (e1184e0) reduced projector part to
   `CanonicalProjectorDenominatorHypothesis`; remainder -- job p2s-colornative3.
2. Concrete frontend `flatFrontend` (100a3e7); all rational enclosures proved (29b9df8);
   `flatFrontend_preparation_of_geometry (hG : MarkedRunGeometryHypothesis)` -- remaining
   six marked-run geometry estimates -- job p2s-frontend3.
3. DONE: `flatFrontend_runtime : FlatSeedFrontendRuntimeHypothesis flatFrontend` (FlatFrontendRuntime.lean), unconditional.

Resume protocol: check `cx-status p2s-*`, `git status`, this file; prompts in /workspace/shared/jobs/_p2s.
Historical sections below (per job) are kept for detail; the Phase-1 text further down is superseded.

## Phase-1 notes (superseded)

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

## Flat seed analysis (p2s-seed)

Added six independently checkable modules: `Bernstein.lean`,
`Chebyshev.lean`, `ChebyshevTrig.lean`, `SeedIntervals.lean`,
`SineKernel.lean`, and `PartialColoring.lean`. This job did not edit existing
Lean sources, the root import file, or the Lake configuration.

**Sharp Bernstein is unconditional.** `bernstein_interpolation` proves the
finite interpolation identity at the roots of `X^(2*n)+1`.
`bernsteinWeight_sum` proves that the nonnegative absolute weights sum to
`n`. The resulting `bernstein_polynomial_circle_bound` gives
`norm(z*P'(z)-n*P(z)) <= n*M` for degree at most `2*n` and a circle bound
`M`. `HasTrigDegree` expresses exact centered Laurent evaluation, including
zero imaginary part. It is closed under every iterated derivative, and

```lean
bernstein_real_iterate (hT : HasTrigDegree n T)
  (hM : ∀ θ, |T θ| ≤ M) (r : ℕ) (θ : ℝ) :
  |(deriv^[r] T) θ| ≤ (n : ℝ)^r * M
```

holds also in degree zero. `hasTrigDegree_trigSum` constructs the Laurent
representation for arbitrary finite real sine/cosine sums with frequencies
at most `n`; `bernstein_trigSum` exposes the same derivative estimate in
that notation. `hasTrigDegree_cosinePolynomial` connects it to the grid API.

**Sampling estimates are unconditional, but interval geometry is unfinished.**
`chebyshev_U_eval_bound` and `chebyshev_derivative_eval_bound` prove
`|U_n(x)| <= n+1` and `|T_n'(x)| <= n^2` on the closed interval `[-1,1]`.
`SeedCosineData` retains an integer polynomial and exact rational
evaluations. Its polynomial and angular variation bounds are `8*N^3`
and `2*N^2`. `seed_marked_cell_witness` proves the `13*h/16` witness from
the inclusive rational cell test; `seed_unmarked_cell_bound` proves the
`5*h/8` complementary margin under the specified enclosure and spacing
allowances. `RationalCosineGrid` is a contract, not a constructed algorithm.
`PolynomialSublevelComponentsHypothesis` explicitly states the remaining
closed-sublevel component theorem, counting singleton tangencies and
bounding the number of components by polynomial degree.

**Kernel work is partial.** `odd_sine_reproducing_identity` proves the finite
kernel formula everywhere, including removable singularities.
`sineKernelError_lt` proves the stated error expression is below `2/3`
for `N >= 2^20`. `SineKernelDecompositionHypothesis` isolates the unproved
local sinc-integral and total-variation estimates. Given it,
`sine_kernel_scaled_of_decomposition` gives the first-quadrant upper bound
`5*K*sqrt(N)` and interval lower bound `(2*K/3)*sqrt(N)`. The global
reflection extension and full integral lemma are not yet established.

**Coloring work is partial.** `DeterministicPartialColoringHypothesis` states
one uniform native multitape-TM algorithm on framed lists of canonical
binary rationals, with the exact entropy budget, half-coordinate condition,
and discrepancy constant `68`. It is not proved. Unconditional exports
prove the exponential quadratic/damping estimates, small-threshold count,
unrounded and rounded potential steps, full-step progress, nearest-sign
terminal rounding, and the full-coloring constant recurrence with `240`
and `2400`. Projector selection, the complete iteration, discrepancy
accumulation, bit bounds, and full-coloring recursion remain open.

Validation: all six individual `lake build Power2ModuleSVP.<Module>` targets
succeeded without warnings. A scratch audit of twelve principal exports
reported only `propext`, `Classical.choice`, and `Quot.sound`; conditional
results retain their named premises. There are no unfinished proofs or
new axioms in these modules. The scratch audit was removed.

Audit: no new mathematical error was found in the portions checked.
The formal sampling argument preserves closed thresholds and both cell
endpoints; the component contract includes tangencies. The Bernstein
proof uses actual complex polynomial interpolation rather than an assumed
analytic estimate. This does not validate the still-unformalized arguments.

To prove `thm:spectral-seed` and instantiate the repair job's
`SpectralSeedFamilyHypothesis`, remaining work includes the Rudin--Shapiro
construction and parameter estimates; seven-cell exclusion, axis avoidance,
symmetries and component counting; discharging the kernel decomposition;
deterministic partial/full coloring; the derivative-grid Taylor rounding
and final coefficient assembly; and uniform rational enclosure, grid,
arithmetic and native-machine time certificates. These lemmas alone do not
yet produce a spectral seed family. Root import integration is left to the
dispatcher.

## Anchor repair (p2s-repair)

Completed the semantic spectral-seed-to-rigid-anchor construction in
`AnchorSeedSpec.lean`, `AnchorScreen.lean`, `DisjointTests.lean`, and
`AnchorRepair.lean`; started native-machine work in `AnchorRepairPoly.lean`.
No existing Lean file, root import, or Lake configuration was changed.

`SpectralSeed d s` requires sign coefficients and evaluation magnitude at
least `(seedConstant : Real) * sqrt d` at every complex root of `X^d+1`,
where `seedConstant = 1/2^252` is rational. The uniform
`SpectralSeedFamilyHypothesis` mirrors the anchor interface: one total list
family, one native multitape polynomial-time certificate on unary degree,
and length/spectral guarantees above a fixed dyadic cutoff. The interface
allows an arbitrary fixed cutoff exponent; the manuscript's seed exponent
is 512. It requires no all-circle bound.

Screening is unconditional: `spectral_product_sqNorm` and `spectral_screen`
reuse `IdealCVP.Canonical.norm_identity` and `sigma_mul`. They give
`gamma^2*d*sqNorm v <= sqNorm (f*v)` and `sqNorm v <= 1/gamma^2` for a cube
product. `signs_mul_cube` proves the parity/domain conclusion for nonzero
multipliers in dyadic degree. `coeffEval_perturbation`,
`SpectralSeed.perturbation`, and `half_seed_screen` preserve half the seed
bound after the allowed flips and give the exact radius `C = 2^506`.
`repair_cutoff_nat` and `repair_cutoff` prove both dimension inequalities
for every exponent at least 3600, including odd exponents.

The executable disjoint-row selector has proved pairwise disjointness,
maximality, and `selectedRows_packing`:
`d <= selectedRows.length * support.card^2`. `rowValue_eq_mul` identifies
the exact local integer test with genuine negacyclic multiplication.
`rowProbability_le_one_sub_half` proves survival at most `1-p/2`, and
`eventProbability_le_pow` multiplies those bounds. All prefix probabilities
are exact rationals over the local flag lists. `eventProbability_branch`
and `eventProbability_terminal` prove branch averaging and the terminal
zero-or-one interpretation without a probability oracle.

`AnchorRepair.atomSums` enumerates sums of signed unit vectors and a blank
symbol. `mem_candidates` proves coverage of every support-at-least-two
multiplier of squared length at most `C`; `candidates_length_le_pow` bounds
the actual list, with repetitions, by `d^(2*C)` for `d >= 3`. No enumeration
of a dimension-sized coefficient box is used. `repair d s : List Int`
chooses every flip by comparing the two exact rational potential values,
including the linear flip penalty. `initial_survival_sum_le_half` and
`initial_potential_lt_one` discharge the initial estimate; there is no
remaining repair/probability hypothesis structure.

Principal namespace-`Power2ModuleSVP` exports are:

```lean
repair_length (d) (s) : (repair d s).length = d
repair_signs (s) (hs : Signs (IdealCVP.ofList (d := d) s)) :
  Signs (IdealCVP.ofList (d := d) (repair d s))
repair_rigid (hd : AnchorRepair.Admissible d) (s)
  (hs : SpectralSeed d (IdealCVP.ofList (d := d) s)) :
  Rigid (IdealCVP.ofList (d := d) (repair d s))
repair_rigid_of_cutoff (hd : Dyadic d) (hlarge : 2^3600 <= d) (s)
  (hs : SpectralSeed d (IdealCVP.ofList (d := d) s)) :
  Rigid (IdealCVP.ofList (d := d) (repair d s))
```

`repair_spec` packages length, signs, and rigidity. `Admissible` states the
explicit manuscript dimension inequalities with `Nat.log2 d`;
`admissible_of_cutoff` discharges them above `2^3600`.

Native-machine progress: `AnchorRepairRuntime.log2_polytime`,
`flipBudget_polytime`, and `applyFlags_polytime` compile. Positive-denominator
unnormalized integer fractions have proved value/ordering specifications and
native certificates `fractionAdd_polytime`, `fractionMul_polytime`, and
`fractionLE_polytime`. The theorem
`rigidAnchorFamily_of_seed_of_repair_polytime` composes a supplied full repair
time certificate with `SpectralSeedFamilyHypothesis`; that certificate is an
explicit argument, not a theorem asserted here. Full candidate/row/probability
loop certificates and encoded intermediate fraction-size bounds remain open.
Consequently `rigidAnchorFamily_of_seed` without that extra argument is not
yet proved, and the uniform module anchor premise has not been discharged.

Validation: successful single-module builds of all five new modules, with
the final `lake build Power2ModuleSVP.AnchorRepairPoly` rebuilding the repair
and its dependencies. Thirteen final axiom audits (including the cutoff
rigidity theorem and conditional native-family composition) report only
`propext`, `Classical.choice`, and `Quot.sound`. Six kernel-computed examples
checked candidate coverage/count, flag application, fraction arithmetic and
comparison, and row selection; two compiled exact-probability checks returned
the expected results. No unfinished proof or new axiom occurs. Own scratch
files were removed after validation.

Audit: no mathematical error was found in the screening, disjoint-tests,
repair, or cutoff arguments formalized here. Candidate repetitions are
explicitly included in the union bound. Prefix branch averaging uses
disjointness within a candidate's selected rows; it requires no independence
between candidates. Bit-complexity of the full rational computation remains
a separate, unproved algorithmic obligation.
- 182db75: coset_npComplete UNCONDITIONAL; moduleSVP_npComplete_of hJ. ebdab28: Bernstein etc. 71afbbf: semantic repair (spectral seed ⇒ rigid), audit (AUDIT.md: no soundness defect).
- Round 5 (05:05 UTC+8): p2s-seed2 (running since 04:49), p2s-repairpoly (repair_polytime, rigidAnchorFamily_of_seed), p2s-color (coloring algorithm + runtime).
- Remaining chain to unconditional module theorem: SpectralSeedFamilyHypothesis (flat seed: Rudin–Shapiro, sine kernel, intervals, coloring, Taylor rounding, runtime) + repair runtime.


## Repair runtime (p2s-repairpoly)

Completed the full native multitape polynomial-time certificate for the
existing total `repair` program. Added seven modules: `RepairRuntime.lean`,
`RepairRuntimeCandidates.lean`, `RepairRuntimeRows.lean`,
`RepairRuntimeProbability.lean`, `RepairRuntimePotential.lean`,
`RepairRuntimeLoop.lean`, and `AnchorRepairPoly2.lean`. Existing committed
Lean sources, other jobs' files, root imports, and Lake configuration were
not edited. Import `Power2ModuleSVP.AnchorRepairPoly2` for the final results.

The namespace-`Power2ModuleSVP` exports are:

```lean
repair_polytime : ComputableTidilyInPolyTime
  (fun a : Nat × List Int => repair a.1 a.2)
  AnchorRepairRuntime.encRepairInput (encList encIntBin)
rigidAnchorFamily_of_seed : SpectralSeedFamilyHypothesis -> RigidAnchorFamilyHypothesis
moduleSVP_npComplete_of_seed (h : SpectralSeedFamilyHypothesis) :
  NPComplete encSVP ModuleSVPLang
```

`AnchorRepairRuntime.repairFast_eq` proves function equality of the certified
list/fraction program `repairFast` and `fun a => repair a.1 a.2`, on every
raw pair. Thus the certificate includes zero/small/nondyadic degrees,
arbitrary seed coefficients, and malformed seed lengths. The original
false-on-tie branch, reverse greedy row order, candidate order, and all
candidate repetitions are preserved.

Fraction sums use a common denominator: a product of positive integer
denominators followed by exact binary natural division and an integer sum.
Fraction products use the numerator and denominator products separately.
The certified binary integer product, sum, and division routines account
for intermediate representation sizes. `fractionBits_polyBounded_of`,
`fractionSum_bits_polyBounded`, `fractionProd_bits_polyBounded`,
`localFraction_bits_polyBounded`, `eventFraction_bits_polyBounded`, and
`potentialFraction_bits_polyBounded` explicitly bound both component bit
lengths by fixed polynomials in their respective encoded input lengths.
No rational normalization or exact real computation is used.

`atomSumsList_polytime n` and `localFraction_polytime n` establish runtime
for each fixed cap before specializing to `screeningBound = 2^506`.
`candidateList_length_le` gives the total bound `(1+2*d)^n`, and
`candidateList_length_le_pow` gives `d^(2*n)` when `3 <= d`. The capped local
evaluator always runs in polynomial time on arbitrary multipliers; equality
to the original local expectation is asserted only under the proved local
support bound. `candidate_support_bounds` supplies that bound throughout
the potential. `rowsList_polytime` uses a bounded-growth reverse fold, and
`flagsFast_polytime` uses exactly `d` iterations with three additional
encoded bits per flag. Positive denominators and exactness are proved at
every interface, including at degree zero through `max 1 d`.

Validation: single-module builds succeeded for all seven modules; the final
`lake build Power2ModuleSVP.AnchorRepairPoly2` rebuilt the entire new chain
without warnings in the owned modules. Eleven axiom audits, including all
three final exports, the program equality, and the potential bit bound,
report only `propext`, `Classical.choice`, and `Quot.sound`. Sixteen small
kernel-computed checks passed for common-denominator arithmetic, empty
products/sums, candidate equality/count at zero, row ordering, negacyclic
local probabilities with partial/terminal prefixes, event products,
padded flag application, and degree-zero repair. No unfinished proof, new
axiom, or new hypothesis structure occurs in these modules. Own scratch
was removed after validation.

Audit: no new mathematical gap was found in the repair runtime argument
associated with `thm:repair`. A uniform polynomial-time certificate for
uncapped local expectation on arbitrary multiplier support is neither used
nor claimed; its exponential branching is avoided by the fixed cap, with
exactness recovered on candidates. The native-machine proof supplies the
bit-complexity obligation previously left open in the anchor repair section.
There are no remaining repair-runtime or seed-to-anchor integration
obligations in this job. Constructing `SpectralSeedFamilyHypothesis` remains
the separate seed/coloring task; the final completeness result above retains
exactly that premise.


## Flat seed round 2 (p2s-seed2)

Added twenty Lean modules, without changing any previously finished Lean
source, the root import file, or Lake configuration:

- `SineKernelProof.lean`, `SineKernelProofAux.lean`,
  `SineKernelProofCorrection.lean`, `SineKernelProofSineIntegral.lean`,
  `SineKernelProofLobes.lean`, `SineKernelProofVariation.lean`,
  `SineKernelProofTail.lean`, `SineKernelProofReflected.lean`,
  `SineKernelProofNear.lean`, `SineKernelProofDecomposition.lean`.
- `RudinShapiro.lean`, `RudinShapiroAux.lean`,
  `RudinShapiroBounds.lean`, `RudinShapiroDerivative.lean`,
  `RudinShapiroWave.lean`.
- `SeedGeometry.lean`, `SeedGeometryAux.lean`,
  `SeedGeometryRolle.lean`, `SeedGeometryCells.lean`,
  `SeedGeometryComponents.lean`.

**The original sine-kernel decomposition is discharged unconditionally.**
Import `Power2ModuleSVP.SineKernelProofDecomposition` for

```lean
sineKernelDecompositionHypothesis_holds : SineKernelDecompositionHypothesis
```

No correction or weakening of its statement was needed. The proof establishes
the continuous sine integral's bounds `0 <= Si(x) <= 2` for `x >= 0`, and
`Si(x) >= 4/3` for `x >= pi`, including certified base estimates at `pi` and
`2*pi`. The continued cosecant correction is monotone, with exact variation
`2 - 4/pi < 2`. Grid integration estimates hold for arbitrary phase and
merely monotone continuous weights; disjoint integer ranges sum their
variations. Each distant half-family costs at most `1/pi`. The reflected
kernel costs at most `2/(N*sin(100*pi/N))`: an exact split at the cosecant
minimum removes the crossing-interval exception. At most two intervals are
local; a containing interval is the unique local interval.
`sine_kernel_global` and `sine_kernel_scaled_global` consequently prove the
global upper bound `5*K*sqrt(N)` and lower bound `(2*K/3)*sqrt(N)` on the
reflected union, with no analytic hypothesis.

**Rudin--Shapiro starting data and bounds are unconditional.** The integer
recursion has exactly `2^k` sign coefficients and degree `2^k-1`.
`rudinShapiro_norm_identity` states that the squared complex norms of its
two evaluations sum to `2^(k+1)` on the unit circle.
`rudinShapiroPrefix_bound` gives the strict `5*sqrt(m)` bound for every
nonempty stable prefix. `rudinShapiro_seed_blocks` proves that both deleted
blocks at the specified separated high bits are copies of the first word.
`rudinShapiroCosinePart_bound` and `rudinShapiroEvenSinePart_bound` give the
`sqrt(N)` and `6*sqrt(N)` estimates under their explicit size inequalities.
`rudinShapiro_slow_block_bounds` proves the normalized derivative rate
`(1/1024)^r`. The actual normalized two-frequency wave has exact all-order
jets, first-five derivative bounds, error below `1/8`, four-jet
nondegeneracy, seven-cell exclusion, and odd-stage zero-axis clearance.

**The component hypothesis is also discharged unconditionally.** Import
`Power2ModuleSVP.SeedGeometryComponents` for

```lean
polynomialSublevelComponentsHypothesis_holds :
  PolynomialSublevelComponentsHypothesis
```

The proof includes a finite cover by strictly separated closed intervals,
including singleton tangencies, with at most the polynomial's degree many
intervals. A raised threshold gives distinct crossings, so no simple-root
assumption is used. Ordered sampled-run counts are also exported.
`seed_interpolation_derivative_bound` proves the separated-node factorial
bound by Lagrange interpolation and repeated Rolle.
`seed_seven_cell_exclusion` and `rudinShapiroWave_seven_cells_unmarked`
prove the actual seven-cell exclusion argument, with its numerical margin;
`seed_axis_clearance` supplies the generic axis estimate.

Validation: all twenty modules have successful individual single-target
builds; final aggregate checks were the single-module targets
`SineKernelProofDecomposition`, `RudinShapiroBounds`, `RudinShapiroWave`,
and `SeedGeometryComponents`. Eighteen final principal-export axiom audits
report only `propext`, `Classical.choice`, and `Quot.sound`. No unfinished
proof, new axiom, or new hypothesis structure occurs in these files. Own
scratch was removed after checking.

Audit: no mathematical error was found in the portions formalized here.
The decomposition's original constants suffice; the reflected estimate is
stronger than the intermediate manuscript estimate. This does not assert
that the remaining spectral-seed construction is already formalized.

Precisely what remains between these lemmas and `thm:spectral-seed`:

1. Select the largest admissible positive odd stage from the final degree,
   and prove all bounds for `N,T,gamma,delta,h`, the cutoff, and rational
   grid sizes. The generic size premises in the block estimates must be
   instantiated with these parameters.
2. Assemble the finite cosine/even-sine supports from the stable sequence:
   exact sign partition, integer even Chebyshev polynomial and its degree,
   and equality of the angular cosine seed with the normalized RS wave.
3. Construct the rational cosine grid, then assemble the marked closed-cell
   runs. Apply the proved sampling, seven-cell, and component lemmas;
   establish all axis exclusions (only the actual wave's zero-axis case is
   specialized here), reflection/period symmetries, four-element orbits,
   `J <= gamma*N`, and the complementary `delta*sqrt(N)` margin. The
   continuous component contract itself is no longer an open obligation.
4. Integrate the separate coloring job's partial/full coloring construction
   with the two concrete seed matrices, including entropy budgets,
   coefficient bounds, and all rational approximation allowances. This job
   supplies the analytic kernel estimates, not a coloring algorithm.
5. Prove the derivative-grid Taylor rounding estimate with constant 5900
   and combine it with the kernel and even-sine bounds on the bad intervals.
6. Assemble the Laurent coefficient signs, shift and append three terms,
   and prove the final all-circle lower bound `2^(-252)*sqrt(d)`.
7. Supply native multitape polynomial-time certificates for the complete
   seed program: stage selection, stable prefixes, rational elementary
   enclosures, grid and marking, coloring calls, coefficient recomputation,
   and final arrays, with all intermediate encoded size bounds. Then
   instantiate `SpectralSeedFamilyHypothesis`. No such uniform seed family
   is claimed here. The independent repair runtime job now provides its
   seed-to-anchor integration; it is not an additional seed obligation.

Root import integration remains the dispatcher's task. In particular,
importing only the identity module `SineKernelProof` does not import the
final theorem; use `SineKernelProofDecomposition`.

## Coloring (p2s-color)

**Partial implementation; the deterministic partial-coloring hypothesis is
not discharged.** Added nine Lean modules, without modifying the committed
`PartialColoring.lean`, the root imports, Lake configuration, or another
job's Lean sources:

- `PartialColoringAlg.lean`: rational dot products, rejection, orthogonal
  projection, and exact minimum-score column selection.
- `PartialColoringAlgProjector.lean`: materialized rational projector tables
  and agreement with the semantic projector.
- `PartialColoringAlgWalk.lean`: the actual total rational partial-coloring
  list program, including input checks, normalization, Taylor initialization,
  heavy-row sorting, constraints, direction, cube truncation, grid updates,
  and a cubic fuel bound.
- `PartialColoringAlgInvariants.lean`: cube preservation, fixed-coordinate
  preservation, small-row preservation, and monotonicity of the sign count.
- `PartialColoringAlgBounds.lean`: cube discrepancy, deletion of large
  thresholds, normalization, and extraction of constant 34 from terminal
  weights, hence constant 68 for original rows.
- `PartialColoringAlgCorrect.lean`: entropy accounting for prepared signed
  rows, explicit remaining trajectory/native hypotheses, and conditional
  correctness of the concrete program.
- `PartialColoringAlgRuntime.lean`: native multitape certificates for
  canonical rational primitives and input checks in the existing encoding.
- `ColoringAux.lean`, `Coloring.lean`: the explicit full-coloring recursion,
  its list interface and semantic proof, and a separate native-time boundary.

All partial-walk definitions and the following exports are in namespace
`Power2ModuleSVP.PartialColoringAlg`. The actual executable is
`partialColor : PartialColoringInput -> List Rat`.

`project_orthogonal`, `project_eq_self`, `project_idempotent`, and
`project_selfAdjoint` handle arbitrary constraint lists, including zero and
dependent rows. `projectorTable_spec` and `cachedColumns_eq` identify the
cached table with that projector. The executable walk uses the cached table;
it does not repeatedly expand the recursive semantic projector.
`bestColumn_min` proves minimum Rayleigh score among all nonzero candidates.
`normalize_bounds` proves squared length strictly above 1/4 and at most one.
`walk_cube`, `walk_fixed`, and `walk_small_row` are unconditional invariants.

The precise conditional correctness exports are:

```lean
partialColor_correct_of_trajectory
  (h : PartialColoringTrajectoryHypothesis) :
  PartialColoringCorrect partialColor

deterministicPartialColoring_of_trajectory_and_native
  (h : PartialColoringTrajectoryHypothesis)
  (hN : PartialColoringNativeHypothesis) :
  DeterministicPartialColoringHypothesis
```

`PartialColoringCorrect` expands to the original framed-list equality and
`PartialColoringSpec`, with the original premises and discrepancy constant
68. `PartialColoringTrajectoryHypothesis` has exactly three fields for the
concrete `run`: half-coordinate progress; terminal weights below two; and
an exponential lower bound with coefficient `33 + 8*stepSize^2`. Its input
contract includes normalized row lengths, retained threshold bounds, the
starting cube, and entropy budget `r/32`. Neither discrepancy nor a machine
certificate is assumed in those fields. `PartialColoringNativeHypothesis`
is the still-unproved full native certificate for `partialColor`.

Namespace-`Power2ModuleSVP` exports `fullColor`, `FullColoringSpec`,
`fullColor_spec`, `fullColoring_of_partialCorrect`, and
`fullColoring_exists_of`. Given any semantically correct partial program,
`fullColor_spec` proves the actual list program returns signs with
row discrepancy at most `(240*c_i + 2400)*sqrt(r)*coloringRowSup(V_i)`.
`coloringRowSup` is the coefficient maximum norm, including dimension zero.
The implementation retains exactly `r - r/2` selected sign coordinates,
and the proved active dimension is exactly `r/2`. The entropy lemma uses
a rational `2/5` bound for the exponential decrease, so odd dimensions are
covered. The concrete specialization is
`fullColor_partialColor_spec_of_trajectory` in the partial-walk namespace.

`FullColoringNativeHypothesis F` separately states the native certificate
for `fullColor F`; `fullColor_algorithm_of_partialCorrect` packages that
certificate with the proved semantics. Polynomial time for one arbitrary
partial program does not alone control denominator growth through the full
recursion. No unconditional full-coloring runtime theorem is claimed.

In namespace `Power2ModuleSVP.ColoringRuntime`, proved native certificates
include canonical numerator/denominator extraction, `divInt_polytime`,
`neg_polytime`, `add_polytime`, `sub_polytime`, `mul_polytime`, `inv_polytime`,
`div_polytime`, `le_polytime`, `lt_polytime`, `nearestSign_polytime`,
`validInput_polytime`, and `malformedFallback_polytime`.
`divInt_bits_le` bounds the canonical result's numerator/denominator binary
sizes by those of the two supplied integers, with one extra bit for zero
inputs. The total partial program checks list shapes, cube membership and
nonnegative thresholds before entering the walk. The real entropy budget
is a theorem premise and is never tested by the executable.

Audit of `lem:partial-color` and `thm:full-color`: no counterexample to either
statement or to constant 68 was found. The extraction proof certifies that
68 follows from the stated terminal estimates. Two implementation details
are explicit. Norm scales use a rational ceiling square root with the same
strict factor-two guarantee, rather than requiring dyadic scales. Also,
initial weights are rounded on a half-mesh: an upper enclosure with error
half a mesh plus that rounding fits within one mesh. A same-mesh rounding
of an approximate value alone would not ensure that allowance near a grid
boundary. `roundUp_half_enclosure` proves the corrected local rule. The
Taylor remainder needed to instantiate its enclosure premise is still open.

Remaining substantive work:

1. Prove the nonterminal subspace dimension, the projector trace/Rayleigh
   bound, positive and truncated-step progress, and the terminal half count.
2. Prove the initial Taylor enclosure, global rounded potential bounds,
   heavy-row terminal weight bound, and accumulated exponential lower bound.
   These discharge the three trajectory fields; they are not proved here.
3. Supply projector/direction determinant bit bounds; additive coordinate
   denominator bounds; native square-root, floor/grid, Taylor, sort and
   bounded-loop certificates; and assemble the full partial-program time
   certificate. Arithmetic certificates alone do not discharge it.
4. Bound intermediate encodings across the full-coloring recursion and
   certify that program, then instantiate the concrete seed coloring calls.

Validation: all eight semantic modules have successful individual
single-module `lake build Power2ModuleSVP.<Module>` checks without warnings.
The native primitives module checks without warnings using `lake env lean`
with a job-local compiled dependency overlay. An initial Lake attempt to
build its missing dependency artifacts failed at the read-only external
artifact cache; subsequent dependency compilation was confined to this
job's scratch directory. No dependency source was edited. Nine executed
exact-rational examples all returned true: ordinary/dependent projectors,
normalization, positive/negative grid rounding, one walk step, both list
programs' small cases, and rejection of an outside-cube input. Twenty
principal-export axiom audits report only `propext`, `Classical.choice`, and
`Quot.sound`. No unfinished proof or new axiom occurs. Own scratch was
removed after checking. Root import integration remains with the dispatcher.

## Flat seed assembly (p2s-seedmain)

Delivered a **conditional assembly**, not a completed construction of the
rational preprocessing routines. In particular, the remaining premises are
stronger than the kernel and partial-coloring hypotheses alone. No concrete
`FlatSeedFrontend` satisfying those premises is constructed here, and the
spectral seed family premise in the module completeness theorem is not yet
discharged.

New files (all in namespace `Power2ModuleSVP`):

- `SeedAlgorithm.lean`: the total two-coloring list program `seed A F`, its
  assembly routine, exact output length, unconditional sign coefficients,
  and valid indexing of both halves of every odd Laurent frequency pair.
- `SeedAlgorithmRuntime.lean`: native multitape polynomial-time composition
  for this program, given certificates for the rational frontend and the
  supplied coloring routine. The certificate covers every raw unary degree,
  malformed coloring outputs and arbitrary background words. Encoded output
  length is also polynomially bounded.
- `FlatSeedTaylor.lean`: smoothness from the existing Laurent representation;
  finite Taylor propagation using the proved Bernstein inequality; a
  geometric majorant and remainder estimate giving the constant 5900.
- `FlatSeedRounding.lean`: real/rational row transfer (including starting-point
  error), closed-quadrant sampling coverage, the complete finite entropy
  budget for integer thresholds `12 + ell`, and rational error absorption
  giving the constant `5281 + 240*ell`. Precision
  `1 / (2^20 * (N+1)^2)` suffices for this second rounding. The empty first
  coloring problem is handled explicitly.
- `FlatSeedBounds.lean`: the two complex-norm alternatives, rotation and
  appended-tail losses, and cutoff arithmetic at exponent 512.
- `FlatSeedMain.lean`: precise remaining preparation contracts, the sampled
  jet estimate derived from rational row enclosures and full coloring, the
  all-circle lower bound, the root-only spectral theorem and uniform family
  assembly. It imports the existing kernel and coloring interfaces unchanged.

Principal exports:

```lean
seed (A : FlatSeedFrontend) (F : PartialColoringInput -> List Rat) : Nat -> List Int
seed_length A F d : (seed A F d).length = d
seed_signs A F d : Signs (IdealCVP.ofList (d := d) (seed A F d))
seed_polytime A hAt F hFt :
  ComputableTidilyInPolyTime (seed A F) encUnary (encList encIntBin)
seed_spectral A hA hK F hF (hd : Dyadic d) (hlarge : 2^512 <= d) :
  SpectralSeed d (IdealCVP.ofList (d := d) (seed A F d))
spectralSeedFamily_of_fullColor A hA hAt hK F hF hFt : SpectralSeedFamilyHypothesis
spectralSeedFamily_of A hA hAt hK hP hT : SpectralSeedFamilyHypothesis
```

`seed_circle_lower` proves the stronger all-circle inequality. The root-only
statement then uses the proved fact that a root of `X^d+1` has unit norm.
`flatSeed_sample_jets` derives the finite jet bounds; the preparation
contract supplies exact row identities and rational enclosures, rather than
assuming those discrepancy bounds or the final spectral inequality.

**Exact remaining ingredient hypotheses in `spectralSeedFamily_of`:**

1. `SineKernelDecompositionHypothesis` (`hK`), exactly as in `SineKernel.lean`.
2. `DeterministicPartialColoringHypothesis` (`hP`), exactly as in
   `PartialColoring.lean`. The proved `fullColor_spec` supplies the semantic
   full-coloring theorem from its algorithm contract.
3. `FullColoringRuntimeHypothesis` (`hT`): a native polynomial-time
   certificate for `fullColor P` from the partial program's certificate and
   correctness. This is separate from the proved full-coloring semantics.
4. `FlatSeedPreparationHypothesis A` (`hA`), which requires four explicit
   per-degree contracts above the dyadic cutoff:
   - `FlatSeedGeometryHypothesis A D`: rational input identity and entropy;
     parameter/grid/interval construction, the interval-count bound,
     folding to the first quadrant, the cosine lower margin off the marked
     intervals and the even sine bound. Existing Rudin--Shapiro and interval
     lemmas do not yet construct a frontend satisfying this contract.
   - `FlatSeedIntervalRoundingHypothesis A D`: the reflected kernel identity,
     the actual second-input identity, and its cube/threshold/entropy
     conditions after the first full coloring. The concrete first matrix,
     transcendental enclosures and first coefficient-rounding estimate are
     still to be connected here.
   - `FlatSeedDerivativeRoundingHypothesis D`: exact normalized derivative-row
     identities, matrix and starting-point rational enclosures, and the
     degree/global/reflection facts for the odd-part error. The discrepancy
     loss and Taylor propagation from these data are proved.
   - `FlatSeedCoefficientHypothesis A D`: the exact Laurent evaluation
     identity for the executable background/odd-word assembly, with a unit
     rotation and a tail of norm at most three. Coefficient signs and list
     indexing are proved, but this algebraic identity remains a premise.
5. `FlatSeedFrontendRuntimeHypothesis A` (`hAt`): three uniform native-machine
   certificates, for `background`, `intervalInput`, and `coefficientInput`.
   Rational sampling/enclosure/marking programs and their bit bounds have not
   been implemented by this job. No runtime certificate for `seed` itself is
   assumed: it is derived from these three certificates and coloring time.

Alternatively `spectralSeedFamily_of_fullColor` accepts one supplied full
coloring routine with `FullColoringCorrect F` and its native certificate;
this bypasses items 2 and 3, retaining the preparation and kernel premises.

Validation: individual module builds and the final single-target
`lake build Power2ModuleSVP.FlatSeedMain` succeeded. The six owned modules
have no warnings in the final build. Fourteen principal-export axiom audits
report only `propext`, `Classical.choice`, and `Quot.sound`. Eight kernel
computed examples check empty/small outputs, negative odd-pair assembly,
integer/rational normalization, and odd-coordinate indexing. No unfinished
proof or new axiom occurs in the delivered files. Own scratch was removed.
No root file, Lake configuration, existing library source or other job's
Lean file was edited.

Audit: no new mathematical error was found in the portions proved. The
empty-interval case must use zero first-coloring rows as well as zero
columns, since positive many exponential terms cannot fit a zero entropy
budget; `seedIntervalRows` records this branch. The manuscript already
separates that case. The major remaining issue is formalization scope,
not a claimed paper defect: the rational frontend and its analytic/algebraic
bridges above still require construction. These conditional exports must
not be reported as an unconditional proof of `thm:spectral-seed`.
- 54e53fa repair runtime + moduleSVP_npComplete_of_seed; 900e794 sine kernel/Rudin–Shapiro/components; 274b974 coloring algorithm (conditional).
- Round 6 (06:20 UTC+8): p2s-seedmain (running since 05:25), p2s-traj (PartialColoringTrajectoryHypothesis), p2s-colornative (coloring TM certificates).
- 37f21db: conditional flat-seed assembly. Round 6b (06:32 UTC+8): p2s-frontend (FlatFrontend*: concrete frontend + 4 preparation contracts).

## Coloring trajectory (p2s-traj)

**The original concrete partial-coloring trajectory contract is now proved,
without a new hypothesis or a change to the executable walk.** Added eight
modules, all in namespace `Power2ModuleSVP.PartialColoringAlg`:

- `ColoringTrajectoryProjector.lean`: rational norm contraction, projector
  trace at least dimension minus constraint-list length, column-square sums,
  and the minimum-score trace estimate. Dependent and zero constraints are
  included; no choice of an independent constraint basis is needed.
- `ColoringTrajectoryGeometry.lean`: constraint counting from the entropy
  bound, trace at least `r/4`, nonzero normalized direction and its quadratic
  energy bound, truncation fixing a new coordinate, and full-step progress.
- `ColoringTrajectoryInitial.lean`: Taylor-sum error, inverse and half-mesh
  initialization enclosures, and the precision/mesh budget. In particular,
  the implemented `initialWeight` lies between `exp(-lambda^2)` and that
  value plus one mesh unit.
- `ColoringTrajectoryProgress.lean`: consumed-step count, progress measure,
  and unconditional half-coordinate termination for `run` under
  `WalkPremises`. The measure is squared norm plus `Delta^2/4` times the
  sign count. It proves `n*Delta^2/4 <= r + r*Delta^2/4` for actual steps.
- `ColoringTrajectoryPotential.lean`: increment bounds, damping bounds,
  cancellation of the linear update, control of the quadratic update,
  nonnegative weights, and the initial and one-step potential bounds.
- `ColoringTrajectoryUpper.lean`: the actual merge-sorted heavy-row bound,
  protection of heavy rows, a remaining-fuel upper-weight invariant, and
  terminal weights strictly below two.
- `ColoringTrajectoryLower.lean`: the exponential lower bound per step,
  telescoping displacement over exactly the consumed steps, and the terminal
  coefficient `33 + 8*stepSize^2`.
- `ColoringTrajectory.lean`: assembly and the unconditional partial/full
  coloring semantic exports. Import this module to use the completed proof.

Principal exports, with the original definitions and premises:

```lean
partialColoringTrajectory : PartialColoringTrajectoryHypothesis
partialColor_correct : PartialColoringCorrect partialColor

deterministicPartialColoring_of_native
  (hN : PartialColoringNativeHypothesis) :
  DeterministicPartialColoringHypothesis
```

The three component theorems are `run_terminal_half`,
`run_terminal_weight_upper`, and `run_terminal_weight_lower`. For
`hp : WalkPremises a x`, they respectively assert:

```lean
r <= 2 * signCoordinateCount (run a x).x
forall i, ((run a x).w i : Real) < 2
forall i,
  Real.exp ((a i).threshold * (dot (a i).a ((run a x).x - x) : Real) -
    (33 + 8 * (stepSize r : Real)^2) * ((a i).threshold : Real)^2)
    <= ((run a x).w i : Real)
```

`partialColor_correct` supplies the original framed-list equality, cube,
ceiling-half sign count, and discrepancy bound
`68 * threshold_i * coloringRowNorm(V_i)`. It has no trajectory or native
premise. `fullColor_partialColor_spec` also specializes the existing full
recursion semantics unconditionally: the concrete program returns signs
with discrepancy at most
`(240*c_i + 2400)*sqrt(r)*coloringRowSup(V_i)` under the original cube,
nonnegative-threshold and entropy premises.

Audit of `lem:partial-color`: no new mathematical error was found. The
Taylor implementation and rational truncation satisfy the original contract.
For the final exponential estimate it is essential to count consumed steps
using the progress measure, rather than use the larger programmed fuel
budget. The latter alone would lose a factor two in the damping exponent.
The Taylor remainder is proved without Stirling: compare a single Taylor
term at `4s` with `exp(4s)` and use `8s <= L` to obtain the needed geometric
decay. All descriptions here are independent paraphrases.

Validation: all eight modules compiled successfully in single-module Lake
builds; the final `lake build Power2ModuleSVP.ColoringTrajectory` has no
warnings. Ten principal-export axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`. There is no unfinished proof or new
axiom in these files. No committed Lean source, root import, Lake
configuration, existing library, or other job's Lean file was edited. Own
scratch was removed after checking.

Remaining work is the independent native-machine and bit-size certificate
for `partialColor`, together with the full-recursion native bounds. Those
remain in the existing native/runtime hypotheses; this job does not claim
an unconditional polynomial-time certificate or change another job's files.


## Coloring native runtime (p2s-colornative)

**Partial completion: neither native hypothesis is discharged.** The existing
`PartialColoringAlg.PartialColoringNativeHypothesis` and
`FullColoringNativeHypothesis PartialColoringAlg.partialColor` remain explicit
obligations. No new hypothesis, axiom, or unfinished proof is introduced.

Added six owned modules; no committed Lean source, root import, Lake entry,
IdealCVP source, or Rank2ModuleSVP source was changed:

- `ColoringNativeSqrt.lean`: a descending binary-digit square-root scan,
  agreement with `Nat.sqrt`, and native certificates for binary square root,
  `ceilSqrt`, and `normScale`. The scan has one step per input bit, with a
  proved bounded-growth fold; it does not scan to the numerical input value.
- `ColoringNativeArithmetic.lean`: native rational powers with unary
  exponents, exact list sums/products through the existing repair fraction
  routines, floor, ceiling, grid rounding, precision, mesh, cubic fuel,
  factorial, `expSum`, and `initialWeight`. Factorial reuses the certified
  binary integer list product. `expSum_bits_polyBounded` bounds canonical
  numerator and denominator bits for the actual Taylor sum.
- `ColoringNativeProjector.lean`: exact list dot products, materialized
  table application, and one projector elimination stage, with native
  certificates. `projectorStep_spec` identifies this stage with
  `PartialColoringAlg.projectorTable (a :: C)` for arbitrary constraint
  lists, including zero and dependent rows. Its certificate includes
  intermediate bit costs for that one stage.
- `ColoringNativeDenominators.lean`: common-denominator and bit invariants
  for the actual cube update, fixed dyadic weight denominators, direction
  independence from unfrozen point values, and a stopped-walk recurrence.
- `ColoringNativeRecursion.lean`: unconditional sign outputs for every
  supplied partial program, a linear final-output encoding bound, shared
  denominator preservation under restriction, and exact denominator
  preservation through all repeated threshold shifts.
- `ColoringNative.lean`: aggregate import, explicitly documenting the two
  remaining native boundaries.

Principal size statements, in namespace `Power2ModuleSVP.ColoringNative`:

```lean
cubeStep_commonDen : -- positive D,E; CommonDen D x; CommonDen E z; |z_j| <= 1
  exists D' > 0, CommonDen D' (x + stepSize r * (stepFraction x z * z)) and
    D'.size <= D.size + (stepSize r).den.size + E.size
walk_commonDen : -- invariant P preserved by nextState, direction bound B on P
  exists D' > 0, CommonDen D' (walk a fuel s).x and
    D'.size <= D.size + fuel * ((stepSize r).den.size + B)
run_weight_den_size : ((run a x).w i).den.size <= precision r m + 2
fullColor_encoding_length_le :
  (encList encColoringRational (fullColor F input)).length <= 13 * input.2.1.length
threshold_iterate_den : ((fun t : Rat => t + 4)^[k] q).den = q.den
```

The first two displayed statements abbreviate the fully typed Lean
statements. `coordinate_bits_le` additionally bounds each cube coordinate's
numerator-plus-denominator bits by twice its common denominator's size.
`vectorDen_size` charges an initial shared denominator to the sum bound on
coordinate denominator bits. `direction_den_eq_of_weights_and_fixed` proves
that changing unfrozen coordinates with the same frozen-coordinate set and
weights changes no direction denominator; only orientation can change.

Audit: weights, rather than coordinates, are rounded. This is sufficient
for the inspected denominator mechanism. For a truncated step, the common
direction denominator cancels, and the old point denominator occurs once.
Thus rounding coordinates is not needed to repair the proved local growth
bound. No mathematical defect or counterexample to polynomial time was
established here. The uniform direction bit bound itself is still open.

Exact remaining work: prove determinant/rank bounds for every intermediate
canonical projector table and direction; bound weight numerator magnitudes
on all raw valid inputs, including inputs without the entropy premise;
instantiate the walk size invariant and certify preparation, sorting,
column selection and stopped iteration as one list program. Then certify
full recursion with a uniform bound on every recursive call's encoding.
One polynomial-time stage, polynomial fuel, and a small final output alone
do not prove these complete machine certificates.

Validation: all six modules passed individual single-module `lake env lean`
compilations, including emitted local artifacts, with no final warnings.
The aggregate import and sixteen principal-export axiom audits also passed;
all audits report only `propext`, `Classical.choice`, and `Quot.sound`.
Eight exact computed checks returned true: binary roots, Taylor summation,
both signs of grid rounding, ordinary/zero/dependent projector stages, and
negative floor/ceiling. Final compilation needs no scratch dependency
overlay. No external dependency source or artifact was modified. Own scratch
was removed after validation. Root integration remains with the dispatcher.

## Flat seed frontend (p2s-frontend)

**Partial completion.** A concrete `Power2ModuleSVP.flatFrontend` is now
implemented. The original interval-rounding and coefficient contracts are
proved for its canonical analytic interpretation. There is still no
unconditional theorem `FlatSeedPreparationHypothesis flatFrontend`.
The remaining obligations are explicitly named below; neither they nor the
uniform spectral seed family are claimed to have been discharged.

Added ten files, without editing previously finished Lean files, the root,
Lake configuration, or another job's sources:

- `FlatFrontendParameters.lean`: bounded largest-odd-stage search; rational
  parameter, height, and grid definitions; admissibility at the cutoff,
  maximality, both gamma bounds, block containment and even-part size premises.
- `FlatFrontendWords.lean`: structurally recursive integer RS word pairs,
  exact agreement with the existing polynomial coefficients, stable prefixes,
  and the executable shifted background word.
- `FlatFrontendTaylor.lean`: rational complex Taylor pairs, sine/cosine
  factorial remainders, finite arctangent sums, and the Machin pi enclosure.
- `FlatFrontendProgram.lean`: explicit precisions, rational square root,
  reflected cosine samples, forward Chebyshev evaluation, inclusive marking,
  one-pass run merging, kernel rows, derivative rows and coefficient
  recomputation. Defines the three fields of `flatFrontend`.
- `FlatFrontendRational.lean`: clipping and floor-square-root enclosures,
  starting-point bounds, and the first coloring's entropy budget.
- `FlatFrontendCoefficients.lean`: exact centered coefficient pairing,
  Laurent evaluation identity, unit rotation, and three-term tail bound.
- `FlatFrontendDerivatives.lean`: exact all-order odd sine jets, normalized
  derivative-row identity and entry bound, trigonometric degree, global sum
  bounds and one common first-quadrant folding map.
- `FlatFrontendInputs.lean`: actual framed-list identities, both rectangular
  shapes, both cube and threshold conditions, and both entropy budgets.
- `FlatFrontendEnclosures.lean`: exact Chebyshev evaluator specification and
  combined Taylor/Machin remainder for rational multiples of pi.
- `FlatFrontendMain.lean`: canonical `analyticData`, two original contracts
  without further analytic premises, and explicit remaining preparation data.

All executable routines use only natural/integer/rational arithmetic and
lists. Real functions, integrals, polynomials used for interpretation, and
angle folding occur only in specifications/proofs. Precision is explicit:
`precision N = 128 + 64*log2(N+1)` and
`taylorOrder N = 128*(N+1)^2 + precision N`. No claim that these choices
already satisfy every required per-degree error inequality is made.
The first threshold is an integer square-root expression using a proved
`log 2 <= 7/10` bound; it is 29 at `N/J = 2^66`. The second thresholds are
`12 + ell`. The recomputed starting point is clipped to `[-4/5,4/5]`;
clipping does not increase its error relative to a point in that interval.

Principal contract exports, in namespace `Power2ModuleSVP.FlatFrontend`:

```lean
interval_contract
  (I : SeedKernelIntervals (seedN d) (intervalCount d)) :
  FlatSeedIntervalRoundingHypothesis flatFrontend (analyticData d I)

coefficient_contract_dyadic
  (I : SeedKernelIntervals (seedN d) (intervalCount d))
  (hd : Dyadic d) (hlarge : 4 <= d) :
  FlatSeedCoefficientHypothesis flatFrontend (analyticData d I)

derivative_contract
  (I : SeedKernelIntervals (seedN d) (intervalCount d))
  (hN : 0 < seedN d) (hE : EnclosureHypothesis I) :
  FlatSeedDerivativeRoundingHypothesis (analyticData d I)

geometry_contract (G : GeometryCertificate d) :
  FlatSeedGeometryHypothesis flatFrontend (analyticData d G.kernelIntervals)

preparation_of (h : PreparationHypothesis) :
  FlatSeedPreparationHypothesis flatFrontend
```

`assembled_evaluation` proves the coefficient identity at every degree
`4*N+4`, independently of intervals and rounding. `derivativeRow_identity`
proves the exact normalized sampled derivative formula at every derivative
order. `sin_cos_taylor_error`, `arctan_taylor_error`, `pi_taylor_error`,
`sqrtApprox_spec`, and `phaseTaylor_pi_error` give certified primitive
remainders, rather than assuming an oracle for elementary functions.

**Exact remaining list:**

1. Construct `GeometryCertificate d` for each dyadic degree above the
   cutoff. Its interval endpoints must be precisely `scanCells`' output.
   Verify the `SeedKernelIntervals` width, gap and axis-clearance fields,
   `intervalCount d * 2^66 <= seedN d`, the complementary cosine margin,
   and the `6*sqrt(N)` even-part bound. This still requires identifying the
   actual background's pair sums/differences with the proved RS parts,
   proving that the rational grid is ordered and sufficiently accurate,
   and assembling the sampling, seven-cell, symmetry and component-count
   lemmas for these parameters. The continuous component-count and wave
   lemmas from the previous jobs themselves need no replacement.
2. Prove `EnclosureHypothesis.fractional_bound`: after the actual first
   full-coloring specification, every real kernel coefficient has absolute
   value at most `3/4`. Include the rational kernel-entry transfer and the
   integer-threshold variant's numerical margin.
3. Prove `EnclosureHypothesis.fractional_error`: the executable endpoint-sum
   recomputation is within `seedRoundingError N` of that real coefficient.
   The clipping transfer has already been proved.
4. Prove `EnclosureHypothesis.derivative_error`: every actual rational
   derivative entry is within `seedRoundingError N` of `derivativeRow`.
   The exact row identities, norm bounds, Taylor/Machin primitive remainder
   formulas and subsequent derivative/Taylor assembly are already proved.
5. Supply the three native-machine certificates in
   `FlatSeedFrontendRuntimeHypothesis flatFrontend`, including intermediate
   bit bounds. This is separate from the semantic preparation obligation
   and remains for the later runtime job.

`PreparationHypothesis` requires exactly a geometry certificate and those
three enclosure fields uniformly above the cutoff. It does not assume the
final spectral inequality, coloring correctness, or frontend runtime.
No change to the existing `FlatSeedMain` contracts was found necessary.
No mathematical error in the examined manuscript argument was established;
the remaining gaps listed here concern the unfinished formal connections.

Validation: individual single-module checks and the aggregate single-target
`lake build Power2ModuleSVP.FlatFrontendMain` succeeded. All ten modules
are imported by that target. The only remaining own-file build messages
are module-system compatibility warnings caused by importing the existing
non-module assembly alongside Mathlib module imports. Twenty-two principal
export axiom audits report only `propext`, `Classical.choice`, and
`Quot.sound`. Eight exact executable checks returned true (RS shapes,
background signs/lengths, empty first input, threshold 29, floor square root,
Taylor values, pi approximation and phase rotation). No unfinished proof or
new axiom occurs in these sources. Job-local scratch was removed after the
final checks. Root import integration remains with the dispatcher.

## Coloring native runtime 2 (p2s-colornative2)

**Partial completion. Neither whole-program native hypothesis is discharged.**
This pass proves entropy-free intermediate weight bit bounds and adds exact
native cached-projector, column-selection and direction programs. The
projector/direction certificates remain conditional on a local arithmetic
bound. It does not export `partialColoringNative_holds` or
`fullColoringNative_partialColor`, and does not claim to derive those two
hypotheses from the remaining arithmetic premise alone.

Added seven owned modules, with aggregate import `ColoringNative2.lean`.
No previously committed Lean source, root import, Lake configuration,
dependency, or frontend job source was edited.

- `ColoringNative2Weights.lean`: unconditional direction norm contraction;
  an entropy-free row-increment bound; initialization between zero and two;
  weight growth through every stopped-walk prefix; and explicit canonical
  numerator-plus-denominator bit bounds. This finishes the earlier raw-input
  weight-magnitude obligation for retained, normalized rows. In particular,
  `prepared_walk_weight_bits_le_raw` needs only positive dimension, a cube
  starting point and nonnegative original thresholds, not entropy. Its bound
  is `2*(fuel+1)+1+2*(precision r preparedRowCount+2)`. Initialization is
  bounded even on arbitrary thresholds. The row-increment argument includes
  zero directions and dependent projectors.
- `ColoringNative2Projector.lean`: the explicit reverse-list fold
  `projectorBatch`, identity initialization and row truncation, with exact
  agreement with the original canonical table. The theorem
  `projectorBatch_polytime_of_size` certifies the entire loop from a uniform
  bound on canonical table encodings for sublists of the input. Every
  prefix accumulator is identified with such a table. Zero, dependent and
  wrong-length raw rows are covered.
- `ColoringNative2Height.lean`: projector entries have absolute value at
  most one; numerator bits are at most denominator bits; an explicit bound
  on the framed table encoding; and reduction of the preceding size premise
  to `CanonicalProjectorDenominatorHypothesis`. This named structure has one
  purely arithmetic field: there exist uniform constants `c,d` bounding each
  canonical entry's denominator bits by `c*(inputEncodingLength+1)^d` for
  every constraint sublist. It has no native-machine, walk, semantic
  coloring, or full-recursion field. Proving it by a Gram determinant/rank
  argument remains open here.
- `ColoringNative2Column.lean`: exact list energies, Rayleigh scores and
  candidate selection, with unconditional native certificates. The complete
  scan stores an existing candidate or the empty zero vector, so its
  accumulator size is bounded by its input encoding without an arithmetic
  growth premise. `bestColumnList_spec` preserves the original tie and
  zero-candidate rules for arbitrary raw lists.
- `ColoringNative2Direction.lean`: native list normalization and the exact
  normalized cached-projector column. Under the local denominator hypothesis,
  `unorientedDirection_polytime` is a native certificate for this entire
  data program. `direction_commonDen_polyBounded` and
  `walk_direction_commonDen_of_projector` produce a polynomial shared
  direction-denominator bound uniform in the point used for orientation.
  The bound is charged to reified constraints and quadratic rows, excluding
  the point's rational numerator/denominator encoding.
- `ColoringNative2Walk.lean`: the entropy-free indexed `WeightBox` invariant
  and its initial/one-step proofs. `walk_commonDen_of_weightBox` and
  `run_commonDen_of_weightBox` instantiate finite-horizon denominator growth;
  `run_coordinate_bits_of_weightBox` also bounds coordinate numerator bits.
  Indexing matters: a fixed upper magnitude bound is not preserved by an
  arbitrary extra step after the fuel budget has been exhausted.
- `ColoringNative2.lean`: aggregate and
  `run_coordinate_bits_of_projector`, composing the actual direction bridge
  with the actual stopped walk, conditional on the local projector
  denominator bound and a uniform reified-constraint encoding bound over
  the explicit weight box. `walkDirectionInput_eq_of_weights_and_fixed`
  proves that this data ignores unfrozen point values.

Remaining work, precisely: prove
`ColoringRuntime.CanonicalProjectorDenominatorHypothesis`; bound
`encDirectionInput (walkDirectionInput a s)` uniformly over the proved
`WeightBox`; certify preparation, exact heavy-row sorting and the stopped
list walk as a composition; then construct and certify the full-recursion
list evaluator with a uniform encoding bound for every recursive call.
The final-output bound from `ColoringNativeRecursion.lean` is not used as a
substitute for that last invariant. No counterexample to polynomial time of
the concrete program was established, and the original program was not
modified. The local denominator hypothesis is a smaller boundary for the
projector/direction subpiece only, not a claimed complete replacement for
both original whole-program hypotheses.

Validation: all seven modules passed individual sequential `lake env lean`
checks with local emitted artifacts and no final warnings. The aggregate
import and twelve principal-export axiom audits passed, reporting only
`propext`, `Classical.choice`, and `Quot.sound`. Five exact executable
checks cover score ties, zero candidates, dependent/zero projector rows,
zero normalization and a nonzero normalized vector. No unfinished proofs,
new axioms or implementation overrides were introduced. Scratch was kept
under `/tmp/p2s-scratch-p2s-colornative2` and removed after validation.

## Flat seed frontend 2 (p2s-frontend2)

**Partial completion: all rational enclosures discharged; marked-run analytic
geometry remains open.** There is still no unconditional
`flatFrontend_preparation : FlatSeedPreparationHypothesis flatFrontend`.
The implementation and its precisions are unchanged. In particular, the
runtime job should continue using `flatFrontend`, `precision`, and
`taylorOrder` from the original frontend files; no corrected frontend is
introduced here.

Seven new owned modules, without changing committed Lean files, the root,
or Lake configuration:

- `FlatFrontend2Derivative.lean`: exact derivative phase identification and
  an entry enclosure whose only premises are rational remainder bounds.
- `FlatFrontend2Precision.lean`: geometric Machin bound, factorial Taylor
  bound, automatic ratio test, uniform rounding budget, and the unconditional
  `derivative_error`. This holds for every derivative order and every actual
  derivative entry, without a large-degree premise. A stronger tolerance
  `fineError N = 1/(2^80*(N+1)^10)` controls endpoint evaluation as well.
- `FlatFrontend2Kernel.lean`: exact integral matrix interpretation and finite
  coefficient sum, exact identification of the first rational input rows,
  recomputation transfer, first-round discrepancy transfer, and reduction of
  the fractional bound to a scalar threshold margin. The empty interval
  family is handled explicitly.
- `FlatFrontend2Endpoints.lean`: endpoint cosine enclosures, the real/rational
  kernel-entry enclosure, a summed error budget, and `fractional_error` for
  every geometry certificate of the computed runs. This theorem needs only
  signs of the first output, not its discrepancy bound.
- `FlatFrontend2Threshold.lean`: a uniform bound on the actual integer first
  threshold and the resulting `firstThreshold_margin`. The key integer
  inequality is `firstThresholdNat N J ^ 2 * J * 2^66 <= 841*N` whenever
  `J > 0` and `J*2^66 <= N`. It allows the threshold to grow for sparse
  interval families instead of incorrectly assuming it is always at most 29.
- `FlatFrontend2Runs.lean`: the actual `scanCells` output has positive widths,
  endpoints within the scanned range, and pairwise cell gaps. It defines the
  canonical endpoints, the remaining six-field `MarkedRunEstimates`, and
  constructs `geometryCertificate_of_estimates` from those estimates.
- `FlatFrontend2Main.lean`: `enclosure_of_geometry` discharges **all three**
  fields of the original `EnclosureHypothesis` using the original executable
  frontend, and composes the preparation theorem below.

Principal exports in `Power2ModuleSVP.FlatFrontend`:

```lean
derivative_error (k : Fin (16*N)) (ell : Nat) (j : Fin N) :
  |derivativeRow N k ell j - (derivativeEntry N k ell j : Real)| <=
    (seedRoundingError N : Real)

enclosure_of_geometry (G : GeometryCertificate d) (hN : 0 < seedN d) :
  EnclosureHypothesis G.kernelIntervals

geometryCertificate_of_estimates (h : MarkedRunEstimates d) :
  GeometryCertificate d

flatFrontend_preparation_of_geometry (hG : MarkedRunGeometryHypothesis) :
  FlatSeedPreparationHypothesis flatFrontend
```

**Exact residual hypothesis.** `MarkedRunGeometryHypothesis` asks for
`MarkedRunEstimates d` at each relevant dyadic degree. Its fields refer to
`runLeft` and `runRight`, which are precisely the computed list endpoints,
and require only:

1. At most six cells per run.
2. One hundred cells of left-axis clearance.
3. One hundred cells of right-axis clearance.
4. `intervalCount d * 2^66 <= seedN d`.
5. The required cosine margin outside these actual runs after folding.
6. The even-part bound `6*sqrt(seedN d)`.

Positive width, range, separation, endpoint alignment, all Taylor/Machin/sqrt
precision bounds, recomputation error, derivative error, and the first
fractional-coefficient bound are proved and are not residual premises.
No spectral inequality or final seed conclusion is a field of this smaller
hypothesis. Constructing the remaining geometry needs the background/RS
identifications, ordered rational-grid error and coverage, and application of
the existing wave/component estimates to the actual marked cells. This
connection has not been formalized in this job. In particular, relevant
`seedN d` is odd, so the unscanned half-cell at the right endpoint requires
an axis-clearance argument. For the sharp count, use a reduced polynomial in
`cos(2*theta)`; the full even Chebyshev polynomial has twice the desired
degree bound. These are proof obligations, not identified counterexamples to
the construction.

Validation: each owned module checked separately; aggregate single-target
`lake build Power2ModuleSVP.FlatFrontend2Main` checks all seven modules.
No unfinished proof, new axiom, native decision, or implementation override
is introduced. All six audited principal exports report only
`propext`, `Classical.choice`, and `Quot.sound`. Job-local scratch was removed.
No native runtime
certificate is claimed by this job. No private source text was copied.

## Flat seed frontend runtime (p2s-frontrt)

**Complete for the original `flatFrontend`.** `FlatFrontendRuntime.lean`
exports the unconditional theorem

```lean
Power2ModuleSVP.flatFrontend_runtime :
  FlatSeedFrontendRuntimeHypothesis flatFrontend
```

All three fields certify the actual total preprocessing functions, including
zero, malformed degrees and arbitrary second-input rational lists. There is
no added arithmetic, size, geometry or coloring hypothesis. This result does
not discharge the frontend's separate analytic preparation contract.

Six new files, all under this job's `FlatFrontendRuntime*` prefix:

- `FlatFrontendRuntimeTaylor.lean`: period-four phase lookup, exact finite-sum
  implementation of the rational Taylor pair, arctangent/Machin sums,
  precision/order counters and binary floor-square-root approximation.
  Rational powers, unary factorials and common-denominator summation reuse
  `ColoringNativeArithmetic` and the repair runtime certificates. Truncation
  orders and square-root precisions are independent unary inputs, so these
  certificates transfer to other polynomial-time precision policies.
- `FlatFrontendRuntimeParameters.lean`: bounded stage search, binary powers,
  rational height, first threshold, and certified unary conversions. The
  coarse raw-input bounds are `blockShift N <= 2048*(N+1)^2`,
  `height N >= 1/2^212` for positive `N`, and
  `gridRatio N <= 2*(64*N*2^212+1)`. The zero branch is proved separately.
  A short list-search helper mirrors complexitylib's `Nat.Search` proof
  locally because that dependency module has no built object in this checkout;
  no shared dependency source or build artifact was changed for this helper.
- `FlatFrontendRuntimeWords.lean`: capped RS word iteration, proved equal to
  the requested prefixes of the original words. Every intermediate word has
  at most the cap's number of sign entries. This certifies stable prefixes
  and individual coefficient lookup without an exponential allocation.
- `FlatFrontendRuntimeChebyshev.lean`: integer common-denominator iteration.
  If the state is `(A,B)`, the next state is
  `(B,2*q.num*B-q.den^2*A)`. The exact rational pair is recovered with
  denominators `q.den^n` and `q.den^(n+1)`. A linear bound on each integer's
  bit length certifies every intermediate state for arbitrary rational `q`.
- `FlatFrontendRuntimeScan.lean`: a capped forward accumulator, proved equal
  to `scanCells 0 none`. The input word length bounds every reachable index;
  the cap gives a uniform additive encoded-state growth bound.
- `FlatFrontendRuntime.lean`: background, reflected samples, marking, interval
  matrices, clipped fractional coefficients, normalized derivative matrices,
  both complete coloring inputs and the final structure. Exports polynomial
  canonical numerator/denominator bit bounds for Taylor pairs, square roots,
  Chebyshev pairs, kernel entries and derivative entries. These bounds come
  from native certificates, not bounds on numerical absolute values alone.

Validation: all six modules built individually and sequentially with
`lake build Power2ModuleSVP.<module>`. The final
`lake build Power2ModuleSVP.FlatFrontendRuntime` passed. A separate importing
Lean check confirmed the exact exported type and all five bit-bound
corollaries. `#print axioms Power2ModuleSVP.flatFrontend_runtime` reports only
`[propext, Classical.choice, Quot.sound]`. The new Lean files contain no
`sorry`, `admit`, new axiom or implementation override. Root, Lake configuration,
existing Lean files and the concurrent jobs' sources were not edited.
