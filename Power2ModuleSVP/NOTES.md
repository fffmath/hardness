# Power2ModuleSVP — paper ↔ Lean map

Paper: [power2svp.pdf](paper/power2svp.pdf). Namespace `Power2ModuleSVP` unless qualified.
Section and lemma numbers refer to that PDF. Native machine certificates refine the paper's
polynomial bit-time claims with executable finite-list programs and explicit size invariants.

| Paper | Lean declaration | File |
| --- | --- | --- |
| §§1.1–2, encoded decision problems | `CosetLang`, `ModuleSVPLang`, `encCoset`, `encSVP` | [Problem.lean](Problem.lean) |
| §2, coefficient cube and signs | `Cube`, `Signs`, `Rigid` | [Coset/Coefficient.lean](Coset/Coefficient.lean) |
| §3.1, Lemma 1 (parity block) | `parity_block`, `parity_block_forcing` | [Coset/ParityBlock.lean](Coset/ParityBlock.lean) |
| §3.1, Theorem 2 (principal coset) | `packCoset_complete`, `packCoset_sound`, `packCoset_correct` | [Coset/Packing.lean](Coset/Packing.lean) |
| §3.2, Lemma 2 (Mahler estimate) | `elementary_mahler_unconditional` | [Coset/Norm/Mahler.lean](Coset/Norm/Mahler.lean) |
| §3.2, Lemma 3 (reciprocal resultant) | `reciprocal_resultant_bound` | [Coset/Norm/Resultant.lean](Coset/Norm/Resultant.lean) |
| §3.2, repeated-factor extraction in Lemma 4 | `dividedDerivativeWitnessHypothesis_holds` | [Coset/Norm/Divided.lean](Coset/Norm/Divided.lean) |
| §3.2, Lemma 4 (bounded remainder) | `bounded_remainder_separation`, `normSeparationHypothesis_holds` | [Coset/Norm/SourceSeparation.lean](Coset/Norm/SourceSeparation.lean) |
| §3.3, Proposition 1 (homogenization) | `homogenization`, `homogenization_minimum`, `triangular_free` | [Anchor/Homogenization.lean](Anchor/Homogenization.lean) |
| §4, positive exactly-one source | `BooleanSource.fromThreeSAT`, `BooleanSource.threeSAT_affine_correct` | [Source/Boolean/Normalize.lean](Source/Boolean/Normalize.lean), [Source/Boolean/Reduction.lean](Source/Boolean/Reduction.lean) |
| §4, Proposition 2 (sparse affine source) | `SparseEncoding.affine_correct` | [Source/Boolean/Affine.lean](Source/Boolean/Affine.lean) |
| §4, Sidon support and reflected clauses | `SparseEncoding.encode` | [Source/Sidon/Encoding.lean](Source/Sidon/Encoding.lean) |
| §4, Lemma 5 (prime reciprocal exponent) | `Sidon.no_common_root_reverse`, `Sidon.modulus_coprime_reverse` | [Source/Sidon/Reciprocal.lean](Source/Sidon/Reciprocal.lean) |
| §4, Lemma 6 (positivity padding) | `SparseEncoding.encoding_padding` | [Source/Sidon/Encoding.lean](Source/Sidon/Encoding.lean) |
| §4, executable source and polynomial runtime | `sourceMap_eq`, `sourceMap_correct`, `sourceMap_polytime` | [Source/Map.lean](Source/Map.lean), [Runtime/Source/PolyTime.lean](Runtime/Source/PolyTime.lean) |
| §5, spectral seed interface | `SpectralSeed`, `SpectralSeedFamilyHypothesis` | [Seed/Specification.lean](Seed/Specification.lean) |
| §5, screening short multipliers | `spectral_screen` | [Anchor/Screen.lean](Anchor/Screen.lean) |
| §5, Lemma 8 and exact local probabilities | `AnchorTests.localExpectation`, `AnchorTests.selectedRows_packing`, `AnchorTests.eventProbability_le_pow` | [Anchor/LocalExpectations.lean](Anchor/LocalExpectations.lean) |
| §5, Theorem 4 (deterministic repair) | `repair_spec`, `repair_rigid_of_cutoff` | [Anchor/Repair.lean](Anchor/Repair.lean) |
| §5, Theorem 3 (uniform rigid anchors) | `rigidAnchorFamily_of_seed` | [Anchor/FromSeed.lean](Anchor/FromSeed.lean) |
| Appendix A.1, Rudin–Shapiro recursion | `rudinShapiroP`, `rudinShapiroQ` | [Seed/RudinShapiro/Basic.lean](Seed/RudinShapiro/Basic.lean) |
| Appendix A, Bernstein estimates | `HasTrigDegree` | [Seed/Bernstein.lean](Seed/Bernstein.lean) |
| Appendix A.1, polynomial sublevel geometry | `polynomialSublevelComponentsHypothesis_holds` | [Seed/Geometry/Components.lean](Seed/Geometry/Components.lean) |
| Appendix A.1, Lemma 9 (computed interval geometry) | `FlatFrontend.markedRunEstimates`, `FlatFrontend.markedRunGeometryHypothesis_holds` | [FlatFrontend/Geometry/Certificate.lean](FlatFrontend/Geometry/Certificate.lean) |
| Appendix A.2, Lemma 10 (sine kernel) | `sineKernelDecompositionHypothesis_holds`, `sine_kernel_scaled_global` | [Seed/SineKernel/Decomposition.lean](Seed/SineKernel/Decomposition.lean) |
| Appendix A.3, rounding and preparation | `FlatFrontend.flatFrontend_preparation` | [FlatFrontend/Geometry/Certificate.lean](FlatFrontend/Geometry/Certificate.lean) |
| Appendix A, Theorem 5 (flat seed) | `seed_circle_lower`, `seed_spectral`, `spectralSeedFamily_of_fullColor` | [Seed/Assembly.lean](Seed/Assembly.lean) |
| Appendix A, uniform native seed family | `spectralSeedFamily_holds` | [Seed/Family.lean](Seed/Family.lean) |
| Appendix B, Lemma 11 (partial coloring) | `PartialColoringAlg.partialColor_correct` | [Coloring/Trajectory/Basic.lean](Coloring/Trajectory/Basic.lean) |
| Appendix B, Theorem 6 (full coloring) | `fullColoring_of_partialCorrect`, `FullColoringSpec` | [Coloring/Full.lean](Coloring/Full.lean) |
| Appendix B, polynomial bit complexity | `ColoringRuntime.partialColoringNative_holds`, `ColoringRuntime.fullColoringNative_partialColor` | [Runtime/Coloring/Certificate.lean](Runtime/Coloring/Certificate.lean) |
| §3.3, proof of Theorem 1 (NP membership) | `coset_mem_NP`, `moduleSVP_mem_NP` | [Membership/NP.lean](Membership/NP.lean) |
| §1.1, Theorem 1 (NP-completeness) | `coset_npComplete`, `moduleSVP_npComplete` | [Main.lean](Main.lean) |
| §1.1, integral YES/NO gap | `moduleReduction_gap` | [Reduction/Completeness.lean](Reduction/Completeness.lean) |

The flat seed is proved on the full unit circle by `seed_circle_lower`; the reusable
`SpectralSeed` interface only asks for evaluations at the negacyclic roots. The seed cutoff is
`2^512`, and deterministic repair exports rigidity from `2^3600`. The source-specific reciprocal
root promise and repeated-factor handling are explicit in the norm proofs.

The search-approximation consequence discussed after Theorem 1 is not separately formalised as
an oracle/search reduction. The integral decision gap is formalised by `moduleReduction_gap`.
Audit findings and implementation choices are retained in `specs/AUDIT*.md`; these reports
predate the final unconditional runtime certificate and the folder restructure.
