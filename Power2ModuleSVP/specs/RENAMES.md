# Power2ModuleSVP module renames

Paths are relative to `Power2ModuleSVP/`. Declaration names and namespaces are preserved,
except for the explicitly removed interfaces listed below. The root `Power2ModuleSVP.lean`
imports every remaining module in sorted order.

## Complete old → new file map

| Old file | New file |
| --- | --- |
| `Anchor.lean` | [Anchor/Family.lean](../Anchor/Family.lean) |
| `AnchorRepair.lean` | [Anchor/Repair.lean](../Anchor/Repair.lean) |
| `AnchorRepairPoly.lean` | [Runtime/Repair/Parameters.lean](../Runtime/Repair/Parameters.lean) |
| `AnchorRepairPoly2.lean` | [Anchor/FromSeed.lean](../Anchor/FromSeed.lean) |
| `AnchorScreen.lean` | [Anchor/Screen.lean](../Anchor/Screen.lean) |
| `AnchorSeedSpec.lean` | [Seed/Specification.lean](../Seed/Specification.lean) |
| `Bernstein.lean` | [Seed/Bernstein.lean](../Seed/Bernstein.lean) |
| `BooleanSource.lean` | [Source/Boolean/Basic.lean](../Source/Boolean/Basic.lean) |
| `BooleanSourceAffine.lean` | [Source/Boolean/Affine.lean](../Source/Boolean/Affine.lean) |
| `BooleanSourceNormalize.lean` | [Source/Boolean/Normalize.lean](../Source/Boolean/Normalize.lean) |
| `BooleanSourcePadding.lean` | [Source/Boolean/Padding.lean](../Source/Boolean/Padding.lean) |
| `BooleanSourceReduction.lean` | [Source/Boolean/Reduction.lean](../Source/Boolean/Reduction.lean) |
| `Chebyshev.lean` | [Seed/Chebyshev/Basic.lean](../Seed/Chebyshev/Basic.lean) |
| `ChebyshevTrig.lean` | [Seed/Chebyshev/Trig.lean](../Seed/Chebyshev/Trig.lean) |
| `Coefficient.lean` | [Coset/Coefficient.lean](../Coset/Coefficient.lean) |
| `Coloring.lean` | [Coloring/Full.lean](../Coloring/Full.lean) |
| `ColoringAux.lean` | [Coloring/FullBookkeeping.lean](../Coloring/FullBookkeeping.lean) |
| `ColoringNative.lean` | [Runtime/Coloring/Components.lean](../Runtime/Coloring/Components.lean) |
| `ColoringNative2.lean` | [Runtime/Coloring/CoordinateBounds.lean](../Runtime/Coloring/CoordinateBounds.lean) |
| `ColoringNative2Column.lean` | [Runtime/Coloring/Column.lean](../Runtime/Coloring/Column.lean) |
| `ColoringNative2Direction.lean` | [Runtime/Coloring/Direction.lean](../Runtime/Coloring/Direction.lean) |
| `ColoringNative2Height.lean` | [Runtime/Coloring/ProjectorBounds.lean](../Runtime/Coloring/ProjectorBounds.lean) |
| `ColoringNative2Projector.lean` | [Runtime/Coloring/CachedProjector.lean](../Runtime/Coloring/CachedProjector.lean) |
| `ColoringNative2Walk.lean` | [Runtime/Coloring/WalkDenominators.lean](../Runtime/Coloring/WalkDenominators.lean) |
| `ColoringNative2Weights.lean` | [Runtime/Coloring/Weights.lean](../Runtime/Coloring/Weights.lean) |
| `ColoringNative3.lean` | [Runtime/Coloring/Certificate.lean](../Runtime/Coloring/Certificate.lean) |
| `ColoringNative3Bounds.lean` | [Runtime/Coloring/DirectionBounds.lean](../Runtime/Coloring/DirectionBounds.lean) |
| `ColoringNative3Box.lean` | [Runtime/Coloring/Box.lean](../Runtime/Coloring/Box.lean) |
| `ColoringNative3ConstraintData.lean` | [Runtime/Coloring/ConstraintData.lean](../Runtime/Coloring/ConstraintData.lean) |
| `ColoringNative3Constraints.lean` | [Runtime/Coloring/Constraints.lean](../Runtime/Coloring/Constraints.lean) |
| `ColoringNative3Data.lean` | [Runtime/Coloring/DirectionDataBounds.lean](../Runtime/Coloring/DirectionDataBounds.lean) |
| `ColoringNative3Gram.lean` | [Runtime/Coloring/Gram/DeterminantBounds.lean](../Runtime/Coloring/Gram/DeterminantBounds.lean) |
| `ColoringNative3GramAlgebra.lean` | [Runtime/Coloring/Gram/Adjugate.lean](../Runtime/Coloring/Gram/Adjugate.lean) |
| `ColoringNative3GramComplete.lean` | [Runtime/Coloring/Gram/Identification.lean](../Runtime/Coloring/Gram/Identification.lean) |
| `ColoringNative3GramInduction.lean` | [Runtime/Coloring/Gram/RowInduction.lean](../Runtime/Coloring/Gram/RowInduction.lean) |
| `ColoringNative3GramKernel.lean` | [Runtime/Coloring/Gram/Kernel.lean](../Runtime/Coloring/Gram/Kernel.lean) |
| `ColoringNative3GramProjection.lean` | [Runtime/Coloring/Gram/Projection.lean](../Runtime/Coloring/Gram/Projection.lean) |
| `ColoringNative3Growth.lean` | [Runtime/Coloring/PartialCallGrowth.lean](../Runtime/Coloring/PartialCallGrowth.lean) |
| `ColoringNative3Loop.lean` | [Runtime/Coloring/Loop.lean](../Runtime/Coloring/Loop.lean) |
| `ColoringNative3Partial.lean` | [Runtime/Coloring/PartialCertificate.lean](../Runtime/Coloring/PartialCertificate.lean) |
| `ColoringNative3PartialDenominators.lean` | [Runtime/Coloring/PartialDenominators.lean](../Runtime/Coloring/PartialDenominators.lean) |
| `ColoringNative3Program.lean` | [Runtime/Coloring/Preparation.lean](../Runtime/Coloring/Preparation.lean) |
| `ColoringNative3Recursion.lean` | [Runtime/Coloring/Recursion/Program.lean](../Runtime/Coloring/Recursion/Program.lean) |
| `ColoringNative3RecursionCorrect.lean` | [Runtime/Coloring/Recursion/Correct.lean](../Runtime/Coloring/Recursion/Correct.lean) |
| `ColoringNative3RecursionDenominators.lean` | [Runtime/Coloring/Recursion/Denominators.lean](../Runtime/Coloring/Recursion/Denominators.lean) |
| `ColoringNative3RecursionEncoding.lean` | [Runtime/Coloring/Recursion/Encoding.lean](../Runtime/Coloring/Recursion/Encoding.lean) |
| `ColoringNative3RecursionExplicit.lean` | [Runtime/Coloring/Recursion/Explicit.lean](../Runtime/Coloring/Recursion/Explicit.lean) |
| `ColoringNative3RecursionGrowth.lean` | [Runtime/Coloring/Recursion/Growth.lean](../Runtime/Coloring/Recursion/Growth.lean) |
| `ColoringNative3RecursionLists.lean` | [Runtime/Coloring/Recursion/Lists.lean](../Runtime/Coloring/Recursion/Lists.lean) |
| `ColoringNative3RecursionStatic.lean` | [Runtime/Coloring/Recursion/Static.lean](../Runtime/Coloring/Recursion/Static.lean) |
| `ColoringNative3Reify.lean` | [Runtime/Coloring/ReifyBounds.lean](../Runtime/Coloring/ReifyBounds.lean) |
| `ColoringNative3Sort.lean` | [Runtime/Coloring/HeavyIndices.lean](../Runtime/Coloring/HeavyIndices.lean) |
| `ColoringNative3SortCore.lean` | [Runtime/Coloring/Sorting.lean](../Runtime/Coloring/Sorting.lean) |
| `ColoringNative3StateBounds.lean` | [Runtime/Coloring/StateBounds.lean](../Runtime/Coloring/StateBounds.lean) |
| `ColoringNative3Step.lean` | [Runtime/Coloring/Step.lean](../Runtime/Coloring/Step.lean) |
| `ColoringNativeArithmetic.lean` | [Runtime/Coloring/Initialization.lean](../Runtime/Coloring/Initialization.lean) |
| `ColoringNativeDenominators.lean` | [Runtime/Coloring/Denominators.lean](../Runtime/Coloring/Denominators.lean) |
| `ColoringNativeProjector.lean` | [Runtime/Coloring/ProjectorStage.lean](../Runtime/Coloring/ProjectorStage.lean) |
| `ColoringNativeRecursion.lean` | [Runtime/Coloring/OutputBounds.lean](../Runtime/Coloring/OutputBounds.lean) |
| `ColoringNativeSqrt.lean` | [Runtime/Coloring/Sqrt.lean](../Runtime/Coloring/Sqrt.lean) |
| `ColoringTrajectory.lean` | [Coloring/Trajectory/Basic.lean](../Coloring/Trajectory/Basic.lean) |
| `ColoringTrajectoryGeometry.lean` | [Coloring/Trajectory/Geometry.lean](../Coloring/Trajectory/Geometry.lean) |
| `ColoringTrajectoryInitial.lean` | [Coloring/Trajectory/Initial.lean](../Coloring/Trajectory/Initial.lean) |
| `ColoringTrajectoryLower.lean` | [Coloring/Trajectory/Lower.lean](../Coloring/Trajectory/Lower.lean) |
| `ColoringTrajectoryPotential.lean` | [Coloring/Trajectory/Potential.lean](../Coloring/Trajectory/Potential.lean) |
| `ColoringTrajectoryProgress.lean` | [Coloring/Trajectory/Progress.lean](../Coloring/Trajectory/Progress.lean) |
| `ColoringTrajectoryProjector.lean` | [Coloring/Trajectory/Projector.lean](../Coloring/Trajectory/Projector.lean) |
| `ColoringTrajectoryUpper.lean` | [Coloring/Trajectory/Upper.lean](../Coloring/Trajectory/Upper.lean) |
| `DisjointTests.lean` | [Anchor/LocalExpectations.lean](../Anchor/LocalExpectations.lean) |
| `FlatFrontend2Derivative.lean` | [FlatFrontend/Enclosure/Derivative.lean](../FlatFrontend/Enclosure/Derivative.lean) |
| `FlatFrontend2Endpoints.lean` | [FlatFrontend/Enclosure/Endpoints.lean](../FlatFrontend/Enclosure/Endpoints.lean) |
| `FlatFrontend2Kernel.lean` | [FlatFrontend/Enclosure/Kernel.lean](../FlatFrontend/Enclosure/Kernel.lean) |
| `FlatFrontend2Main.lean` | [FlatFrontend/Enclosure/Preparation.lean](../FlatFrontend/Enclosure/Preparation.lean) |
| `FlatFrontend2Precision.lean` | [FlatFrontend/Enclosure/Precision.lean](../FlatFrontend/Enclosure/Precision.lean) |
| `FlatFrontend2Runs.lean` | [FlatFrontend/Enclosure/Runs.lean](../FlatFrontend/Enclosure/Runs.lean) |
| `FlatFrontend2Threshold.lean` | [FlatFrontend/Enclosure/Threshold.lean](../FlatFrontend/Enclosure/Threshold.lean) |
| `FlatFrontend3Blocks.lean` | [FlatFrontend/Geometry/Blocks.lean](../FlatFrontend/Geometry/Blocks.lean) |
| `FlatFrontend3Budget.lean` | [FlatFrontend/Geometry/Budget.lean](../FlatFrontend/Geometry/Budget.lean) |
| `FlatFrontend3Complement.lean` | [FlatFrontend/Geometry/Complement.lean](../FlatFrontend/Geometry/Complement.lean) |
| `FlatFrontend3Cosine.lean` | [FlatFrontend/Geometry/Cosine.lean](../FlatFrontend/Geometry/Cosine.lean) |
| `FlatFrontend3Count.lean` | [FlatFrontend/Geometry/Count.lean](../FlatFrontend/Geometry/Count.lean) |
| `FlatFrontend3Coverage.lean` | [FlatFrontend/Geometry/Coverage.lean](../FlatFrontend/Geometry/Coverage.lean) |
| `FlatFrontend3Even.lean` | [FlatFrontend/Geometry/Even.lean](../FlatFrontend/Geometry/Even.lean) |
| `FlatFrontend3Grid.lean` | [FlatFrontend/Geometry/Grid.lean](../FlatFrontend/Geometry/Grid.lean) |
| `FlatFrontend3Main.lean` | [FlatFrontend/Geometry/Certificate.lean](../FlatFrontend/Geometry/Certificate.lean) |
| `FlatFrontend3Margin.lean` | [FlatFrontend/Geometry/Margin.lean](../FlatFrontend/Geometry/Margin.lean) |
| `FlatFrontend3Ordering.lean` | [FlatFrontend/Geometry/Ordering.lean](../FlatFrontend/Geometry/Ordering.lean) |
| `FlatFrontend3Parameters.lean` | [FlatFrontend/Geometry/Parameters.lean](../FlatFrontend/Geometry/Parameters.lean) |
| `FlatFrontend3Polynomial.lean` | [FlatFrontend/Geometry/Polynomial.lean](../FlatFrontend/Geometry/Polynomial.lean) |
| `FlatFrontend3Sampling.lean` | [FlatFrontend/Geometry/Sampling.lean](../FlatFrontend/Geometry/Sampling.lean) |
| `FlatFrontend3Scan.lean` | [FlatFrontend/Geometry/Scan.lean](../FlatFrontend/Geometry/Scan.lean) |
| `FlatFrontend3Wave.lean` | [FlatFrontend/Geometry/Wave.lean](../FlatFrontend/Geometry/Wave.lean) |
| `FlatFrontend3Words.lean` | [FlatFrontend/Geometry/Words.lean](../FlatFrontend/Geometry/Words.lean) |
| `FlatFrontendCoefficients.lean` | [FlatFrontend/Coefficients.lean](../FlatFrontend/Coefficients.lean) |
| `FlatFrontendDerivatives.lean` | [FlatFrontend/Derivatives.lean](../FlatFrontend/Derivatives.lean) |
| `FlatFrontendEnclosures.lean` | [FlatFrontend/Enclosures.lean](../FlatFrontend/Enclosures.lean) |
| `FlatFrontendInputs.lean` | [FlatFrontend/Inputs.lean](../FlatFrontend/Inputs.lean) |
| `FlatFrontendMain.lean` | [FlatFrontend/Preparation.lean](../FlatFrontend/Preparation.lean) |
| `FlatFrontendParameters.lean` | [FlatFrontend/Parameters.lean](../FlatFrontend/Parameters.lean) |
| `FlatFrontendProgram.lean` | [FlatFrontend/Program.lean](../FlatFrontend/Program.lean) |
| `FlatFrontendRational.lean` | [FlatFrontend/Rational.lean](../FlatFrontend/Rational.lean) |
| `FlatFrontendRuntime.lean` | [Runtime/FlatFrontend/Certificate.lean](../Runtime/FlatFrontend/Certificate.lean) |
| `FlatFrontendRuntimeChebyshev.lean` | [Runtime/FlatFrontend/Chebyshev.lean](../Runtime/FlatFrontend/Chebyshev.lean) |
| `FlatFrontendRuntimeParameters.lean` | [Runtime/FlatFrontend/Parameters.lean](../Runtime/FlatFrontend/Parameters.lean) |
| `FlatFrontendRuntimeScan.lean` | [Runtime/FlatFrontend/Scan.lean](../Runtime/FlatFrontend/Scan.lean) |
| `FlatFrontendRuntimeTaylor.lean` | [Runtime/FlatFrontend/Taylor.lean](../Runtime/FlatFrontend/Taylor.lean) |
| `FlatFrontendRuntimeWords.lean` | [Runtime/FlatFrontend/Words.lean](../Runtime/FlatFrontend/Words.lean) |
| `FlatFrontendTaylor.lean` | [FlatFrontend/Taylor.lean](../FlatFrontend/Taylor.lean) |
| `FlatFrontendWords.lean` | [FlatFrontend/Words.lean](../FlatFrontend/Words.lean) |
| `FlatSeedBounds.lean` | [Seed/Flat/Bounds.lean](../Seed/Flat/Bounds.lean) |
| `FlatSeedMain.lean` | [Seed/Assembly.lean](../Seed/Assembly.lean) |
| `FlatSeedRounding.lean` | [Seed/Flat/Rounding.lean](../Seed/Flat/Rounding.lean) |
| `FlatSeedTaylor.lean` | [Seed/Flat/Taylor.lean](../Seed/Flat/Taylor.lean) |
| `Homogenization.lean` | [Anchor/Homogenization.lean](../Anchor/Homogenization.lean) |
| `Main.lean` | [Reduction/Completeness.lean](../Reduction/Completeness.lean) |
| `MainAssembly.lean` | [Seed/Family.lean](../Seed/Family.lean) |
| `MainFinal.lean` | [Main.lean](../Main.lean) |
| `Membership.lean` | [Membership/NP.lean](../Membership/NP.lean) |
| `MembershipAux.lean` | [Membership/Verifier.lean](../Membership/Verifier.lean) |
| `MembershipCert.lean` | [Membership/Certificates.lean](../Membership/Certificates.lean) |
| `MembershipPoly.lean` | [Membership/PolyTime.lean](../Membership/PolyTime.lean) |
| `NormDivided.lean` | [Coset/Norm/Divided.lean](../Coset/Norm/Divided.lean) |
| `NormDividedAux.lean` | [Coset/Norm/FactorMultiplicity.lean](../Coset/Norm/FactorMultiplicity.lean) |
| `NormFinal.lean` | [Coset/Norm/SourceSeparation.lean](../Coset/Norm/SourceSeparation.lean) |
| `NormMahler.lean` | [Coset/Norm/Mahler.lean](../Coset/Norm/Mahler.lean) |
| `NormMahlerAux.lean` | [Coset/Norm/NewtonSums.lean](../Coset/Norm/NewtonSums.lean) |
| `NormResultant.lean` | [Coset/Norm/Resultant.lean](../Coset/Norm/Resultant.lean) |
| `NormResultantAux.lean` | [Coset/Norm/RootProducts.lean](../Coset/Norm/RootProducts.lean) |
| `NormSeparation.lean` | [Coset/Norm/Separation.lean](../Coset/Norm/Separation.lean) |
| `NormSeparationAux.lean` | [Coset/Norm/Estimates.lean](../Coset/Norm/Estimates.lean) |
| `Packing.lean` | [Coset/Packing.lean](../Coset/Packing.lean) |
| `ParityBlock.lean` | [Coset/ParityBlock.lean](../Coset/ParityBlock.lean) |
| `PartialColoring.lean` | [Coloring/Partial/Specification.lean](../Coloring/Partial/Specification.lean) |
| `PartialColoringAlg.lean` | [Coloring/Partial/Projector.lean](../Coloring/Partial/Projector.lean) |
| `PartialColoringAlgBounds.lean` | [Coloring/Partial/Bounds.lean](../Coloring/Partial/Bounds.lean) |
| `PartialColoringAlgCorrect.lean` | [Coloring/Partial/Correct.lean](../Coloring/Partial/Correct.lean) |
| `PartialColoringAlgInvariants.lean` | [Coloring/Partial/Invariants.lean](../Coloring/Partial/Invariants.lean) |
| `PartialColoringAlgProjector.lean` | [Coloring/Partial/ProjectorTable.lean](../Coloring/Partial/ProjectorTable.lean) |
| `PartialColoringAlgRuntime.lean` | [Runtime/Coloring/Arithmetic.lean](../Runtime/Coloring/Arithmetic.lean) |
| `PartialColoringAlgWalk.lean` | [Coloring/Partial/Walk.lean](../Coloring/Partial/Walk.lean) |
| `Problem.lean` | [Problem.lean](../Problem.lean) |
| `ReductionMap.lean` | [Reduction/Map.lean](../Reduction/Map.lean) |
| `ReductionMapAux.lean` | [Runtime/Reduction/Packing.lean](../Runtime/Reduction/Packing.lean) |
| `ReductionMapPoly.lean` | [Reduction/PolyTime.lean](../Reduction/PolyTime.lean) |
| `RepairRuntime.lean` | [Runtime/Repair/Arithmetic.lean](../Runtime/Repair/Arithmetic.lean) |
| `RepairRuntimeCandidates.lean` | [Runtime/Repair/Candidates.lean](../Runtime/Repair/Candidates.lean) |
| `RepairRuntimeLoop.lean` | [Runtime/Repair/Loop.lean](../Runtime/Repair/Loop.lean) |
| `RepairRuntimePotential.lean` | [Runtime/Repair/Potential.lean](../Runtime/Repair/Potential.lean) |
| `RepairRuntimeProbability.lean` | [Runtime/Repair/Probability.lean](../Runtime/Repair/Probability.lean) |
| `RepairRuntimeRows.lean` | [Runtime/Repair/Rows.lean](../Runtime/Repair/Rows.lean) |
| `RudinShapiro.lean` | [Seed/RudinShapiro/Basic.lean](../Seed/RudinShapiro/Basic.lean) |
| `RudinShapiroAux.lean` | [Seed/RudinShapiro/Prefixes.lean](../Seed/RudinShapiro/Prefixes.lean) |
| `RudinShapiroBounds.lean` | [Seed/RudinShapiro/Bounds.lean](../Seed/RudinShapiro/Bounds.lean) |
| `RudinShapiroDerivative.lean` | [Seed/RudinShapiro/Derivative.lean](../Seed/RudinShapiro/Derivative.lean) |
| `RudinShapiroWave.lean` | [Seed/RudinShapiro/Wave.lean](../Seed/RudinShapiro/Wave.lean) |
| `SeedAlgorithm.lean` | [Seed/Algorithm.lean](../Seed/Algorithm.lean) |
| `SeedAlgorithmRuntime.lean` | [Runtime/Seed/Composition.lean](../Runtime/Seed/Composition.lean) |
| `SeedGeometry.lean` | [Seed/Geometry/Basic.lean](../Seed/Geometry/Basic.lean) |
| `SeedGeometryAux.lean` | [Seed/Geometry/JetSeparation.lean](../Seed/Geometry/JetSeparation.lean) |
| `SeedGeometryCells.lean` | [Seed/Geometry/Cells.lean](../Seed/Geometry/Cells.lean) |
| `SeedGeometryComponents.lean` | [Seed/Geometry/Components.lean](../Seed/Geometry/Components.lean) |
| `SeedGeometryRolle.lean` | [Seed/Geometry/Rolle.lean](../Seed/Geometry/Rolle.lean) |
| `SeedIntervals.lean` | [Seed/Intervals.lean](../Seed/Intervals.lean) |
| `Sidon.lean` | [Source/Sidon/Basic.lean](../Source/Sidon/Basic.lean) |
| `SidonEncoding.lean` | [Source/Sidon/Encoding.lean](../Source/Sidon/Encoding.lean) |
| `SidonReciprocal.lean` | [Source/Sidon/Reciprocal.lean](../Source/Sidon/Reciprocal.lean) |
| `SineKernel.lean` | [Seed/SineKernel/Specification.lean](../Seed/SineKernel/Specification.lean) |
| `SineKernelProof.lean` | [Seed/SineKernel/Integral.lean](../Seed/SineKernel/Integral.lean) |
| `SineKernelProofAux.lean` | [Seed/SineKernel/EndpointPhase.lean](../Seed/SineKernel/EndpointPhase.lean) |
| `SineKernelProofCorrection.lean` | [Seed/SineKernel/Correction.lean](../Seed/SineKernel/Correction.lean) |
| `SineKernelProofDecomposition.lean` | [Seed/SineKernel/Decomposition.lean](../Seed/SineKernel/Decomposition.lean) |
| `SineKernelProofLobes.lean` | [Seed/SineKernel/Lobes.lean](../Seed/SineKernel/Lobes.lean) |
| `SineKernelProofNear.lean` | [Seed/SineKernel/Near.lean](../Seed/SineKernel/Near.lean) |
| `SineKernelProofReflected.lean` | [Seed/SineKernel/Reflected.lean](../Seed/SineKernel/Reflected.lean) |
| `SineKernelProofSineIntegral.lean` | [Seed/SineKernel/SineIntegral.lean](../Seed/SineKernel/SineIntegral.lean) |
| `SineKernelProofTail.lean` | [Seed/SineKernel/Tail.lean](../Seed/SineKernel/Tail.lean) |
| `SineKernelProofVariation.lean` | [Seed/SineKernel/Variation.lean](../Seed/SineKernel/Variation.lean) |
| `SourceMap.lean` | [Source/Map.lean](../Source/Map.lean) |
| `SourceMapAux.lean` | [Runtime/Source/Normalize.lean](../Runtime/Source/Normalize.lean) |
| `SourceMapPoly.lean` | [Runtime/Source/PolyTime.lean](../Runtime/Source/PolyTime.lean) |
| `SourceMapPrime.lean` | [Runtime/Source/PrimeSearch.lean](../Runtime/Source/PrimeSearch.lean) |

`coset_npHard` and `coset_npComplete` move from the old `Main.lean` to the new
`Main.lean`; the old conditional module results and integral gap move to
`Reduction/Completeness.lean`. Both unconditional headline results now live in `Main.lean`.

## Dead-code audit

The initial transitive import closure of `MainFinal`, `Main`, and `Membership`, counting
both ordinary and `public import` edges, contained 181 of 182 modules. The single excluded
module was `SidonAudit.lean`: it contained only historical prose and no declarations.
Its obsolete integration-status notes were removed with the file. Whole-repository searches
found no Lean imports of Power2 modules outside this library and its root.

`DisjointTests.lean` is live exact-probability mathematics, now `Anchor/LocalExpectations.lean`.
The `ColoringNative*`, `ColoringNative2*`, `FlatFrontend2*`, and `FlatFrontend3*` families are
also live; their names described development passes rather than dead alternate routes.

Whole-repository `rg` searches preceded each declaration deletion. Removed declarations:

- `FullColoringRuntimeHypothesis` and its sole dependent assembly `spectralSeedFamily_of`: the
  obsolete universal-program runtime closure identified by AUDIT2 is not used by the proof.
- `spectralSeedFamily_of_remaining`, `moduleSVP_npComplete_of_remaining`, and
  `moduleSVP_npComplete_of_fullColoringNative`: stale final wrappers whose named premises are
  now discharged. `spectralSeedFamily_holds` directly assembles the concrete certified seed.
- Scratch `#print` commands in the old `Main.lean` and `NormFinal.lean`.

Preserved interfaces include `moduleSVP_npComplete_of (hJ : RigidAnchorFamilyHypothesis)`,
`rigidAnchorFamily_of_seed`, `moduleSVP_npComplete_of_seed`, and
`spectralSeedFamily_of_fullColor`. No mathematical statement of a surviving declaration changed.
