# IdealCVP — exact CVP for principal cyclotomic ideals

Lean formalisation of Jiaqi Liu, Yansong Feng, and Yanbin Pan,
[Exact CVP Is NP-Complete for Principal Cyclotomic Ideals](paper/2608.23828.pdf),
arXiv:2608.23828 (ePrint 2026/1793). The [LaTeX source](paper/src/) includes
[the module-SIVP extension](paper/src/main_module_sivp.tex).

For power-of-two `d`, exact decision-CVP on nonzero principal ideals of
`ℤ[X]/(X^d + 1)` is NP-complete under deterministic polynomial-time many-one reductions.
The cyclic problem over `ℤ[X]/(X^(2d) − 1)` is also NP-complete, including arbitrary singular
and zero generators. Exact module-SIVP is NP-complete for independent rank-two integral
cyclotomic bases. Thresholds use squared coefficient norms; proved canonical-embedding
identities account for the factor `d` in squared norms. Encoded malformed inputs are rejected.

## Main Lean results

All names below are in namespace `IdealCVP` unless qualified. File links are relative to
`IdealCVP/`. Import `IdealCVP` for the whole library; the complexity theorems are in
`IdealCVP.Complexity.*`.

| Result | Lean name | File |
| --- | --- | --- |
| **Principal cyclotomic CVP NP-completeness** | `principalCVP_npComplete : NPComplete encCVP PrincipalCVP` | [Complexity/NPComplete.lean](Complexity/NPComplete.lean) |
| X3C NP-completeness | `x3c_npComplete : NPComplete encX3C X3CLang` | [Complexity/SatToX3C.lean](Complexity/SatToX3C.lean) |
| Paper's X3C → principal CVP hardness route | `principalCVP_npHard_via_X3C` | [Complexity/SatToX3C.lean](Complexity/SatToX3C.lean) |
| Separated cyclic CVP NP-completeness | `principalCyclicCVP_npComplete : NPComplete encCVP SeparatedPrincipalCyclicCVP` | [Complexity/SeparatedCyclic.lean](Complexity/SeparatedCyclic.lean) |
| Arbitrary principal cyclic CVP hardness | `principalCyclicCVP_npHard` | [Complexity/CyclicProblem.lean](Complexity/CyclicProblem.lean) |
| Arbitrary principal cyclic CVP NP-completeness | `principalCyclicCVPGeneral_npComplete : NPComplete encCVP PrincipalCyclicCVP` | [Complexity/GeneralCyclic.lean](Complexity/GeneralCyclic.lean) |
| Triangular rank-two module-SIVP NP-completeness | `moduleSIVP_npComplete : NPComplete encModuleSIVP ModuleSIVPLang` | [Complexity/ModuleProblem.lean](Complexity/ModuleProblem.lean) |
| General rank-two module-SIVP NP-completeness | `moduleSIVPGeneral_npComplete : NPComplete encModuleSIVP ModuleSIVPGeneral` | [Complexity/GeneralModule.lean](Complexity/GeneralModule.lean) |
| P/poly closure under polynomial-time reductions | `Cslib.Circuits.Boolean.PPoly.of_polyTimeReducible` | [Complexity/PPolyReduction.lean](Complexity/PPolyReduction.lean) |
| Fixed-family CVPP circuits ⇒ NP ⊆ P/poly | `np_subset_ppoly_of_fixedCVPP` | [Complexity/CVPPClass.lean](Complexity/CVPPClass.lean) |
| Fixed-family CVPP circuits ⇒ PH = Σ₂ | `PH_eq_SigmaP_two_of_fixedCVPP` | [Complexity/CVPPClass.lean](Complexity/CVPPClass.lean) |
| Polynomial advice and query time for CVPP ⇒ PH = Σ₂ | `PH_eq_SigmaP_two_of_polyCVPP` | [Complexity/CVPPClass.lean](Complexity/CVPPClass.lean) |

The completeness results are unconditional. The CVPP consequences assume circuits or
polynomial-size advice and a polynomial-time query decider; preprocessing time is unbounded.
Complexity classes, reductions, and polynomial runtime use complexitylib's native multitape
Turing-machine definitions.

## Proof route

1. Encode X3C incidence equations as a masked Boolean system, and place variables at Sidon
   positions. A parity block and rounding force every short ideal vector to encode a solution.
   YES instances attain squared distance Δ; NO instances have squared distance at least Δ+4.
2. Identify coefficient convolution with multiplication in the actual cyclotomic quotient.
   Lift to the cyclic quotient with doubled dimension and gap 8Δ versus 8Δ+32.
3. Complete CVP instances to free rank-two modules, with exact second minimum `Q² + δ`
   for CVP minimum δ. Extend membership from triangular bases to arbitrary independent bases.
4. Use a universal triple collection with a presence mask to fix the ideal by universe size.
   Combine its hardness with P/poly closure and Karp–Lipton for the CVPP consequences.
5. Certify total list compilers, SAT → X3C, and polynomial runtime. Explicit integer-preimage
   bounds and Boolean verifiers prove NP membership, including singular cyclic inputs.

Rational scaling, canonical embeddings, and closest-vector cover extraction are also proved.
Approximation variants beyond the exact squared-distance gaps are not formalised.

## Layout

| Directory / files | Contents |
| --- | --- |
| `Lattice.lean`, `X3C.lean`, `Sidon.lean`, `Coordinates.lean` | Coefficient norms, source systems, sparse positions |
| `Reduction.lean`, `Main.lean`, `Blocks.lean`, `Rounding.lean`, `Norms.lean`, `Penalty.lean` | Mathematical compiler, separation, correctness, exact gaps |
| `Cyclotomic.lean`, `Quotient.lean`, `FullRank.lean`, `GeneralFullRank.lean`, `Cyclic.lean` | Actual quotient rings, lattice bases, cyclic lift |
| `ModuleSIVP.lean`, `GeneralModule.lean`, `Rational.lean`, `Canonical.lean` | Module minima, general bases, rational data, canonical norms |
| `Fixed.lean`, `FixedIndexed.lean`, `CVPP.lean`, `SearchToDecision.lean` | Fixed families, advice, cover extraction |
| `Dimensions.lean`, `SizeBounds.lean`, `StrongBounds.lean`, `Certificates.lean`, `CertificateBound.lean`, `IntegerPreimage.lean` | Output sizes, verifiers, certificate bounds |
| `Complexity/` | Encoded languages, executable compilers, native runtime, NP-completeness, CVPP classes |
| `paper/` | Paper PDF and LaTeX sources |
| `specs/` | Current scope and retained research notes |

[NOTES.md](NOTES.md) maps paper results to Lean declarations and records deviations.
[specs/STATUS.md](specs/STATUS.md) gives the verification scope. The root import is
[IdealCVP.lean](../IdealCVP.lean). Rank2ModuleSVP and Power2ModuleSVP reuse this infrastructure.

## Verification

The library is sorry-free and adds no axioms. Headline theorem axiom audits report only
`propext`, `Classical.choice`, and `Quot.sound`.

Build from the repository root with `lake build IdealCVP` (Lean / Mathlib `v4.36.0-rc1`).
If the artifact cache is read-only, use
`LAKE_CACHE_DIR=/tmp/hardness-lake-cache lake build IdealCVP`.
The shared tidy jobs use `/workspace/shared/jobs/hardness-tidy/build.sh IdealCVP`
to serialize builds.
