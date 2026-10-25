# IdealCVP — paper ↔ Lean map

Paper: [Exact CVP Is NP-Complete for Principal Cyclotomic Ideals](paper/2608.23828.pdf).
The [LaTeX source](paper/src/main.tex) supplies the labels below;
[main_module_sivp.tex](paper/src/main_module_sivp.tex) also includes the module-SIVP extension.
Names are in `IdealCVP` unless qualified. File links are relative to `IdealCVP/`.
Import `IdealCVP` for the whole library.

| Paper section / lemma | Lean name | File |
| --- | --- | --- |
| §2, coefficient distances and exact minima | `CVPYes`, `MinimumSquaredDistance` | [Lattice.lean](Lattice.lean) |
| §2, X3C and masked Boolean equations | `X3CInstance`, `X3CInstance.hasExactCover_iff_hasSolution`, `X3CInstance.exactCoverEquivFeasible` | [X3C.lean](X3C.lean) |
| §2, `def:principal-cyclotomic-cvp`, actual quotient ring | `Cyclotomic.quotEquiv`, `Cyclotomic.toQuot_mul`, `Cyclotomic.mem_principalIdealLattice_iff` | [Quotient.lean](Quotient.lean) |
| §2, nonzero principal ideals have full rank | `Cyclotomic.modulus_irreducible`, `Cyclotomic.principalMultiplicationBasis`, `Cyclotomic.principal_full_rank` | [GeneralFullRank.lean](GeneralFullRank.lean) |
| §2, `lem:canonical`, canonical embedding | `Canonical.norm_identity`, `Canonical.field_norm_identity`, `Canonical.principalCVP_iff_rational` | [Canonical.lean](Canonical.lean) |
| §3.1, `lem:sidon`, Erdős–Turán positions | `SidonPositions.erdosTuranAlpha`, `SidonPositions.erdosTuran_differences`, `SidonPositions.erdosTuran` | [Sidon.lean](Sidon.lean) |
| §3.1, distinct monomials and no wrap | `SidonPositions.hExp_injective`, `SidonPositions.crossExp_injective`, `SidonPositions.row_ne_cross` | [Coordinates.lean](Coordinates.lean) |
| §3.1, `lem:boolean-identity` | `ReductionData.ha_expansion`, `ReductionData.boolean_identity` | [Reduction.lean](Reduction.lean) |
| §3.2, parity block identity | `ReductionData.generator_product`, `ReductionData.block_product` | [Reduction.lean](Reduction.lean) |
| §3.2, `lem:admissible`, rounding | `rounding_gap` | [Rounding.lean](Rounding.lean) |
| §3.2, `lem:admissible`, forbidden multipliers | `Cyclotomic.sparse_mul_bound`, `Cyclotomic.block_norm_lower_bound`; `penalty_separation` | [Norms.lean](Norms.lean), [Penalty.lean](Penalty.lean) |
| §3.2, `lem:admissible`, allowed / forbidden cases | `ReductionData.admissible_allowed`, `ReductionData.admissible_forbidden`, `ReductionData.discrete_gap` | [Reduction.lean](Reduction.lean) |
| §3.2, `thm:compiler`, correctness and exact gap | `ReductionData.compiler_correct`, `ReductionData.compiler_yes`, `ReductionData.compiler_no`, `ReductionData.feasibleEquivClosest` | [Main.lean](Main.lean) |
| §3.2, `thm:cyclotomic-cvp`, X3C specialization | `x3cToCVP`, `x3c_correct`, `x3c_yes_gap`, `x3c_no_gap`, `exactCoverEquivClosest` | [Main.lean](Main.lean) |
| §3.2, `thm:cyclotomic-cvp`, quotient formulation | `x3c_correct_quotient` | [Quotient.lean](Quotient.lean) |
| §3.2, output dimension | `x3c_dimension_le` | [Dimensions.lean](Dimensions.lean) |
| §3.2, executable data and magnitude bounds | `compileX3C`, `compileX3C_correct`, `compileX3C_size` | [SizeBounds.lean](SizeBounds.lean) |
| §3.2, binary / unary encoding sizes | `compileX3C_coeff_bits`, `compileX3C_threshold_bits`, `compileX3C_outputLength_le`, `compileX3C_unaryLength_le` | [StrongBounds.lean](StrongBounds.lean) |
| §3.2, native polynomial-time implementation | `compileFast_correct`; `poly_compileFast` | [Complexity/CompileFastBridge.lean](Complexity/CompileFastBridge.lean), [Complexity/CompileFastPolyTime.lean](Complexity/CompileFastPolyTime.lean) |
| §3.2, list X3C → principal CVP | `compileX3CList_correct`, `polyTimeReducible_X3C_CVP` | [Complexity/X3CToCVP.lean](Complexity/X3CToCVP.lean) |
| §3.2, source NP-completeness and paper hardness route | `x3c_npComplete`, `principalCVP_npHard_via_X3C` | [Complexity/SatToX3C.lean](Complexity/SatToX3C.lean) |
| §3.2, principal CVP NP membership | `principalCVP_mem_NP` | [Complexity/Verifier.lean](Complexity/Verifier.lean) |
| §3.2, `thm:cyclotomic-cvp`, NP-completeness | `principalCVP_npComplete` | [Complexity/NPComplete.lean](Complexity/NPComplete.lean) |
| §3.3, `lem:principal-crt`, cyclic lift | `Cyclic.product_distance`, `Cyclic.small_iff`, `Cyclic.smallEquiv`, `Cyclic.principal_full_rank` | [Cyclic.lean](Cyclic.lean) |
| §3.3, `thm:cyclic-cvp`, correctness and gap | `x3c_cyclic_correct`, `x3c_cyclic_yes_gap`, `x3c_cyclic_no_gap` | [Cyclic.lean](Cyclic.lean) |
| §3.3, cyclic hardness | `principalCyclicCVP_npHard` | [Complexity/CyclicProblem.lean](Complexity/CyclicProblem.lean) |
| §3.3, recognizable separated cyclic subclass | `principalCyclicCVP_npComplete` | [Complexity/SeparatedCyclic.lean](Complexity/SeparatedCyclic.lean) |
| §3.3, arbitrary cyclic generators, including singular ones | `principalCyclicCVPGeneral_mem_NP`, `principalCyclicCVPGeneral_npComplete` | [Complexity/GeneralCyclic.lean](Complexity/GeneralCyclic.lean) |
| §4, `thm:fixed-family`, universe-dependent ideal | `Fixed.generator_independent`, `Fixed.fixed_family_correct`, `Fixed.fixed_family_yes`, `Fixed.fixed_family_no` | [Fixed.lean](Fixed.lean) |
| §4, repeated indexed triples | `fixed_family_correct_indexed`, `fixed_family_yes_indexed`, `fixed_family_no_indexed` | [FixedIndexed.lean](FixedIndexed.lean) |
| §4, executable ordered-triple fixed family | `FixedFast.generator_independent`, `polyTimeReducible_X3C_FixedCVPP`, `fixedCVPP_npHard` | [Complexity/FixedCompiler.lean](Complexity/FixedCompiler.lean) |
| §4, abstract preprocessing advice | `CVPPScheme`, `cvpp_advice_decides`, `cvpp_advice_decides_indexed` | [CVPP.lean](CVPP.lean) |
| §4, P/poly closure used in `cor:cvpp` | `Cslib.Circuits.Boolean.PPoly.of_polyTimeReducible` | [Complexity/PPolyReduction.lean](Complexity/PPolyReduction.lean) |
| §4, `cor:cvpp`, circuit and advice formulations | `np_subset_ppoly_of_fixedCVPP`, `PH_eq_SigmaP_two_of_fixedCVPP`, `PH_eq_SigmaP_two_of_polyCVPP` | [Complexity/CVPPClass.lean](Complexity/CVPPClass.lean) |
| Module extension, `def:module-sivp`, field independence | `ModuleSIVP.Independent`, `ModuleSIVP.SecondMinimumSq`, `ModuleSIVP.ExactSecondMinimumSq` | [ModuleSIVP.lean](ModuleSIVP.lean) |
| Module extension, `lem:module-completion` | `ModuleSIVP.module_completion` | [ModuleSIVP.lean](ModuleSIVP.lean) |
| Module extension, `thm:module-sivp`, mathematical reduction | `x3cToModuleSIVP`, `x3c_module_sivp_correct`, `x3c_module_sivp_yes`, `x3c_module_sivp_no` | [ModuleSIVP.lean](ModuleSIVP.lean) |
| Module extension, triangular-basis NP-completeness | `moduleSIVP_npComplete` | [Complexity/ModuleProblem.lean](Complexity/ModuleProblem.lean) |
| Module extension, arbitrary independent integral bases | `ModuleSIVP.generalMatrix_det_iff`; `moduleSIVPGeneral_npComplete` | [GeneralModule.lean](GeneralModule.lean), [Complexity/GeneralModule.lean](Complexity/GeneralModule.lean) |
| Rational inputs and squared thresholds | `rationalCVP_clear_denominators`, `ModuleSIVP.rationalBasisSIVP_clear_denominators` | [Rational.lean](Rational.lean) |
| Canonical-embedding versions of the reductions | `x3c_correct_canonical`, `x3c_yes_gap_canonical`, `x3c_no_gap_canonical`, `x3c_module_sivp_yes_canonical`, `x3c_module_sivp_no_canonical` | [Canonical.lean](Canonical.lean) |
| Explicit verifier and produced certificates | `verify_eq_true`, `matrix_cvp_iff`, `x3c_bounded_certificate` | [Certificates.lean](Certificates.lean) |
| NP certificates for arbitrary nonsingular integer bases | `certificate_coeff_le`, `cvp_iff_bounded_certificate`, `decideBoundedCVP_eq_true` | [CertificateBound.lean](CertificateBound.lean) |
| NP certificates for arbitrary-rank integer systems | `exists_bounded_integer_preimage`, `exists_integer_preimage_bits` | [IntegerPreimage.lean](IntegerPreimage.lean) |
| Closest-vector oracle → cover extraction and decision | `X3CInstance.decode`, `X3CInstance.decode_closest_isExactCover`, `x3c_iff_decode_oracle` | [SearchToDecision.lean](SearchToDecision.lean) |

## Notes

- Indices are zero-based. Coefficient squared norms are integral. The cyclotomic YES minimum
  is exactly Δ and the NO lower bound is Δ+4; the cyclic lift doubles the dimension and gives
  8Δ versus 8Δ+32. Canonical embedding multiplies cyclotomic squared norms and gaps by `d`.
  The Fourier norm identity holds for real coefficients in every positive dimension;
  the cyclotomic field applications use dyadic dimensions.
  Exact minima include attainment and a universal lower bound; the cover correspondence is
  a bijection. Approximation variants beyond these exact gaps are not formalised.
- The paper's Erdős–Turán positions give `d ≤ 4(3q)(8n²+1)` for the mathematical X3C compiler.
  The native runtime proof uses the larger cubic Sidon construction, with
  `d ≤ 4M(6n³+2n+1)` for padded row/column counts `M,n`. Its total list program handles malformed
  and degenerate inputs. [Complexity/CompileBridge.lean](Complexity/CompileBridge.lean) retains
  `compileList_correct` for the prime-search reference compiler; the optional runtime premise in
  `principalCVP_npComplete_of_compilePoly` ([Complexity/NPComplete.lean](Complexity/NPComplete.lean))
  is absent from the unconditional headline theorem.
- Coefficient convolution is proved equivalent to multiplication in the actual polynomial
  quotient. Full rank holds for every nonzero dyadic cyclotomic generator, including `d = 1`.
  Arbitrary cyclic generators can be singular or zero; their NP certificates use the stronger
  rectangular integer-preimage bound, with no rank promise. For `n` columns the bound is
  `T^(16(n+1)²)`, where `T = 2 + m + n + Σ|Mᵢⱼ| + Σ|vᵢ|`. The proof uses integral Gram/adjugate
  kernel corrections and includes rank zero.
- Module-SIVP uses independence over the genuine rational cyclotomic field. The completion
  has exact second minimum `Q² + δ` for CVP minimum δ. The native triangular recognizer chooses
  `Q = 1 + ‖T‖² + ‖g‖²`, a larger valid scale than the mathematical ceiling-square-root choice.
  The general language extends this to all independent integral rank-two bases using their
  monomial-translate matrix. Rational bases and targets are scaled to actual integral spans;
  squared thresholds scale by the square of the denominator and are then floored, including
  negative thresholds.
- The mathematical fixed family enumerates three-element subsets. Its native runtime version
  enumerates all ordered triples, including disabled degenerate tuples. Only the target and
  threshold depend on the input collection; the generator depends on the unary universe size.
  Repeated indexed triples are allowed, and cannot both occur in an exact cover.
- CVPP is non-uniform: either polynomial-size circuits or polynomial-size advice with a
  polynomial-time query decider imply `NP ⊆ P/poly` and `PH = Σ₂`. Preprocessing time is unbounded.
  The P/poly closure theorem handles variable reduction-output lengths and arbitrary encodings
  without efficient-decoder assumptions.

The library is sorry-free; headline axiom audits use only `propext`, `Classical.choice`, and
`Quot.sound`. See [README.md](README.md) for the main results and
[specs/STATUS.md](specs/STATUS.md) for scope. Development history is retained in git.
