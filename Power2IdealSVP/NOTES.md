# Power2IdealSVP — paper ↔ Lean map

Paper: [power2-ideal-svp.pdf](paper/power2-ideal-svp.pdf), 27 October 2026.
Names below are relative to `Power2IdealSVP`; folder namespaces are written explicitly.
The table refers to the paper's actual numbered Lemmas 1–3 and equations (1)–(3).
Runtime results certify native tidy multitape Turing machines on the fixed encodings.

| Paper lemma, equation or construction | Lean declaration | File |
| --- | --- | --- |
| Theorem 1, encoded decision language | `IdealInput`, `encIdeal`, `IdealYes`, `IdealInput.WellFormed`, `IdealSVPLang` | [Problem.lean](Problem.lean) |
| §1.1, no-carry and Newton identities | `Source.three_digits_unique`, `Source.multiset_triple_eq_of_moments` | [Source/ThreeTerm.lean](Source/ThreeTerm.lean) |
| §1.1, labels and three-term uniqueness | `Source.base`, `Source.label`, `Source.three_term_unique`, `Source.two_term_unique`, `Source.ordered_difference_unique` | [Source/Labels.lean](Source/Labels.lean) |
| Lemma 1, common row/column | `Source.exists_row_or_column` | [Source/RowColumn.lean](Source/RowColumn.lean) |
| Lemma 1, extraction | `Source.difference_clique_extraction` | [Source/Extraction.lean](Source/Extraction.lean) |
| Lemma 1, converse and clique threshold | `Source.clique_positions_nonneg`, `Source.clique_iff_positions` | [Source/Extraction.lean](Source/Extraction.lean) |
| §1.1, polynomial labels | `Source.labelBound_le`, `Runtime.maxLabel_le` | [Source/Labels.lean](Source/Labels.lean), [Runtime/Structure.lean](Runtime/Structure.lean) |
| §1.2, negative-cyclic extension and shifts | `Spin.lift`, `Spin.xpow`, `Spin.mul_xpow_apply`, `Spin.mul_apply_lift` | [Algebra/SpinBasic.lean](Algebra/SpinBasic.lean) |
| §1.2, odd alternating spins and Θ | `Spin.OddAlternating`, `Spin.fieldAt`, `Spin.Theta`, `Spin.le_Theta_iff` | [Spin/Defs.lean](Spin/Defs.lean) |
| §1.2, Q, R₀, n, allowed windows and scales | `Spin.Q`, `Spin.R0`, `Spin.n`, `Spin.Eplus`, `Spin.A`, `Spin.T`, `Spin.RT`, `Spin.C`, `Spin.tau`, `Spin.L`, `Spin.G` | [Spin/Parameters.lean](Spin/Parameters.lean) |
| Lemma 2, skew pairing and balanced digits | `Spin.sum_skew_xpow`, `Spin.balanced_five_fin_zero` | [Algebra/SpinBasic.lean](Algebra/SpinBasic.lean) |
| Lemma 2, dyadic orbit exclusion | `Spin.power_two_orbit_exclusion` | [Algebra/SpinBasic.lean](Algebra/SpinBasic.lean) |
| Lemma 2, vanishing and exclusion | `Spin.guard_zero`, `Spin.guard_digit_zero`, `Spin.guard_cyclic_pair_allowed` | [Spin/Guard.lean](Spin/Guard.lean) |
| Lemma 2, antipodal correction | `Spin.xpow_antipodal`, `Spin.antipodal_guard_coefficient` | [Algebra/SpinBasic.lean](Algebra/SpinBasic.lean) |
| Lemma 3, monomial invariance under changing the cut | `Spin.OddAlternating.monomial_mul`, `Spin.fieldAt_monomial_mul`, `Spin.spinValue_monomial_mul` | [Spin/Shifts.lean](Spin/Shifts.lean) |
| Lemma 3, run partition | `Spin.runStarts`, `Spin.runBlock` | [Spin/Runs.lean](Spin/Runs.lean) |
| Lemma 3, short arc and normalization | `Spin.short_arc_integer`, `Spin.exists_signed_shift_short_support` | [Spin/ShortArc.lean](Spin/ShortArc.lean), [Spin/Normalization.lean](Spin/Normalization.lean) |
| Lemma 3, unique trimer and component labels | `Spin.trimer_unique`, `Spin.left_run_offset`, `Spin.right_run_offset`, `Spin.integer_geometry_with_card` | [Spin/Geometry.lean](Spin/Geometry.lean) |
| Lemma 3, coefficient classification | `Spin.classify_passing_spin` | [Spin/Classification.lean](Spin/Classification.lean) |
| Lemma 3, canonical alternating support | `Spin.integerAlternating_configuration`, `Spin.configurationSpin`, `Spin.oddAlternating_configurationSpin` | [Spin/Support.lean](Spin/Support.lean), [Spin/Converse.lean](Spin/Converse.lean) |
| §1.4, four window coefficients and directed endpoint table | `Spin.interactionKernel_cell_table`, `Spin.interactionKernel_cell_table_rev`, `Spin.componentField_table` | [Spin/Interaction.lean](Spin/Interaction.lean) |
| §1.4, endpoint totals and threshold | `Spin.smallConfigurationField_min`, `Spin.smallConfigurationField_threshold` | [Spin/Interaction.lean](Spin/Interaction.lean) |
| §1.4, actual negacyclic converse | `Spin.configurationSpin_field`, `Spin.spinValue_configurationSpin`, `Spin.exists_spin_of_differences` | [Spin/Converse.lean](Spin/Converse.lean) |
| Equation (1), abstract distance-set form | `Spin.theta_threshold_iff_differences` | [Spin/Equivalence.lean](Spin/Equivalence.lean) |
| §1.5, integral norm bounds and domination | `Algebra.abs_mul_le`, `Algebra.coercive`, `Algebra.dominated_injective`, `Algebra.normInf_dominated_signs` | [Algebra/IdealBasic.lean](Algebra/IdealBasic.lean) |
| §1.5, (1−X)S=2, XS=S−2, parity ideal | `Ideal.difference_sumPoly`, `Ideal.xPoly_sumPoly`, `Ideal.commonParity_iff`, `Ideal.mem_sumPoly_ideal_iff` | [Ideal/Parity.lean](Ideal/Parity.lean) |
| §1.5, full-sign objective Ψ | `Ideal.minField`, `Ideal.psi`, `Ideal.psi_attained` | [Ideal/FullSigns.lean](Ideal/FullSigns.lean) |
| §1.5, domain-wall bijection | `Ideal.wallSpin`, `Ideal.oddAlternating_iff_existsUnique_sign` | [Ideal/Walls.lean](Ideal/Walls.lean) |
| Equation (2) | `Ideal.thetaOf`, `Ideal.psi_clock_eq` | [Ideal/Theta.lean](Ideal/Theta.lean) |
| §1.5, actual attained first minimum | `Ideal.lambdaInf`, `Ideal.lambdaInf_generator`, `Ideal.generator_ne_zero` | [Ideal/Minimum.lean](Ideal/Minimum.lean) |
| Equation (3), f and positive radius | `Ideal.constructedF`, `Ideal.lambdaInf_constructedF`, `Ideal.constructedF_ne_zero`, `Ideal.radius_eq`, `Ideal.radius_pos` | [Ideal/Construction.lean](Ideal/Construction.lean) |
| Equations (1)–(3), threshold and additive gap | `Ideal.idealYes_constructedF_iff`, `Ideal.no_gap`, `Ideal.no_gap_vector`, `Ideal.outputInput_mem_iff` | [Ideal/Construction.lean](Ideal/Construction.lean) |
| §1.1, total encoded graph normalization | `Runtime.normalGraph`, `Runtime.normalised_clique_iff`, `Runtime.smallAnswer_correct_of_not_mainCase` | [Runtime/Graph.lean](Runtime/Graph.lean) |
| §1.5, executable lists and total source map | `Runtime.guardCoeff`, `Runtime.generatorCoeffs`, `Runtime.construction`, `Runtime.reduceList` | [Runtime/Construction.lean](Runtime/Construction.lean) |
| §1.5, literal dimension and degenerate cases | `Runtime.degree_le_vertexCount`, `Runtime.reduceList_length`, `Runtime.reduceList_dyadic`, `Runtime.reduceList_correct_of_not_mainCase` | [Runtime/Structure.lean](Runtime/Structure.lean) |
| §1.5, polynomial bit time | `Runtime.reduceList_polytime` | [Runtime/PolyTime.lean](Runtime/PolyTime.lean) |
| Equation (1), normalized graph/differences | `Glue.differenceSet_eq_edgeDifferences`, `Glue.clique_iff_positions_exact`, `Glue.spinDistances_valid`, `Glue.positiveDifferences_iff` | [Glue/Source.lean](Glue/Source.lean), [Glue/Distances.lean](Glue/Distances.lean) |
| Equations (1)–(2), equivalent spin objectives | `Glue.oddAlternating_iff`, `Glue.thetaOf_eq_Theta` | [Glue/Theta.lean](Glue/Theta.lean) |
| Equations (1)–(3), runtime parameter/list identities | `Glue.degree_eq_spin`, `Glue.guardCoeff_eq`, `Glue.runtimeTau_eq`, `Glue.runtimeG_eq_toList` | [Glue/Spin.lean](Glue/Spin.lean) |
| Equation (3), executable ideal bridge | `Glue.reduceList_correct_of_eq1` | [Glue/Ideal.lean](Glue/Ideal.lean) |
| Equation (1), discharged bridge; total correctness | `Glue.runtime_eq1`, `reduceList_correct` | [Glue/Correctness.lean](Glue/Correctness.lean) |
| Theorem 1, polynomial verifier | `idealVerifier`, `idealVerifier_correct`, `idealVerifier_polytime`, `Membership.idealBoundInput_polytime` | [Membership/Verifier.lean](Membership/Verifier.lean), [Membership/PolyTime.lean](Membership/PolyTime.lean) |
| Theorem 1, polynomial certificate size | `Membership.ideal_certificate_bound`, `Membership.ideal_certificate_length` | [Membership/Certificates.lean](Membership/Certificates.lean) |
| Theorem 1, NP membership | `idealSVP_mem_NP` | [Membership/NP.lean](Membership/NP.lean) |
| Theorem 1, reduction and NP-completeness | `clique_polyTimeReducible_idealSVP`, `idealSVP_npHard`, `idealSVP_npComplete` | [Main.lean](Main.lean) |

## Interfaces and proof conventions

The source proof uses `Fin v` vertices and integer labels
`i + (3v³+1)i² + (3v³+1)²i³`, with `i = vertex.val + 1`.
Three-term uniqueness permits repetitions. Ordered nonzero differences are unique.
`difference_clique_extraction` works already for sets of size at least two;
`clique_iff_positions` assumes target at least two. The total runtime map selects
the paper gadget only at targets at least three.

`Spin.DValid D A0` means every distance is positive and at most `A0`.
`Spin.PositiveDifferences D P` uses natural distances `(y-x).toNat`;
`Source.PositiveDifferences P D` uses integer distances. `Glue.positiveDifferences_iff`
proves compatibility. The window is `{16d−1, 16d, 16d+1, 16d+2}` at each positive
source distance, together with the near distances one and two. Negative windows
are reflections, not additional windows at negative centers.

`Spin.OddAlternating` uses ternary coefficients, odd support size, and sign parity
of support rank. `Ideal.OddAlternating` uses a total sum `η = ±1` with every prefix
sum equal to zero or `η`. Their equivalence retains both initial signs. Integer
lifts use Euclidean quotient and remainder, so negative indices carry the correct
negacyclic sign. The generic ideal bridge assumes positive degree; the source
spin gadget additionally uses its explicit dyadic degree. Degree-zero defaults in
total objective definitions are never used in these theorems.

`Ideal.lambdaInf` is the infimum of norms of actual nonzero ideal products, not a
quantity defined using the desired sign-layer formula. The proof attains that
minimum on a full sign image and excludes all other parity-ideal layers by
coercivity. For any integer coefficient array `G` and nonnegative threshold `τ`,
`Ideal.lambdaInf_constructedF` gives exactly

```text
λ₁,∞(f R_n) = M + B − 2 Θ(G),
H = G(1−X), B = ‖H‖₁ + 2τ + 1, K = BX + H,
M = 3‖K‖₁ + 1, f = (M−K)S, r = M+B−2τ = M+‖H‖₁+1.
```

No source promise or hypothesis `τ ≤ Θ(G)` is required for this identity.
`Ideal.no_gap` proves `r + 2 ≤ λ₁,∞` when `Θ(G) < τ`.
`Glue.runtime_eq1` discharges the historical `hEq1` interface of
`Glue.reduceList_correct_of_eq1`; the headline theorem has no such hypothesis.
Canonical coefficient-list equalities transport objectives without dependent casts.

The guard correction and the exact bound
`Runtime.degree x ≤ 5376 * Runtime.vertexCount x.1 ^ 9 + 66`
are documented in [README.md](README.md). The degree is unary and polynomial in
the number of distinct declared vertices. Guard powers and all scale arithmetic
are binary, with polynomial encoding length. This establishes actual TM time,
rather than only counting arithmetic operations.

## Reuse and tidy decisions

`IdealCVP` supplies negacyclic list/coefficient arithmetic, quotient-ring
nonsingularity and Cramer certificate bounds. `Power2ModuleSVP` supplies `Coeff`,
`Dyadic`, `coeffSup`, signs and parity-block algebra. Membership imports the
shared radius scan from `Power2ModuleSVPSubsetSum.Membership.Radius`, and uses
`mem_NP_of_witness` with signed-binary list decoding. The witness is an integral
multiplier list: the verifier checks its nonzero bounded product. The paper's
alternative rational-linear-algebra verifier need not be implemented separately.

The two local algebra files were compared with `Power2ModuleSVP` and
`Power2ModuleSVPSubsetSum/Algebra`. Their norm estimates overlap mathematically,
but paper A's `coeffL1` is natural-valued, while both local APIs use integer
absolute sums. The local signed integer powers, Euclidean antiperiodic lift,
balanced-digit/orbit arguments, and scalar-domination lemmas are not verbatim
copies of those libraries. Replacing the files by imports would require API and
cast bridges, so they are retained. No shared package or other subproject was edited.

A whole-repository Lean search preceded dead-code review. Every private helper
is referenced; exported mathematical corollaries are retained as API rather than
removed solely for having no internal caller. All main declarations already had
docstrings; the remaining elementary public simp helpers now have them too.
Module documentation follows imports, as required by Lean, and has a `Paper:` line.
Removed 13 redundant direct imports; retained the direct graph import required by
Lean’s module visibility rules. The remaining warnings concern legacy imports of dependencies;
a project-wide module-system migration is outside this conservative tidy.

This document and [specs/STATUS.md](specs/STATUS.md) consolidate the completed
`hp2n-bsrc`, `hp2n-bspin`, `hp2n-bglue`, `hp2n-brun`, `hp2n-mem`, and
`hp2n-bfinal` reports. Their former cross-job integration boundaries are all closed.
The historical audit is retained verbatim; its original external artifact links
and prospective obligations describe the audit-time state, not outstanding work.
Paper §1.6's finite-`p` obstruction remains outside the formalised scope.
