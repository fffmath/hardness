# Power2IdealSVP — final status

Paper: [power2-ideal-svp.pdf](../paper/power2-ideal-svp.pdf), Theorem 1.
Consolidated on 2026-10-28 from hp2n-bsrc, bspin, bglue, brun, mem, bfinal and bdocs.

The formalisation is complete: principal ideal coefficient infinity-norm SVP in
varying dyadic degree is unconditionally NP-complete. The total executable
CLIQUE reduction, its native polynomial-time certificate, and the NP verifier
have no remaining mathematical or runtime obligations. Headline statements and
fixed problem definitions are unchanged. Exact signatures are in
[../README.md](../README.md); the full paper map is in [../NOTES.md](../NOTES.md).

## Completed proof components

- **Source (bsrc):** no-carry base expansion, explicit Newton identities,
  three-term multiset uniqueness with repetitions, unique ordered differences,
  common-row/column extraction, and the converse positions construction.
  Extraction works for at least two positions; the total map uses the gadget
  at targets at least three. Labels satisfy `labelBound v ≤ 21*v^9` for `v ≥ 1`.
- **Sparse spins (bspin):** antiperiodic integer lifts, signed shifts, balanced
  base-five uniqueness, dyadic orbit exclusion (including the antipode), guard
  vanishing, active-neighbour and short-arc bounds, dimer/trimer run partition,
  unique trimer, exact component offsets, support cardinality, and converse
  construction. The actual negacyclic interaction table proves the exact
  threshold equivalence for arbitrary valid distance sets and positive targets.
- **Ideal bridge (bsrc):** integral norm estimates and scalar domination;
  `(1−X)S=2`, `XS=S−2`, the common-parity ideal characterization; the full-sign
  and odd alternating domain-wall bijection; attained finite objectives and
  equation (2). `lambdaInf` is the actual first minimum of nonzero products.
  Equation (3), generator nonzeroness, positive radius, the exact language
  threshold and the additive NO gap are proved without a source-YES promise.
- **Runtime (brun):** normalization of distinct declared vertices, symmetric
  simple adjacency, all small/impossible target decisions, explicit list
  programs for every parameter and coefficient array, dyadic degree and exact
  lengths, polynomial unary dimension, binary bit bounds, and native tidy
  multitape-TM certificates through `Runtime.reduceList_polytime`.
  Literal bound: `Runtime.degree x ≤ 5376 * Runtime.vertexCount x.1 ^ 9 + 66`.
- **Glue (bglue and bfinal):** exact source label/difference identities,
  well-formedness for every output, runtime/ideal identities for H, B, K, M, S,
  f and r, natural/integer distance compatibility, prefix/rank alternation
  equivalence, and equality of both sparse-spin objectives. Runtime/Spin
  parameter and canonical-list equalities prove `Glue.runtime_eq1`, discharging
  the former `hEq1` argument of `Glue.reduceList_correct_of_eq1`.
  `reduceList_correct` is unconditional on every typed graph input.
- **Membership (mem):** dyadic/length/nonzero checks, integral multiplier-list
  product and binary-radius scan, exact verifier correctness, native TM time,
  nonsingularity/Cramer coefficient bounds, polynomial framed witness length,
  and `idealSVP_mem_NP` via `mem_NP_of_witness`.
- **Assembly (bfinal):** `clique_polyTimeReducible_idealSVP`, `idealSVP_npHard`
  and `idealSVP_npComplete` compose the certified map with complexitylib's
  `Clique_npHard` and the proved membership theorem.

## Documentation and tidy (bdocs)

Added README, NOTES, this status and a short completed PLAN. The six former job
reports and temporary bdocs progress note are merged here and into NOTES and
removed. AUDIT.md is retained unchanged as historical evidence. All private
helpers were checked for references across the repository; none was clearly
dead. Exported corollaries remain mathematical API. Local algebra is retained
because the related external norm APIs are not verbatim replacements (notably,
paper A uses natural one-norms and these local estimates use integer one-norms).

Added documentation to the remaining elementary public helpers and removed
13 redundant direct imports, verified by rebuilding through retained imports.
All project Lean lines are at most 100 characters, all modules have a module
docstring with a `Paper:` line after imports, and public definitions/theorems
have docstrings. No proof bodies, mathematical definitions or headline
statements changed. No edits outside Power2IdealSVP/ were needed.

The antipodal guard coefficient is `2·5^j`, with magnitude bound
`2·5^(s−1)`; this corrects the literal paper bound and adds at most one bit.
Both guard implementations already have this coefficient. Small/impossible
source cases dispatch to degree-one radius-one/radius-zero constants. The
`r+2` gap belongs to the main construction, not the radius-zero constant NO.
Paper §1.6 (finite-`p` obstruction) is outside the formalised scope.

## Verification

The pre-tidy full locked build passed (7180 jobs), recorded in
`/tmp/hp2n-bdocs-build.log`. Earlier component and final integration audits
also reported only `propext`, `Classical.choice`, and `Quot.sound`.

Post-tidy full build **PASSED** (7180 jobs); headline-signature and axiom checks
**PASSED**, using:

```sh
LAKE_CACHE_DIR=/tmp/hardness-lake-cache /workspace/shared/bin/lake-locked build Power2IdealSVP
LAKE_CACHE_DIR=/tmp/hardness-lake-cache /workspace/shared/bin/lake-locked env lean /tmp/hp2n-bdocs-axioms.lean
```

Build log: `/tmp/hp2n-bdocs-build-final.log`.
Axiom/signature script: `/tmp/hp2n-bdocs-axioms.lean`;
log: `/tmp/hp2n-bdocs-axioms.log`.
The script checks the five headline signatures, the literal degree bound and
axioms of completeness, total correctness, and NP membership. All three depend
on exactly `[propext, Classical.choice, Quot.sound]`.

`git diff --check`, documentation-link checks, the 100-character Lean line scan,
module/public docstring checks, and the forbidden-proof-token scan all pass.
Comparing Lean source with HEAD after stripping imports/comments/whitespace
confirms that all proof bodies, statements, and definitions are unchanged.
All changed and added files are inside Power2IdealSVP/.

Remaining module-system import warnings come from legacy imports of Mathlib
and other module-system dependencies; a module-system migration is outside
this tidy. No proof or unused-variable/simp warnings required suppression.
All build and Lean invocations in this job use the machine-wide lock wrapper.
No package files were modified and no commits were attempted.

## File inventory

Added: `README.md`, `NOTES.md`, `specs/PLAN.md`, `specs/STATUS.md`.

Lean documentation/import tidy:

- `Algebra/IdealBasic.lean`, `Algebra/SpinBasic.lean`
- `Ideal/Parity.lean`, `Ideal/Theta.lean`
- `Runtime/Construction.lean`, `Runtime/Graph.lean`, `Runtime/PolyTime.lean`
- `Source/Labels.lean`, `Source/RowColumn.lean`, `Source/ThreeTerm.lean`
- `Spin/Defs.lean`, `Spin/Parameters.lean`, `Spin/Runs.lean`, `Spin/Shifts.lean`,
  `Spin/ShortArc.lean`

Removed after consolidation: `specs/STATUS-hp2n-bsrc.md`,
`specs/STATUS-hp2n-bspin.md`, `specs/STATUS-hp2n-bglue.md`,
`specs/STATUS-hp2n-brun.md`, `specs/STATUS-hp2n-mem.md`,
`specs/STATUS-hp2n-bfinal.md`. The temporary bdocs progress note was also merged.
`specs/AUDIT.md`, `Problem.lean`, `Main.lean` and the library root are unchanged.

No open obligations within the requested scope.
