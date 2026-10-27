# hp2n-brun — complete

Paper: `paper/power2-ideal-svp.pdf`, Sections 1.1 and 1.5; audit Section 3.

## Files and verified interfaces

- `Runtime/Graph.lean`: executable distinct-vertex normalization, zero-based normalized
  edges, `normalGraph : SimpleGraph (Fin v)`, and direct small-target decisions.
  `normalised_clique_iff` transports the exact source CLIQUE semantics for every input.
  `normalGraph_adj_iff` connects the Fin graph to the edge list;
  `smallAnswer_correct_of_not_mainCase` covers all omitted source cases.
- `Runtime/Construction.lean`: every intermediate paper parameter is a named list program;
  total `reduceList : Graph × ℕ → IdealInput`. Uses the original negacyclic list product
  for H and f. The antipodal guard coordinate receives both summands. Includes exact
  difference/window/forbidden-distance specifications and Coeff-level product bridges.
- `Runtime/PolyTime.lean`: native TM certificates for every computational intermediate and
  unconditional `reduceList_polytime : ComputableTidilyInPolyTime reduceList
  (encPair encGraph encNat) encIdeal`. Unary polynomial counters, binary integer powers
  via the certified power primitive, and binary scalar/norm arithmetic. Also polynomial
  bounds on unary dimension and final encoded output length.
- `Runtime/Structure.lean`: least-power dimension property, exact array lengths, positive
  main radius, fixed YES/NO properties, and degenerate-branch reduction correctness.
  Bounds: `maxLabel x ≤ 21*v^9`, `degree x ≤ 5376*v^9 + 66`.
  `reduceList_length` and `reduceList_dyadic` apply to every typed input.

## Validation

All builds used `LAKE_CACHE_DIR=/tmp/hardness-lake-cache` and
`/workspace/shared/bin/lake-locked`; no direct lake/lean invocation was used.

- Targeted Construction build passed: `/tmp/brun-construction.log`.
- Targeted PolyTime build passed: `/tmp/brun-polytime2.log`.
- Targeted Structure build passed (also checks Graph): `/tmp/brun-structure-build.log`.
- Combined `lake-locked env lean /tmp/BrunCheck.lean` passed:
  `/tmp/brun-final-check.log`. Checks exact main declarations and axioms; executable smoke
  cases cover repeated labels, loops, undeclared endpoints, reversed edges, targets zero,
  one and above v, a 100-bit label, negacyclic reflection, and the antipodal guard factor 2.
- Axiom inspection: only propext, Classical.choice, Quot.sound; total output length and
  dyadic proofs use propext alone. No proof holes or extra axioms. New modules have no
  warnings; build logs replay existing upstream module-system warnings.

## Integration boundary

No runtime obligations remain. The separate mathematics jobs must connect their Coeff
construction to these named executable intermediates and supply main-case IdealSVPLang
correctness. The runtime files do not assume those claims. Library roots, problem interfaces,
lakefile, other subprojects, and package sources were not edited. No commit was made.
