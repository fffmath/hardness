# hp2n-arun — complete

The existing reduction is certified directly, without an executable twin or changes
to any mathematical definitions. All degree/loop counters use unary encodings;
weights, coefficients, and scales use binary encodings.

## Files

- `Runtime/Primitives.lean`: unary degree selection, exact binary list l1 norms,
  scalar multiplication, constants, D/DStar/K filters, Boolean masks, Laurent weights.
- `Runtime/Reduction.lean`: certificates for every gadget field, both output columns,
  zero removal, empty-list dispatch, and the total `reduce` map.
- `Main.lean`: the polynomial reduction, NP-hardness, and NP-completeness endpoints.

The base-five filter uses `intBin_pow`, including its library proof of intermediate
bit growth with unary exponents. Negacyclic products reuse `poly_negacyclicMul`.
The scales use the actual list l1 norms; no upper-bound replacement is made.
Private field equations and local irreducibility avoid expanding the complete
record while composing certificates. No heartbeat limit increases are needed.

## Main declarations

All four are in namespace `Power2ModuleSVPSubsetSum`:

```lean
reduce_polytime : ComputableTidilyInPolyTime reduce
  (encPair (encList encNat) encNat) encSVP

subsetSum_polyTimeReducible_moduleSVP :
  PolyTimeReducible (encPair (encList encNat) encNat) encSVP
    Cslib.Complexity.SubsetSum ModuleSVPLang

moduleSVP_npHard : NPHard encSVP ModuleSVPLang

moduleSVP_npComplete : NPComplete encSVP ModuleSVPLang
```

Hardness uses exactly `Cslib.Complexity.SubsetSum_npHard.trans
subsetSum_polyTimeReducible_moduleSVP`. Completeness pairs it with the existing
`moduleSVP_mem_NP` from `Membership/NP.lean`.

## Verification

Commands, all exit 0:

```sh
LAKE_CACHE_DIR=/tmp/hardness-lake-cache /workspace/shared/bin/lake-locked build \
  Power2ModuleSVPSubsetSum.Runtime.Primitives
LAKE_CACHE_DIR=/tmp/hardness-lake-cache /workspace/shared/bin/lake-locked build \
  Power2ModuleSVPSubsetSum.Runtime.Reduction
LAKE_CACHE_DIR=/tmp/hardness-lake-cache /workspace/shared/bin/lake-locked build \
  Power2ModuleSVPSubsetSum.Main
LAKE_CACHE_DIR=/tmp/hardness-lake-cache /workspace/shared/bin/lake-locked env lean \
  /tmp/hp2n-arun-check.lean
```

The final Main build completed successfully (7113 jobs). No warnings in the new
modules; pre-existing dependency module-system warnings remain. Scratch examples
check all four exact signatures. Axiom inspection reports only `propext`,
`Classical.choice`, and `Quot.sound` for each of the four endpoints.

New-file module-doc/Paper-reference, 100-character-line, forbidden-proof-token,
and whitespace scans pass. No existing files, fixed interfaces, library roots,
lakefile, other subprojects, or dependency sources were edited. No commit attempted.

Logs: `/tmp/hp2n-primitives-build.log`, `/tmp/hp2n-runtime-build.log`,
`/tmp/hp2n-main-build.log`, `/tmp/hp2n-arun-check.log`.

Nothing remains open for this task.
