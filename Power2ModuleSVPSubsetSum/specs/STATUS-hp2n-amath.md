# hp2n-amath — complete

Implemented the requested mathematical correctness core of paper A. All required
correctness obligations are proved. The optional witness-bijection Corollary 4.3 is omitted.
TM runtime certificates and NP membership were deliberately left to their separate jobs.

## Entry points

Import `Power2ModuleSVPSubsetSum.Reduction.Correctness` for the total reduction and all
correctness/gap endpoints. Import `Power2ModuleSVPSubsetSum.Rigidity.Bounds` additionally
for the full Section 3 norm-bound API. The library root was not edited.

- `Power2ModuleSVPSubsetSum.reduce : List ℕ × ℕ → SVPInput` is an executable list program.
- `reduce_correct` proves equivalence with `Cslib.Complexity.SubsetSum` on every input.
- `reduce_wellFormed` proves every output has dyadic degree, exact-length arrays, and
  `listIndependent = true`, using the existing quotient/field determinant equivalence.
- `reduce_yes_gap` proves `FirstMinimum` equals the stored radius on YES inputs.
- `reduce_no_gap` bounds every nonzero output vector below by stored radius plus one on NO.
- `Reduction.gadget_no_minimum_bounds` proves the paper gadget has an attained NO minimum
  between `M+1` and `2M`. `UpperBound` supplies an explicit first-column vector of norm `2M`.

Exact signatures of the main algebra, rigidity, encoding and endpoint declarations are in
[API-hp2n-amath.md](API-hp2n-amath.md).

## Mathematical contents

- Generic coefficient l1 and maximum norms; convolution estimates; signed shift formula.
- Coefficient involution, adjointness, skew orthogonality, signed monomial units/inverses.
- Explicit D, S, K; opposite-pair identities; exact pair norm; vanishing coefficients;
  D*D=2; skew K; rho bound; balanced base-five support rigidity.
- Exact F, nu, rho, L, M, Q; complete multiplier rigidity; injectivity of Q+V.
- Position-indexed Boolean witnesses preserve multiplicities. Zero removal preserves the
  full multiset source language. Empty/all-zero lists use fixed degree-one identity
  YES/NO instances at radii one/zero according to whether the target is zero.
- List program for (4.1)–(4.3), exact parameter/model bridges, Boolean encoding,
  Laurent coefficient identities, exact norm M+2*natAbs(A-B), determinant validity,
  normalized short-vector classification, total correctness and exact gaps.

## Runtime handoff

The data path is `reduce` → `positiveWeights` → `Reduction.positiveReduce` →
`Reduction.gadget`. It contains no noncomputable definitions or proof fields.
`Gadget` is ordinary executable data. Loops traverse the input list or `List.range n`;
weights and the target enter binary arithmetic only. The degree is
`2 * 2 ^ Nat.clog 2 (max 2 weights.length)`. `rho` is computed by `listL1 DK`, not
replaced by its upper bound. Proof-only l1/adjoint/unit operations need no runtime certificates.

## Verification

Final command, exit 0:

```sh
LAKE_CACHE_DIR=/tmp/hardness-lake-cache lake build \
  Power2ModuleSVPSubsetSum.Reduction.Correctness \
  Power2ModuleSVPSubsetSum.Rigidity.Bounds
```

Build completed successfully (7093 jobs), covering all 25 new Lean modules.
No warnings in the new modules. Existing dependency module-system warnings remain.

Final `#print axioms` checks of `reduce_correct`, `reduce_wellFormed`, `reduce_yes_gap`,
`reduce_no_gap`, `multiplier_rigidity`, `gadget_exactNorm`, `gadget_no_minimum_bounds`,
and first-minimum existence report only `propext`, `Classical.choice`, `Quot.sound`.
Forbidden-token, module-doc/Paper-reference and 100-character-line scans pass.
Small executable checks return radii 1 and 0 for empty/all-zero branches and degree 4,
radius 27 for weights [1], target 1.

No fixed interfaces, library roots, lakefile, or other subprojects were edited.
No commit was attempted. All files are left in the requested worktree.

## New Lean files

- `Algebra/Adjoint.lean`
- `Algebra/Norms.lean`
- `Algebra/Units.lean`
- `Reduction/Boolean.lean`
- `Reduction/Bridge.lean`
- `Reduction/Constants.lean`
- `Reduction/Construction.lean`
- `Reduction/Correctness.lean`
- `Reduction/ExactNorm.lean`
- `Reduction/ExactVector.lean`
- `Reduction/Gap.lean`
- `Reduction/Map.lean`
- `Reduction/Model.lean`
- `Reduction/Soundness.lean`
- `Reduction/Source.lean`
- `Reduction/UnitAction.lean`
- `Reduction/UpperBound.lean`
- `Reduction/Validity.lean`
- `Reduction/WeightIdentity.lean`
- `Rigidity/Bounds.lean`
- `Rigidity/Filter.lean`
- `Rigidity/Multiplier.lean`
- `Rigidity/Parameters.lean`
- `Rigidity/Skew.lean`
- `Rigidity/Support.lean`
