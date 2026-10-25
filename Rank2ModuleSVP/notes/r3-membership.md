# Round 3 — membership

This is a retained round note. See [the current paper-to-Lean map](../NOTES.md)
for the final interfaces; unused intermediate corollaries were removed during cleanup.

Assigned files: `MembershipAux.lean`, `Membership.lean`. The arithmetic API is in
`Rank2ModuleSVP.Membership`; the final resource-bound theorem is in
`Rank2ModuleSVP`. Only those files and this note are changed.

## Paper → Lean

| Paper statement | Lean declaration |
| --- | --- |
| Power basis `1,…,ζ^(q−2)`, `Φ_q=1+⋯+X^(q−1)` | `Membership.repr`, `powerCoeffs_repr`, `powerElement_repr`, `powerElement_surjective` |
| Cyclic convolution followed by elimination of the last coefficient | `Membership.cyclicCoeff`, `mul`, `cyclicCoeff_eq`, `powerCoeffs_mul`, `powerElement_mul` |
| Power-basis addition and subtraction | `Membership.powerElement_add`, `powerElement_sub` |
| `lem:cyclotomic-form`, executable norm | `Membership.norm_eq`, `pairNorm_eq` |
| Short-vector coefficient bound (pre.tex NP paragraph) | `Membership.powerCoeffs_abs_le_norm` |
| Input promises (intro.tex and final membership paragraph in reduction.tex) | `Membership.primeCheck_eq`, `det_eq`, `wellFormedCheck_eq` |
| Nonzero short module-vector certificate | `Membership.product_eq`, `verifier_spec`, `moduleSVP_iff_exists_check` |
| Polynomial-time arithmetic and trial-division verifier | `Membership.poly_mul`, `poly_norm`, `poly_primeCheck`, `poly_wellFormedCheck`, `poly_verifier` |
| `thm:main-intro`, NP half with the remaining resource obligation explicit | `Rank2ModuleSVP.moduleSVP_mem_NP_of_resource_bounds` |

## What is implemented

The arithmetic and checker are total executable list programs, including at
`q=0` and for malformed list lengths. The semantic bridges assume `NeZero q`
only when interpreting quotient elements; `wellFormedCheck_eq` obtains this
from the checked primality. The prime check is trial division over `range q`.
Its runtime proof uses the actual unary `q` encoding in `encSVP`.

Multiplication first computes cyclic convolution with a zero at index `q−1`,
then subtracts the convolution coefficient at `q−1` from every remaining
coefficient. The correctness theorem is in the round-1 quotient ring itself;
there is no field assumption or complex-embedding assumption. Nonzeroness is
checked by positivity of the exact product canonical norm. The determinant is
checked by nonvanishing of its exact canonical norm.

The runtime proofs use IdealCVP's list/integer arithmetic and complexitylib's
`ComputableTidilyInPolyTime` composition pipeline. The conditional NP theorem
uses IdealCVP's signed-integer list decoder and complexitylib's
`mem_NP_of_witness`. Its sole premise supplies a polynomial `B` bounding the
magnitude-bit size of coefficients of some accepted pair of multipliers for
every YES input. The theorem proves the encoding-length bound itself,
including list/pair framing, signs, and the unary dimension.

No named analytic hypothesis is introduced or used. In particular none of
`WanPowerSumEstimates`, `PrimesThreeModFourDyadic`, or
`BennettPeikertMinimum` occurs in this development.

## Open obligation

Unconditional `moduleSVP_mem_NP` is **not** claimed. The remaining obligation is
precisely to discharge `hcertificateBits` in
`moduleSVP_mem_NP_of_resource_bounds` for a concrete polynomial `B`:

1. Construct the `2(q−1)`-column integer matrix for multiplication by the two
   generators, using the proved list multiplication semantics.
2. Prove its evaluation agrees with `Membership.product`, and bound its entries
   by the generator encoding length.
3. Apply IdealCVP's `exists_integer_preimage_bits` (which also handles deficient
   rank), or an adjugate argument, to a short vector. The required bound on the
   short vector's power-basis coordinates is already
   `powerCoeffs_abs_le_norm`.
4. Transfer the small matrix preimage back to accepted multiplier lists and
   obtain a polynomial in `(encSVP x).length`.

There is no remaining verifier-correctness or primality-runtime premise in
the conditional theorem. No unproved proposition has been packaged as a
named hypothesis to hide the matrix/preimage gap.

## Validation

- `MembershipAux` passed its targeted module build (48 s).
- `LAKE_CACHE_DIR=/tmp/hardness-lake-cache lake env lean
  Rank2ModuleSVP/Membership.lean` passed (exit code 0); log:
  `/tmp/membership-main-check.log`.
- The final targeted build passed (exit code 0):
  `LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 2400 lake build
  Rank2ModuleSVP.Membership` (7043 jobs; main module 65 s). Log:
  `/tmp/membership-build3.log`.
- `/tmp/r3-membership-axioms.lean` imports the compiled main module and runs
  `#print axioms` on all 39 new theorems. The audit passed (exit code 0); all
  reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
  Log: `/tmp/r3-membership-axioms.log`.
- A source scan found no `sorry`, `axiom` declaration, or `native_decide` in
  either new Lean file. No named analytic hypothesis is used.

Outcome: steps 1–3 and the polynomial-time verifier in step 5 are complete;
the short-vector-coordinate part of step 4 and the conditional NP bridge are
also complete. The matrix/small-preimage certificate-bit argument in step 4
is the remaining reason unconditional `moduleSVP_mem_NP` is not yet stated.
