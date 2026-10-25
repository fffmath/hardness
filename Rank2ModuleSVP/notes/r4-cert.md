# Round 4 — certificate bound

This is a retained round note. See [the current paper-to-Lean map](../NOTES.md)
for the final interfaces; unused intermediate corollaries were removed during cleanup.

Assigned file: `Rank2ModuleSVP/MembershipCert.lean`. All earlier round sources
and other jobs' files are unchanged. Imports `Membership` and
`IdealCVP.IntegerPreimage`; no `Rank2ModuleSVP.Reduction*` or `Clearing*` imports.

## Paper → Lean

Names below are in `Rank2ModuleSVP.Membership`, except the final theorem.

| Paper label / statement | Lean declaration |
| --- | --- |
| Multiplication matrix in the power basis (`eq:hadamard-norm-r` discussion) | `powerMatrix`, `powerMatrix_mulVec` |
| Expanded generator matrix `C_M` (`eq:standard-Euclidean-basis-exact`) | `certificateMatrix`, `certificateMatrix_mulVec` |
| Matrix entry bound by twice the maximum generator coefficient | `powerMatrix_entry_bound`, `certificateMatrix_entry_bound` |
| `lem:cyclotomic-form`, short vector coordinate bound for the NP argument | `product_coordinate_bound` |
| Polynomial magnitude bits for the two multiplier lists (pre.tex NP paragraph) | `certificateBitsPolynomial`, `bounded_certificate` |
| `thm:main-intro`, unconditional NP membership half | `Rank2ModuleSVP.moduleSVP_mem_NP` |

## Argument

This follows all four steps of `r3-membership.md`'s open obligation. Each block
of the integral `2(q-1)` by `2(q-1)` matrix is multiplication by one stored ring
coordinate. An entry is the difference of two cyclically selected generator
coefficients, after eliminating the omitted final coefficient. The matrix's
multiplication agrees exactly with the existing executable `Membership.product`.

For input length `N`, generator coefficients and the threshold have absolute
value at most `2^N`. The matrix entries are at most `2^(N+1)`, and both dimensions
are at most that bound because the encoding pays for unary `q`. The existing
`powerCoeffs_abs_le_norm` bounds each coordinate of an accepted short vector by
its component norm, hence by the threshold and `2^N`.

Apply `IdealCVP.exists_integer_preimage_bits` with `L = N+1` to that short
vector and its existing multiplier preimage. The theorem needs no rank promise.
Recover two length-`q-1` lists from the new preimage; matrix equality preserves
the exact product lists, so the existing verifier accepts them. Their magnitude
bit sizes are bounded by the explicit cubic polynomial

```
B(N) = (N+1) * (16*(2*N+1)^2) + 1
     = 64*N^3 + 128*N^2 + 80*N + 17.
```

This discharges the entire premise of
`moduleSVP_mem_NP_of_resource_bounds`. No named hypotheses, complex embeddings,
or extra algebraic assumptions are used. No mathematical obligation remains
in the assigned membership scope.

## Validation

- The complete source passed `lake env lean` (exit code 0;
  `/tmp/r4-cert-check5.log`).
- The final targeted build passed (exit code 0, 7065 jobs):
  `LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 2400 lake build Rank2ModuleSVP.MembershipCert`.
  Log: `/tmp/r4-cert-build.log`.
- The compiled-module audit passed (exit code 0):
  `LAKE_CACHE_DIR=/tmp/hardness-lake-cache lake env lean /tmp/r4-cert-axioms.lean`.
  It runs `#print axioms` on all 13 new public theorems, including
  `bounded_certificate` and `moduleSVP_mem_NP`. A scripted check confirms
  every dependency is in `{propext, Classical.choice, Quot.sound}`.
  Log: `/tmp/r4-cert-axioms.log`.
- The final source scan found no `sorry`, axiom declaration, or `native_decide`.
  No named analytic hypothesis is used; no obligation remains in this job.
