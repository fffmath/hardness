import Power2ModuleSVP.BooleanSourceReduction

/-!
# Boolean-source audit and integration notes (job p2s-sidon)

Only independently written Lean definitions/proofs and these short notes are
included; the private source documents are not redistributed.

## Scope checked

* `BooleanSource.fromThreeSAT` reuses complexitylib's proved clause padding.
  It compresses variable labels into an occurrence list and handles malformed
  exact-three inputs with a fixed contradictory two-row formula.
* The positive exactly-one selector gadget is proved in both directions, with
  pairwise distinct variables in every output triple and explicit fresh labels.
* `SparseEncoding.encode` returns finite exponent and signed offset data. The
  polynomial interpretation uses the one-based quadratic positions and the
  duplicated, reflected clause families from `prop:sidon-source`.
* `SparseEncoding.affine_correct` and `BooleanSource.threeSAT_affine_correct`
  prove both directions of the full quotient equation. The row interface
  `RowIsolation` is a proved intermediate result, not an extra hypothesis.
* `SparseEncoding.encoding_padding` proves `lem:sidon-padding` for the actual
  translation. `Sidon.no_common_root_reverse`, `Sidon.no_unit_circle_root`, and
  `Sidon.modulus_coprime_reverse` prove the algebraic part of
  `lem:sidon-reciprocal` using Mathlib's cyclotomic irreducibility.
* `SparseEncoding.weight_eq` gives the exact support count. The explicit size
  bound is `L ≤ 1125*r*v^2` in the nonempty positive-source regime; the total
  3SAT source has a cubic bound depending only on its clause count.

## Boundary conditions and paper audit

1. The strict odd-prime interval for the position parameter requires at least
   two variables. The selector gadget always supplies at least four. The total
   finite prime-search definition uses `max v 2` for smaller unrelated inputs.
2. The raw empty construction does not imply the dimension cutoff 64. The
   composed source does, as proved by `boolean_source_dimension`.
3. A uniform `O(r*v^2)` bound needs a nonzero clause count. The unconditional
   bound includes `4*r+1`; the composed gadget always has at least three rows.
4. No additional mathematical gap was found in the three local claims after
   checking support-family separation, repeated-index pair sums, positivity
   padding, prime parity, and the cyclotomic degree obstruction.

## Remaining integration work

The functions are explicit finite computations and their output sizes are
proved polynomial. A complexitylib multitape `ComputableTidilyInPolyTime`
certificate for normalization, finite prime search, and the complete data map
is not supplied here. Consequently this library does not yet assert a new
`PolyTimeReducible` or NP-hardness theorem for the affine language. Existing
`ThreeSAT_npComplete` / `ExactThreeSAT_npComplete` are imported, not reproved.
The global root imports, PLAN/STATUS, and final SVP composition belong to the
dispatcher and were not modified by this job.
-/
