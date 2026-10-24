# r6-map — paper v2 §5.3 and §5.4

All new map declarations are in `Rank2ModuleSVP.ReductionMap`. Only
`Problem.lean`, `MembershipAux.lean`, `ReductionMapAux.lean`, `ReductionMap.lean`,
and this note were edited. No `Reduction*` module is imported by the map.

## Paper-to-Lean correspondence

| Paper v2 item | Lean declaration | Status / hypotheses |
|---|---|---|
| Theorem 1.1: every odd prime | `SVPInput.WellFormed`, `Membership.wellFormedCheck_eq` | Done: primality and `q ≠ 2`, with unchanged lengths, determinant and threshold conditions. |
| §5.4 NP membership | `Rank2ModuleSVP.moduleSVP_mem_NP` | Done, unconditional; existing certificate-size proof rebuilds for the larger language. |
| §5.3 fixed module has squared minimum 8 | `eisenstein_norm_ge_two`, `fixed_minimum`, `fixed_minimum_attained` | Done directly in the quotient coefficient model. |
| §5.3 fixed YES / NO | `fixedYes_mem`, `fixedNo_not_mem`, `fixed_outputs_wellFormed` | Done; `q = 3`, lists `[2,0]`, `[0,0]`, thresholds 8 and 1. |
| Malformed / empty-universe / zero-row preprocessing | `reductionMap_malformed_correct`, `reductionMap_empty_correct`, `reductionMap_zeroRow_correct` | Done, on the indicated branches. Empty-universe handling runs after malformed-input rejection. |
| Nondegenerate incidence coverage, `M ≤ 3n` | `mapInstance_cover`, `mapM_le_n` | Done; the input universe has `3*x.1` elements, and the stronger `x.1 ≤ n` is proved. |
| §5.3 `k = max(K0,(n+2)^2)` | `mapK`, `mapK_bounds` | Done for arbitrary natural `K0`. |
| Bertrand prime scan | `primeScan_exists`, `primeScan_prime`, `primeScan_interval`, `primeScan_le` | Done. Scans the increasing `Y+1` integers in `[Y,2Y]`, testing odd primality by trial division. Interval/minimality need `2 ≤ Y`; fallback 3 makes it total at `Y=0,1`. |
| Dyadic order bound | `mapQ_spec`, `reductionMap_q_le`, `reductionMap_dimension_bound` | Done for all `K0`, `1 ≤ C0`. The last result uses the explicit `dimensionPolynomial K0 C0`. |
| Cyclic-to-power-basis conversion | `atom`, `singleList_eq_atom`, `powerElement_atom`, `powerElement_scalar` | Done; subtracts the coefficient at `q-1`. |
| Generator computations | `gList`, `vList`, `uList`, `piList`, `centerList`, `coreInput`, `reductionMap` | Executable definitions. Cubic Sidon positions, indexed incidences, integral checker, no Gauss sum or denominator clearing. |
| §5.3 first generator | `reductionMap_m₁` | Done: `powerPair` of the actual output lists is `(Checker.U * pi^k, 0)`. |
| §5.3 second generator | `reductionMap_m₂` | Done: `(Checker.U * sepCenter k - Checker.V, -(Checker.Q * mapGamma k))`. |
| Equation (23) threshold | `reductionMap_S`, `reductionMap_S_formula` | Done: exact `Checker.thresholdNumerator` and its rational `Q²(B₀+F+κ)` identity. `mapGamma k = Nat.sqrt (9*k/10)`, `F = Γ²(q-1)`. |
| Power-basis coordinate lengths | `coreInput_lengths`, `reductionMap_lengths` | Done for every nonzero order. |
| Arithmetic coefficient growth | `cyclicCoeff_abs_bound`, `mul_abs_bound`, `atom_abs_bound`, `ringPow_abs_bound` | Done. Multiplication bounds each coefficient by `2qAB`; powers by `2(2q(A+1))^n`. These are magnitude bounds, not machine certificates. |
| Prime-scan polynomial time | `poly_primeCandidates`, `poly_oddPrimeCheck`, `poly_primeScan` | Done in `ComputableTidilyInPolyTime`, unary input and output. |
| Parameter computation polynomial time | `poly_mapK`, `poly_mapY`, `poly_mapQ`, `poly_hasZeroRow` | Done for each fixed `K0 C0`; `encX3C` is the source encoding. |
| List sums / cyclic single coefficients | `poly_sumLists`, `poly_singleList` | Done, unary dimension and indices, binary integer coefficients. |
| Integer square root / Γ / Q / S polynomial time | `sqrtScan_eq`, `poly_nat_sqrt`, `poly_mapGamma`, `poly_qScale`, `poly_threshold` | Done. The square-root certificate uses an explicit bounded unary counting scan. |

## Remaining work

The full theorem

```lean
ComputableTidilyInPolyTime (reductionMap K0 C0) IdealCVP.encX3C encSVP
```

is **not proved**. Specifically:

1. Compile `ringPow` for variable unary exponent/dimension, using its proved
   coefficient growth bound to supply the polynomial intermediate encoding-length
   bound required by complexitylib iteration.
2. Express the proof-dependent finite loops in `gList`/`vList` on `toInstance`
   as ordinary `List.range`/`getD` loops on `X3CList`, and apply the proved
   `poly_singleList`, `poly_sumLists`, and membership list arithmetic certificates.
   Natural offsets have polynomial size after zero-row preprocessing; signed
   offsets can be implemented using residues. Prove the equality to the existing
   executable core constructor.
3. Compose the generator certificates, threshold certificate, parameter scan,
   and preprocessing to obtain the full map certificate.

Consequently no `PolyTimeReducible` or NP-hardness result is asserted here.
Final semantic YES–NO correctness for the nondegenerate branch and nonzero
output determinant/threshold can be supplied by the separate reduction job,
using `reductionMap_q`, `reductionMap_m₁`, `reductionMap_m₂`, and `reductionMap_S`.
The map requires no additional named hypothesis, and uses no Wan estimate.
Its dyadic bounds require `1 ≤ C0`; its semantic identities impose no
asymptotic cutoff. Later assembly can plug in the reduction job's explicit
constants for `K0 C0`.

## Validation

Passed:

- `LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 2400 lake build Rank2ModuleSVP.MembershipCert`.
- `LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 2400 lake build Rank2ModuleSVP.ReductionMap`.
- `/tmp/r6-map-axioms.lean`: `#print axioms` on all public theorems in
  both map modules, the changed verifier characterization, certificate and NP
  theorems, and the executable map itself (84 declarations total). Every axiom
  set is contained in `{propext, Classical.choice, Quot.sound}`.
- `/tmp/r6-map-eval.lean`: executable checks produce the fixed YES for `(0,[])`,
  fixed NO for malformed `(0,[(0,1,2)])`, fixed NO for zero-row `(1,[])`, and for
  `(1,[(0,1,2)])` with `K0=0,C0=1` produce order 19, four coordinate lists of
  length 18, and threshold 1410194582784.

There are no `sorry`, `axiom`, or `native_decide` declarations in the assigned
sources. Build warnings are lint/style warnings; all checks above succeed.
