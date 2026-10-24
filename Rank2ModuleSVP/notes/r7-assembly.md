# r7-assembly — paper v2 Theorem 1.1

Owned files: `Rank2ModuleSVP/Main.lean` and this note. No other repository
source was edited. `Main.lean` imports `Reduction`, `ReductionMap`, and
`MembershipCert`; it does **not** import `ReductionMapPoly`.

## Paper-to-Lean correspondence

All declarations below are in namespace `Rank2ModuleSVP`.

| Paper v2 item | Lean declaration | Status / hypotheses |
| --- | --- | --- |
| Absolute constants for §5.3 | `mainK0`, `mainC0`, `mainK0_ge_redK0`, `mainC0_ge_redC0`, `mainK0_pos`, `mainC0_pos` | Done. `mainK0 = max redK0 1 = 100000000`; `mainC0 = max redC0 8 = 1000`. Both are explicit naturals and at least one. |
| Cubic Sidon positions satisfy (16) | `main_cubic_offsets` | Done. For `1 ≤ k`, `I.n ≤ k`, `I.q ≤ I.n`, and `(2*k)^8 ≤ q`. No external estimate. |
| Equations (22)–(23) in the executable power-basis encoding | Private helpers `main_coreInput_m₁`, `main_coreInput_m₂`, `main_coreInput_S` | Done. Match `coreInput_m₁/m₂/S` with `redM1/redM2/redS`; `mapGamma` and `redGamma` have the same natural square-root definition. |
| Nondegenerate output promises in §5.4 | `main_coreInput_wellFormed` | Done. Odd prime, `redK0 ≤ k`, `(2*k)^redC0 ≤ q`, and `3*I.q ≤ Checker.W I`. Uses `redDet_ne_zero`, `redS_nonneg`, and the four proved coordinate lengths. Does not need Wan. |
| Theorem 5.2 in the actual encoded language | `main_coreInput_correct` | Done. Explicit `WanPowerSumEstimates` argument, the preceding promises, `I.n+2 ≤ Nat.sqrt k`, and (16). Instantiates `exact_X3C_encoding`. |
| Every total-map output satisfies the SVP promises | `reductionMap_wellFormed_of_constants`, `reductionMap_wellFormed` | Done, with no external estimate. The generic version permits arbitrary `K0 ≥ redK0`, `C0 ≥ redC0`, `C0 ≥ 1`. |
| Theorem 1.1, total YES–NO equivalence | `reductionMap_correct_of_constants`, `reductionMap_correct` | Done, with explicit `hWan : WanPowerSumEstimates`. Covers malformed inputs, the empty universe, zero rows, and the nondegenerate branch. Generic version allows `K0 ≥ redK0`, `C0 ≥ redC0`, `C0 ≥ 8`. |
| Theorem 1.1, NP-completeness | `moduleSVP_npComplete_of_polytime` | Done, conditional on explicit `hWan` and `hpoly : ComputableTidilyInPolyTime (ReductionMap.reductionMap mainK0 mainC0) IdealCVP.encX3C encSVP`. Composes `IdealCVP.x3c_npHard` with the map and uses `moduleSVP_mem_NP`. |

## Numerical and preprocessing bridges

For the cubic positions, `alphaStar ≤ 3*n^3+n`. From `n ≤ k` and `1 ≤ k`
the proof obtains `tau ≤ 9*k^3`, and absence of zero rows supplies
`I.q ≤ I.n ≤ k` via `mapM_le_n`. Thus

```text
4*tau*(3*I.q) ≤ 108*k^4 < 256*k^4 ≤ 256*k^8 = (2*k)^8 ≤ q.
```

`mapK_bounds` supplies `(n+2)^2 ≤ k`, hence both `n ≤ k` and
`n+2 ≤ Nat.sqrt k`. `mapQ_spec` supplies primality, exclusion of two, and the
prime-size lower bound. `red_regime_mono` transports the regime to `redK0` and
`redC0`. The generic correctness theorem makes later increases of the constants
possible without repeating the assembly.

For threshold nonnegativity, `mapInstance_cover` and
`Checker.rows_le_incidence_count` prove exactly `3*I.q ≤ Checker.W I`.
No unconditional nonnegativity premise is assumed. All three preprocessing
branches reuse their existing correctness theorems and fixed well-formed outputs.

## Integration and remaining scope

The requested conditional NP-completeness theorem is complete. The final
unconditional-in-time corollary can be added by the integrator after importing
the separate polynomial-time module and supplying
`ReductionMap.reductionMap_polytime mainK0 mainC0` as `hpoly`. That certificate
is not assumed to exist by this module, and this note does not claim the final
corollary already exists. `WanPowerSumEstimates` remains the sole external
mathematical estimate.

Corollary 1.2 is not formalized here. The current SVP development defines the
decision language, not a shortest-vector search relation with an encoded oracle
interface and a polynomial bound on oracle answer length. A faithful one-call
Turing reduction needs those definitions, the answer-size bound, and a timed
oracle program; the decision many-one theorem alone does not certify them.
Complexitylib has general oracle machinery, but no such rank-two SVP search
interface was established in these files. No substitute search-hardness claim
is asserted.

## Validation

- `LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 2400 lake env lean Rank2ModuleSVP/Main.lean`
  succeeded.
- `LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 2400 lake build Rank2ModuleSVP.Main`
  succeeded (7103 jobs; linter warnings only).
- A single scratch file `/tmp/r7-assembly-check.lean` checked the numerical
  values of both constants and ran `#print axioms` on all twelve public
  theorems in `Main.lean`. The check succeeded; every axiom set is a subset
  of `{propext, Classical.choice, Quot.sound}`. In particular both requested
  main theorems have exactly these three standard axioms and no others.
  The scratch file was removed after the audit.
- No `sorry`, `axiom`, or `native_decide` occurs in `Main.lean`.
