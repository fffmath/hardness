# r5-checker — paper v2 §4

This is a retained round note. See [the current paper-to-Lean map](../NOTES.md)
for the final interfaces; unused intermediate corollaries were removed during cleanup.

Status: DONE for all assigned checker tasks. No open proof obligations in the assigned scope.

All names below are in `Rank2ModuleSVP.Checker`, exported by `Rank2ModuleSVP.Checker`.

| Paper v2 label | Lean name(s) | Status |
| --- | --- | --- |
| §4.1, Equation (15): offsets | `tau`, `beta`, `offsetInt`, `d` | Preserved |
| Lemma 4.1 | `row_shift_bad_separation` (with `bad_card_bound`) | Done / preserved |
| §4.2: integral g, V, Q, U | `g I s`, `V I s`, `Q I h`, `U I s h` | Done |
| Rational images | `gQ`, `VQ`, `UQ`; `gQ_eq_p`, `VQ_eq`, `UQ_eq` | Done |
| g is self-conjugate | `p_conjugate` (rationalized checker) | Done |
| Lemma 4.2: exact U identity and lower bound for arbitrary y in K | `positiveChecker_norm_exact`, `checker_U_norm_lower` | Done |
| Lemma 4.2: monomial bounds for arbitrary w in K | `checker_g_norm_bound`, `checker_V_norm_bound` | Done |
| Lemma 4.2: integral U and V corollaries | `checker_U_norm_lower_int`, `checker_V_norm_bound` | Done |
| Equations (17)–(18): κ, R(x), B₀ | `kappa I (q := q) h`, `remainder I s h x`, `B₀ I (q := q) h` | Done |
| Equation (19): E(x) and nonnegativity | `E`, `E_nonneg`, `E_nonneg_binary` | Preserved |
| Theorem 4.3: exact normalized score | `checker_score` | Done |
| Theorem 4.3: 0 ≤ R(x) < κ/8 | `remainder_nonneg`, `remainder_lt` | Done |
| Theorem 4.3: bundled score, E ≥ 0 and remainder bounds | `checker_score_bounds` | Done |
| Theorem 4.3 applied directly to the integral checker value | `checker_score_int` | Done |
| Equation (20): admissibility and vanishing E | `Clean`, `Admissible`, `E_eq_zero_of_clean` | Done / preserved |
| Equation (21): lower bound for every binary weight-h vector | `checker_lower` | Done |
| Equation (21): upper bound conditional on admissibility | `checker_upper_of_clean` | Done |
| §5 threshold integrality: Q²B₀ ∈ ℤ | `baselineNumerator`, `baseline_scale_eq` | Done |
| §5 threshold integrality: Q²κ = 2qQ | `kappa_scale_eq` | Done |
| §5: S = Q²(B₀ + F + κ) ∈ ℤ for every integral F | `thresholdNumerator`, `threshold_integral` | Done |

## Hypotheses and model

- All new algebraic and norm statements require only `q : ℕ` and `[NeZero q]`. They are stronger than the requested odd-prime specialization; no primality or modulo-four restriction is needed.
- The X3C instance is the existing `IdealCVP.X3CInstance`; witness positions are `IdealCVP.SidonPositions I.n`. In this representation the paper's M is `3*I.q`, and `W I = 3*I.n`. The existing positive n assumption gives `W_ge_three`.
- `checker_score`, `remainder_lt`, `checker_lower`, `checker_upper_of_clean`, `checker_score_bounds` require binary `x : Coeff ℚ q`, coefficient sum h, and `1 ≤ h`. The upper bound additionally requires `Clean I s x`. `checker_score_int` has the corresponding integral binary and weight assumptions.
- The multiplier bounds apply to every rational quotient element, including arbitrary elements used in Lemma 5.1; no integrality or sparse representative is assumed. The U lower bound does not require h > 0.
- Lemma 4.1 retains the exact separation premise `4*tau I s*(3*I.q) < q`. The score identities and multiplier estimates themselves do not need separation.
- Threshold integrality requires `1 ≤ h` and an arbitrary integer F.
- No `WanPowerSumEstimates` or other named external hypothesis is used. No asymptotic largeness premise or job-specific asymptotic constants are needed in this algebraic section.

`CheckerAux` proves adjointness and weighted triangle estimates directly from the coefficient canonical form. Monomial isometries are the existing coefficient-model lemmas in `PrimeCyclotomic`. The strict remainder bound uses the squared triangle estimate `(3/2)‖a‖² + 3‖b‖²`, the two g multiplier bounds, and `W ≥ 3`, `h ≥ 1`.

`p` is retained as the rational image of v2 g, preserving the reusable quadratic/correlation API. The dead v1 D, old baseline, Gauss-sum multiplier, inverse denominator construction, and all modulo-four assumptions were removed from the owned checker files. `GaussSum.lean` is now a `PrimeCyclotomic` compatibility-import stub, and the checker does not import it.

Theorem 4.4's existence/counting argument is outside this job; the requested Equation (21) packaging is proved conditional on admissibility.

## Verification

- Passed `LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 2400 lake build Rank2ModuleSVP.Checker Rank2ModuleSVP.GaussSum`; this also builds `CheckerAux`.
- Passed direct iteration with `lake env lean Rank2ModuleSVP/Checker.lean`.
- Audited every public theorem in both checker modules (102 declarations) with `#print axioms`, using `/tmp/r5-checker-axioms.lean`. Every result uses only `propext`, `Classical.choice`, and `Quot.sound`. Output: `/tmp/r5-checker-axioms.log`.
- No `sorry`, `axiom`, `native_decide`, forbidden imports, or modulo-four conditions in the owned Lean files.
