# r6-reduction — paper v2 §§4.3–5.2

Owned files: `Rank2ModuleSVP/Reduction.lean` and `Rank2ModuleSVP/ReductionAux.lean`.
All declarations below are in namespace `Rank2ModuleSVP`.

| Paper v2 label | Lean declarations | Status |
| --- | --- | --- |
| Common absolute constants | `redK0`, `redC0`, `red_regime`, `red_regime_mono` | Done; currently `100000000`, `1000`; both may be increased |
| Agreement of prescribed weights | `cntH_eq_sepWeight` | Done, definitionally `21*k/20` |
| Sidon positions modulo q | `red_alpha_injective`, `red_difference_injective`, `redPositions_card` | Done, for generic `IdealCVP.SidonPositions` under (16) |
| Forbidden offsets and pairs in (20) | `redOffsets_card`, `redOffsets_nonzero`, `red_admissible_representative` | Done; instantiates `admissible_representative` with `D_wit ∪ D_bad` and the actual forbidden pairs |
| Theorem 4.4 specialized to the checker | `red_admissible_representative` | Done, including arbitrary compatible syndrome and prescribed binary witness bits |
| Corollary 4.5, coset membership | `red_coset_representative` | Done, using `sepCenter_representative` and `ramified_coset_syndrome` |
| Corollary 4.5, (21) | `red_checker_bounds`, `red_corollary_4_5` | Done, including both inequalities and all representative properties |
| Generators in (22) | `redM1`, `redM2`, `red_moduleVector`, `red_moduleVector_norm`, `redCost` | Done; integral second coordinate is `-QΓw` |
| Nonzero determinant | `redDet_ne_zero` | Done, without assuming a domain structure on the coefficient quotient |
| Parameters (23) | `redGamma`, `redF`, `redNu`, `redS`, `redS_eq` | Done; `redS` is the explicit integer `thresholdNumerator` |
| Exact floor in (23) | `redGamma_real_floor` | Done: `Nat.sqrt (9*k/10) = floor(sqrt(9*k/10))` over the reals |
| Lemma 5.1 / (24) | `red_global_stability`, `red_global_stability_int`, `redNu_bounds` | Done over arbitrary rational cyclotomic elements and in the integral model |
| Γ² = 9k/10 + O(√k) | `redGamma_rounding`, `redGamma_bounds`, `redGamma_error` | Done with explicit errors |
| ν = O(k^(-3/2)), κ = O(q/k) | `redNu_decay`, `red_kappa_bounds` | Done: `ν*k*sqrt(k) ≤ 1/32`, `0 < κ ≤ q/(5000*k)` |
| Baseline error | `red_baseline_upper`, `red_baseline_lower`, `red_baseline_error` | Done; two-sided results assume `3*I.q ≤ Checker.W I` |
| H = (21/40)L + o(L) | `red_H_error` | Done: absolute error at most `q + 4*k²` |
| F = (18/40)L + o(L) | `red_F_error` | Done: absolute error at most `(2*sqrt(k)+1)*q + k` |
| S/Q² = (39/40)L + o(L) | `red_S_error`, `red_S_relative_error` | Done under the paper's row-count premise; relative error at most `2/sqrt(k)` |
| Positive/nonnegative threshold | `redS_nonneg`, `redS_pos_of_cover` | Done with the necessary premises described below |
| Theorem 5.2, completeness | `red_completeness` | Done with strict `< redS` |
| Theorem 5.2, roots of unity | `red_signed_isometry`, `red_signed_inverse`, `red_root_normalization`, `red_no_cover_error` | Done in the coefficient quotient model |
| Theorem 5.2, all four soundness cases | `red_soundness_cost`, `red_soundness` | Done with strict `redS < pairNormSq` for every nonzero module vector |
| Exact X3C encoding | `exact_X3C_encoding` | Done |

## Main interface and hypotheses

`exact_X3C_encoding I s hWan hk hpow hn hoff` states

```lean
I.HasExactCover ↔
  SVPYes (redM1 (q := q) I s k) (redM2 I s k) (redS (q := q) I k)
```

It uses `[NeZero q]`, `[Fact q.Prime]`, and exactly these numerical premises:

- `redK0 ≤ k`;
- `(2*k)^redC0 ≤ q`;
- `I.n + 2 ≤ Nat.sqrt k`;
- `4*Checker.tau I s*(3*I.q) < q`.

The only external named estimate is the explicit argument
`hWan : WanPowerSumEstimates`. Soundness and the determinant theorem do not
need Wan. No congruence condition modulo four is used. The numerical regime
already excludes two. The headline equivalence does **not** need the row-count
premise below. The definitions of `redS` and `redF` need an explicit `q` when
their arguments alone do not determine it.

## Necessary correction to the requested nonnegativity premise

The job's listed assumptions omit the paper's preprocessed-input condition
`M ≤ W`, i.e. `3*I.q ≤ Checker.W I`. The paper uses this condition explicitly
in its two-sided parameter estimates. `redS_nonneg` and the two-sided baseline
and threshold estimates take that elementary inequality as an explicit
premise. For inputs with no zero row it follows from
`Checker.rows_le_incidence_count`. `redS_pos_of_cover` instead obtains positivity
from completeness whenever there is an exact cover.

Unconditional nonnegativity under only the listed assumptions is false, so it
has not been asserted or left as a proof placeholder. For example, fix
`k = 100000000`, use one triple and the one-point Sidon positions `α = 0`, and
take `I.q = floor(q/24)` for a sufficiently large admissible prime `q`. Then
`τ = 1`, and (16) holds since `12*I.q < q`. With `h`, `Q`, and `Γ` fixed by k,
the threshold divided by `Q²` is

```text
q * (h + Γ² + (12h - 12*I.q + 2)/Q)
  - h² - Γ² + (12h - 72h²)/Q.
```

It is negative for sufficiently large q. The X3C instance has many zero rows.
The encoding equivalence remains valid for it; only the request for an
unconditionally nonnegative threshold and two-sided baseline asymptotics
needs the missing preprocessing premise. There are no incomplete Lean proofs.

## Validation

- `LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 2400 lake build Rank2ModuleSVP.Reduction`
  succeeded (7071 jobs; linter warnings only).
- `/tmp/r6-reduction-axioms.lean` runs `#print axioms` on all 56 public theorems
  in both owned modules. `lake env lean` succeeded; output is in
  `/tmp/r6-reduction-axioms.log`.
- Every audited theorem uses only a subset of `propext`, `Classical.choice`,
  and `Quot.sound`. In particular this holds for `exact_X3C_encoding`,
  `redDet_ne_zero`, `redS_nonneg`, `red_corollary_4_5`, `red_completeness`,
  `red_soundness`, and the quantitative parameter estimates.
- No `sorry`, `axiom`, or `native_decide` occurs in either owned Lean file.
- Only the two assigned Lean source files and this note were created/edited;
  verification scratch files are under `/tmp`.
