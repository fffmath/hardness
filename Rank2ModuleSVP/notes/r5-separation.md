# r5-separation — paper v2 §3.3

This is a retained round note. See [the current paper-to-Lean map](../NOTES.md)
for the final interfaces; unused intermediate corollaries were removed during cleanup.

Owned source: `Rank2ModuleSVP/RobustCenter.lean`. No additional module is needed.

| Paper v2 label | Lean declarations | Status |
| --- | --- | --- |
| Lemma 3.5(i) | `sparse_tools_i_v2` | Done: both squared coefficient norm and support bounds, without a smallness assumption |
| Lemma 3.5(ii) | `second_shell` | Done: signed monomial with norm `q-1`, or norm at least `2q-4` |
| Lemma 3.6 | `sparse_tools_ii` | Done: wrapper for `SparsePolynomial.sparse_tools_ii` |
| Equation (11) | `robustCenter`, `sepWeight`, `sepCenter` | Done: `sepWeight k = 21*k/20`, `sepCenter k = sepWeight k + pi^(k/2)` |
| Explicit coefficient representative | `robustCenterPolynomial`, `robustCenterCoeffs`, `classOf_robustCenterCoeffs` | Done for `k/2 < q` |
| Coefficient sum following (11) | `sum_robustCenterCoeffs`, `sepCenter_representative` | Done: sum is exactly `h`; prescribed-weight form included |
| Theorem 3.7, pointwise | `robust_center_explicit`, `robust_center`, `robust_center_sub_ideal` | Done: `2*k*q < 10*normSq (w*c-a)` |
| Theorem 3.7, squared ideal distance | `idealDistanceSq`, `idealDistanceSq_attained`, `robust_center_distance`, `separation_distance_v2` | Done: attained integer minimum satisfies `2*k*q < 10*distanceSq` |

Explicit constants are `sepK0 = 100` and `sepC0 = 1`. The final v2 theorems assume `k ≥ sepK0`, `q` prime, `q ≥ (2*k)^sepC0`, `w ≠ 0`, and `normSq w ≤ 3*q`. In particular, this works for every odd prime in the required range. Increasing either constant preserves the parameter conditions. No named analytic hypothesis, including `WanPowerSumEstimates`, is needed.

The generic separation theorems allow arbitrary natural weight `h`. `robust_center_explicit` requires only `k ≥ 100`, `k ≤ q-1`, and `q ≥ 4`. The simpler interface assumes `2*k ≤ q`. The proof uses `5*support(e) ≤ 2*k`, `support(w) ≤ 6`, and sparse vanishing at one twice, as in the paper.

The standalone coefficient-sum theorem assumes `k ≥ 2` and `k/2 < q`. The prescribed-weight representative theorem uses the same bounds as separation. It provides both its class and exact coefficient sum, suitable for Lemma 3.3 / Corollary 4.5.

Removed the obsolete q-derived `descentParameter`, `descentWeight`, and the v1 `L/100` interface. The centre, ideal-distance definitions, and polynomial proof helpers are retained and updated.

Open mathematical work in this assignment: none.

Validation completed:

- `LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 2400 lake build Rank2ModuleSVP.RobustCenter` succeeded (6671 jobs; linter warnings only).
- `/tmp/r5_separation_axioms.lean` imports the built module and runs `#print axioms` on all 21 public theorems, including all paper-facing results and polynomial helpers. `lake env lean` succeeded; output is in `/tmp/r5_separation_axioms.log`.
- Every audited theorem depends only on `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `axiom`, or `native_decide` occurs in the owned Lean source.
- Only the assigned Lean file and this job note were edited; verification scratch files are under `/tmp`.
