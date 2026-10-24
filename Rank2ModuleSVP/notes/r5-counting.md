# r5-counting — paper v2

Status: **done** for all assigned counting and abstract admissibility obligations.
All names below are in namespace `Rank2ModuleSVP`.

## Paper label → Lean name

| v2 label | Lean declaration | Status |
|---|---|---|
| §3.2 absolute constants | `cntK0 = 100000000`, `cntC0 = 1000` | done |
| (6), h = floor(21k/20) | `cntH`, `cntH_rounding`, `cntH_real_rounding`, `cntH_bounds` | done |
| (7), H = h(q-h), L = 2kq | `cntNormH : ℤ`, `cntL : ℕ` | done |
| Uniform range for Wan after prescribing bits | `cnt_sqrt_small`, `cnt_parameter_range` | done |
| Increasing absolute constants | `cnt_regime_mono` | done |
| (8), the finite family F(u;P,η) | `completions`, `mem_completions` | retained, generic |
| t = sum of prescribed bits | `fixedOnes_card_sum` | done |
| (9), shifted positive moments | `shiftedMoment`, `syndrome_insert_free` | retained, generic |
| (10), ordered tuples and factorial division | `orderedCompletions_eq_good`, `factorial_mul_card_completions` | retained, generic |
| Wan finite counting skeleton | `completions_count_bounds` (uses `wan_good_count_bounds`) | retained, generic |
| Theorem 3.4 | `uniform_completions`, `uniform_completions_div` | done, factors 3/4 and 5/4 |
| Theorem 3.4, strict relative error < 1/4 | `uniform_completions_relative_error` | done |
| Stronger counting interval | `uniform_completions_sharp` | done, factors 13/16 and 17/16 |
| F nonempty | `uniform_completions_nonempty` | done |
| §4.3, strict coordinate ratio | `fixed_coordinate_ratio`, `fixed_coordinate_ratio_div` | done; any number of added coordinates within the size budget, including 1 and 2 |
| §4.3, at most 2n pairs per offset touching P | `touching_pairs_card` | done |
| §4.3, finite quantitative union bound | `clean_event_budget` | done, constant 2 |
| §4.3, O(k³) numerator | `cnt_clean_numerator` | done, numerator ≤ 3200k³ |
| §4.3, union bound < 1 | `cnt_clean_budget` | done |
| Theorem 4.4, all external pairs at supplied offsets | `admissible_completions` | done |
| Theorem 4.4, arbitrary forbidden-pair predicate | `admissible_representative` | done |
| (20), generic correlation tools | `cyclicCorrelation_eq_single`, `cyclicCorrelation_eq_zero`, `enhanced_clean_of_budget` | retained, generic |

## Hypotheses and consumer interface

The counting and existence theorems explicitly take `hWan : WanPowerSumEstimates`.
This is the only external named estimate. They assume `q.Prime`, `cntK0 ≤ k`,
and `(2*k)^cntC0 ≤ q`, with the usual `[NeZero q]` instance for `ZMod q`.
No congruence condition modulo four is present. The numerical regime already
excludes the prime two, so the results cover every odd prime in the stated range.
`cnt_regime_mono` lets consumers replace either absolute constant by a larger one.

For Theorem 3.4, `u : Fin k → ZMod q` has zeroth coordinate `cntH k` modulo q;
`P.card ≤ Nat.sqrt k`; and the integral function `η` takes values zero or one on P.
Its values outside P do not matter. The theorem's `m` is
`cntH k - (fixedOnes P η).card`; `fixedOnes_card_sum` identifies the prescribed
weight with the paper's sum. `uniform_completions_div` states the actual count
bounds with main term `wanMain q k m / m.factorial = q^(m-k+1)/m!`.

For the ratio theorem, supply an additional finite coordinate set J disjoint
from P, with `P.card + J.card ≤ Nat.sqrt k`. The event is `completionEvent F J`.
`fixed_coordinate_ratio_div` gives the strict inequality
`|F_J| / |F| < 2*(h/q)^J.card`.

Import `Rank2ModuleSVP.Admissible` for the abstract Theorem 4.4. Supply:

* `P.card + 2 ≤ Nat.sqrt k` and prescribed binary values on P;
* a finite offset set D with `0 ∉ D` and `D.card ≤ 100*P.card^2 + 100`;
* `forbidden : ZMod q → ZMod q → Prop`, with
  `forbidden a b → b-a ∈ D ∧ (a ∉ P ∨ b ∉ P)`.

`admissible_representative` produces `x ∈ completions k (cntH k) u P η` such
that `x a * x b = 0` for every forbidden pair. Membership includes binarity,
syndrome, exact integral weight, and all prescribed values. For distinct positions
α₁,…,αₙ, instantiate P with their image, so `P.card = n`.
The checker consumer can take `D := D_wit ∪ D_bad` and its required pairs from
(20). `admissible_completions` also gives the stronger conclusion directly for
all pairs at offsets in D with at least one endpoint outside P.

The quantitative budget proved is
`2*D.card*(2*P.card*h+h^2) < q`; its numerator is at most `3200*k^3`.
The proof uses the one- and two-free-coordinate bounds, without independence.
Concrete checker offset/cardinality/Sidon facts belong to the checker job;
there is no remaining abstract counting obligation here.

## Removal of v1 dependencies

Removed `rsK`, `rsT`, `rsH`, the old one-variable eventual statements,
`ReductionParameters`, and the old reduction gap/checker wrappers from the owned
files. Both asymptotics modules have no Checker/GaussSum/RobustCenter import.
The generic support bijections and exact-budget correlation results remain.

## Validation

Successful targeted build:

```
LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 2400 lake build Rank2ModuleSVP.Admissible
```

This builds the owned chain Completions → AsymptoticsAux → Asymptotics → Admissible.
Direct `lake env lean` checks were also used during development.

`/tmp/r5-counting-axioms.lean` imports Admissible and runs `#print axioms` on all
53 theorems declared in the four owned modules. The successful output is in
`/tmp/r5-counting-axioms.log`. Every result uses only a subset of
`propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `axiom`, or `native_decide` occurs in these modules.

Open assigned obligations: **none**.
