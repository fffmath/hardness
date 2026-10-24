# Round 3 — asymptotics

Assigned files only: `Asymptotics.lean`, `AsymptoticsAux.lean`, this note.
Namespace: `Rank2ModuleSVP`. The main module imports the companion module,
`Checker`, `Completions`, and `Wan`; it does not import `Descent2`,
`RobustCenter`, or `BennettPeikert`. IdealCVP is reused through these imports
(in particular its X3C and Sidon structures).

## Paper → Lean

| Paper statement | Lean declaration |
| --- | --- |
| `eq:rs-parameters`, polynomial scale consequences | `rsK_polynomial_small` |
| `thm:uniform-completions`, moving-exponent domination | `wan_power_domination`, `wan_errors_envelope`, `wan_errors_envelope_eventually` |
| All three relative errors tend uniformly to zero | `wan_relative_errors_eventually` |
| `eq:uniform-completion-bounds` | `uniform_completions_eventually`, `uniform_completions_nonempty_eventually` |
| `cor:fixed-coordinate-ratio`, factorial comparison | `factorial_ratio_le_power` |
| `eq:fixed-coordinate-ratio` | `fixed_coordinate_ratio_eventually` |
| `thm:enhanced-clean`, at most 2|P| touching pairs per offset | `touching_pairs_card` |
| `thm:enhanced-clean`, exact finite event budget | `clean_event_budget`, `clean_event_budget_eventually` |
| `thm:enhanced-clean`, arbitrary Sidon offsets | `enhanced_clean_eventually` |
| `thm:enhanced-clean`, actual separated-offset checker | `checker_sidon_mod`, `checker_enhanced_clean_eventually` |
| `eq:Gamma-target-exact`, exact nearest-positive-integer choice | `rsGammaTarget`, `rsGamma` |
| Quantitative control of integer rounding | `rsGamma_sq_bounds`, `rsGamma_sq_bounds_eventually` |
| `eq:HL-parameters`, `eq:F-S-nu-exact` | `reductionH`, `reductionL`, `reductionF`, `reductionBaseline`, `reductionThreshold`, `reductionNu` |
| `lem:gap-and-stability`, all numerical inequalities | `reduction_gap_arithmetic`, `GapInequalities`, `ReductionParameters`, `gap_inequalities_eventually`, `reductionParameters_eventually`, `reductionParameters_explicit` |
| Actual checker baseline agrees with statistics formula | `checker_baseline_eq` |
| Actual checker satisfies all gap inequalities | `ReductionParameters.checker_gap` |
| `eq:global-stability-exact`, rounded integer Γ | `ReductionParameters.checker_stability` |

## Quantitative content and interfaces

For every sufficiently large **natural** q, simultaneously for every t ≤ T,
put m = h-t. All three absolute Wan errors are at most `q^(m-k-1)`.
The collision and coordinate main terms are `q^(m-k)`, so their relative
errors are at most 1/q; the unrestricted main term is one power larger.
`wan_relative_errors_eventually` gives the full uniform epsilon statement,
not merely a fixed constant bound. These estimates themselves are unconditional.

With the explicit input `hWan : WanPowerSumEstimates`, the completion count
satisfies

```
q^(m-k+1)/2 ≤ m! * |F| ≤ 2*q^(m-k+1).
```

The threshold and constants are uniform in the syndrome u, prescribed set P,
and binary prescribed values η. The zeroth syndrome equation is an explicit
premise. `fixed_coordinate_ratio_eventually` proves the cross-multiplied bound

```
q^r * |F_Q| ≤ 4*h^r*|F|
```

for every r = |Q| with `|P|+r ≤ T` and Q disjoint from P. This is stronger
than restricting to r=1,2, and is equivalent to the paper's probability bound
because q and |F| are positive. The factorial lemma holds for arbitrary r≤m.

`clean_event_budget` proves the exact premise used by
`enhanced_clean_of_budget` whenever

```
4*|D|*(2*|P|*h+h^2) < q.
```

It handles one-free-endpoint and two-free-endpoint pairs separately, with no
independence assumption. `clean_event_budget_eventually` discharges this when
`|P|+2≤T`, `|D|≤C*T^2`, and zero is not an offset, using the existing
`clean_budget_eventually (4*C)`. `checker_enhanced_clean_eventually` removes
the abstract offset-cardinality premise: witness offsets contribute at most
n² and bad offsets at most 2W²=18n², so C=19 suffices. It returns membership
in the actual completion set and `Checker.Clean` for the rational cast of the
integral binary vector. Sidon uniqueness modulo q is proved from the paper's
existing row bound `4*tau*M < q`.

The rounded integer is precisely

```
max 1 (floor(sqrt(99*k*q/(100*(q-1))) + 1/2)).
```

Thus ties round upward. For `q≥100001` and `k≥10^12`,
`0.9899*k ≤ Γ² ≤ 0.9901*k`. The proof uses floor inequalities and real
square-root identities, with no approximation assumption. The explicit
reduction threshold is

```
q ≥ max 100001 ((2*10^12)^1000).
```

`reductionParameters_explicit` establishes the entire package at that
threshold. The eventual theorem also holds for all natural q, so restricting
to primes congruent to three modulo four requires no further asymptotics.
The package is uniform over real statistics `0<W≤3T`, `0≤M≤W`, and
`0≤v≤W²/q`. `ReductionParameters.checker_gap` supplies those statistics for
the actual checker, using its proved V norm bound, `W=3n`, and the explicit
no-isolated-row assumption. `ReductionParameters.checker_stability` applies
the existing coefficient-model stability theorem with this Γ and proved ν
bounds. No complex embedding, quotient field instance, or new analytic input
is used.

## Numeric inequalities and exact paper lines

Line numbers refer to the unchanged `paper/src/chapter/reduction.tex`.

| Paper line / use | Lean field or theorem |
| --- | --- |
| 83, B₀>0 | `GapInequalities.baseline_pos` |
| 83, 0<ν<1, required to invoke stability | `GapInequalities.nu_pos`, `.nu_lt_one` |
| 86 and 252–257, root-of-unity nonbinary shell | `GapInequalities.nonbinary_unit`: `(1-ν)(H+2q+F)>S` |
| 87 and 218–224, w=0 | `GapInequalities.zero_multiplier`: `S<L` |
| 88 and 272–276, short nonsigned-monomial multiplier | `GapInequalities.short_nonunit`: `(1-ν)(L/100+Γ²(2q-4))>S` |
| 89 and 286, long multiplier | `GapInequalities.long_nonunit`: `3F>S` |
| 95–98, global stability | `ReductionParameters.checker_stability` |
| 128, baseline error sufficient for the fine shell gap | Internal checked estimates `hBerrlo`, `hBerrhi` in `reduction_gap_arithmetic` prove `|B₀-H|≤q/100` |
| 146, cancellation smaller than the 2q shell gap | Internal `hcancel` proves `ν(H+2q+F)≤q/2` |
| 203–204, completeness attains S | `reduction_completeness_threshold` |
| 246, binary negative instance has S+2>S | `reduction_binary_gap` |
| 286, strict intermediate step 3qΓ²>3F | `ReductionParameters.long_coordinate` |
| 361, S>0 for the integral threshold | `ReductionParameters.threshold_pos` |

## Hypotheses and remaining work

Only `WanPowerSumEstimates` is used, passed explicitly to completion-count,
ratio, and enhanced-clean results. All parameter, rounding, factorial,
finite-union, gap, and stability results are unconditional. No new named
hypothesis is introduced. There are no remaining asymptotic obligations in
this job; constructing the rank-two module and its final encoding is outside
this assignment.

## Validation

The final targeted build passed:

```
LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 2400 lake build Rank2ModuleSVP.Asymptotics
```

It built both assigned modules successfully (6689 jobs; auxiliary module 138 s,
main module 109 s). Log: `/tmp/r3-asymptotics-final-build.log`.
The source scan found no `sorry`, axiom declaration, or `native_decide`.
The final compiled-module audit passed (exit code 0):

```
LAKE_CACHE_DIR=/tmp/hardness-lake-cache lake env lean /tmp/r3-asymptotics-axioms.lean
```

It applies `#print axioms` to **all 30 new public theorems**, including every
main theorem in both modules. Every printed dependency belongs to the
allowed set `{propext, Classical.choice, Quot.sound}`; a scripted check of all
30 output lines confirmed this. Log: `/tmp/r3-asymptotics-axioms.log`.
No `sorryAx` occurs. The main and auxiliary final source files are the versions
checked by the successful build and this audit.
