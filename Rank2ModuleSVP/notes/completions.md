# Round 2 — completions

This is a retained round note. See [the current paper-to-Lean map](../NOTES.md)
for the final interfaces; unused intermediate corollaries were removed during cleanup.

Assigned files: `Rank2ModuleSVP/Wan.lean`, `Rank2ModuleSVP/Completions.lean`.
The round-1 files are imported, not modified; in particular the syndrome and
binary-vector predicates come from `Descent`, which reuses IdealCVP.

## Paper → Lean

- `prop:wan-power-sum-estimates` → `WanPowerSumEstimates`,
  `powerSumSolutions`, `PositiveMoment`. The hypothesis states all three
  real-valued estimates for every prime, admissible k,m and positive syndrome.
  Half powers use real exponents. It is a `def : Prop`, never an axiom.
- `eq:rs-parameters` → `rsK`, `rsT`, `rsH`. Greatest-integer characterizations
  are `rsK_greatest`, `rsT_greatest`. `rsK_tendsto`, `rsT_tendsto`,
  `rsT_isLittleO`, `rsH_isLittleO`, `rsH_real_rounding` prove the scale facts.
  `completion_parameter_range` gives Wan's range uniformly for t ≤ T.
- `thm:uniform-completions`, exact counting step → `completions`,
  `freeSupports`, `supportOrderingsEquiv`, `card_supportOrderings`,
  `completions_eq_image_freeSupports`, `card_completions_eq_freeSupports`,
  `orderedCompletions_eq_good`, `factorial_mul_card_completions`.
  In particular the latter states m! |F| = |good power-sum tuples|.
- `thm:uniform-completions`, explicit-error step →
  `card_powerSumSolutions_le_good_add`, `wan_good_count_bounds`,
  `completions_count_bounds`, `completions_nonempty_of_error_budget`.
  The collision union uses ordered distinct index pairs (a harmless factor
  of two); forbidden prescribed entries use exactly m |P| events.
- `cor:fixed-coordinate-ratio`, exact event identity → `completionEvent_eq`.
  `pairEvent_subset_completionEvent`, `card_pairEvent_le` reduce pair events
  to the extra prescribed free coordinates.
- `thm:enhanced-clean`, finite union-bound and Sidon step →
  `exists_clean_products_of_budget`, `enhanced_clean_of_budget`,
  `cyclicCorrelation_eq_single`, `cyclicCorrelation_eq_zero`.
  Witness/bad offsets are abstract and no checker definitions are imported.
  `clean_budget_eventually` proves the eventual smallness of the polynomial
  numerator C T² (2 T h + h²), for each fixed natural C.

## Remaining obligations

This implements the fallback requested in the job: exact bijections/counting
identities and the finite union-bound skeleton, with separated asymptotic facts.
It does **not** yet prove the full eventual Θ estimate or the eventual
fixed-coordinate probability bound. Specifically still open:

1. Bound the three Wan relative errors uniformly for m=h-t, 0 ≤ t ≤ T,
   proving they tend to zero. The explicit errors are definitions in `Wan`.
2. Deduce uniform constant-factor completion estimates and the factorial
   comparison giving the one/two coordinate ratio bound.
3. Combine that ratio bound with the at-most-2|P| one-free-endpoint pairs per
   offset, and at-most-q two-free-endpoint pairs, to discharge the exact
   event budget in `enhanced_clean_of_budget`. The Sidon and correlation
   conclusion itself is already separated from that numerical premise.

No additional named analytic hypothesis is introduced to cover these gaps.
The count bounds take `hWan : WanPowerSumEstimates` explicitly. The parameter,
support, factorial, event-identity, and exact-budget clean theorems are
unconditional. Validation and axiom-audit results follow below.

## Validation

- The combined current source passed Lean with all 52 public theorems checked.
- `/tmp/completions-audit-source.lean` ran `#print axioms` on all 52 theorems;
  Lean exited successfully. Every report contains only `propext`,
  `Classical.choice`, and `Quot.sound`. The audit source was checked to match
  the two current source files exactly. Log: `/tmp/completions-source-axioms.log`.
- A source scan found no `sorry`, `axiom` declaration, or `native_decide`.
- `Rank2ModuleSVP.Wan` has a successful module build. The final
  `LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 2400 lake build
  Rank2ModuleSVP.Completions` passed (6669 jobs; Wan 258 s, Completions 287 s).
  Log: `/tmp/completions-final-build.log`.
