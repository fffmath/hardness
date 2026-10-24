# checker (round 2)

Files: `CheckerAux.lean`, `Checker.lean`. Namespace:
`Rank2ModuleSVP.Checker`. Reuses `IdealCVP.X3CInstance` and
`IdealCVP.SidonPositions`.

Paper label → Lean API:

- incidence-count → `incidence_count`, `rows_le_incidence_count`.
- row-shifts → `alphaStar`, `alpha_le_alphaStar`, `tau`, `beta`, `offsetInt`, `d`.
- row-shift-separation → `row_shift_separation`, `row_shift_signed_separation`,
  `row_shift_bad_separation`, `bad_card_bound` (≤ 2W²).
- gauss-sum over ℚ → `rationalize`, `thetaQ`, `conjugate_thetaQ`, `thetaQ_sq`.
- checker-U → `U`.
- checker-U-properties → `checker_U_properties`, `U_mul_conjugate`, `U_norm_exact`,
  `U_norm_expanding`, `U_isUnit`, `U_ne_zero`.
- checker-V → `V`, `V_denominator`, and instance-specific `checkerV`.
- multiplier bound for V → `D_norm_bound`, `V_norm_bound`,
  `checker_V_norm_bound`.
- checker-additional-correlations → `E`.
- enhanced-clean-correlations → `Clean`, `E_eq_zero_of_clean`.
- checker-baseline → `B₀`.
- checker-score → `checker_score`, `E_nonneg_binary`,
  `checker_score_clean_cover`.
- global-stability-exact → `global_stability_exact` and
  instance-specific `checker_global_stability`, and the arbitrary-real-Γ
  versions `global_stability_exact_real`, `checker_global_stability_real`.

The coefficient trace and descended form are `trace` and `inner`;
`inner_adjoint` is the multiplication/conjugation adjointness identity.
The analytic arguments use these identities and positivity, with no complex
embedding or assumed field structure. Invertibility follows from injectivity
of the norm-expanding multiplication map and finite dimensionality.

Conventions: rows are `Fin (3*I.q)` and `beta` uses row index `i.val+1`.
`alphaStar` is exactly the last (largest) Sidon position; τ is exactly
2α⋆+1, so the separation hypothesis is the paper’s exact q > 4τM bound.
`rowValue` is the actual incidence row sum Aξ. Error sums use ordered
incidence pairs. Both rational Γ (including the integer Γ used by the reduction) and
arbitrary real Γ are supported.

No named hypotheses are introduced or used. The assumptions are explicit
primality, q % 4 = 3, the indicated offset-size bound, binary coefficients
and prescribed weight, and the explicit positivity/upper bound on ν for
stability. The asymptotic portions of gap-and-stability are deferred as
requested.

All proofs passed a complete incremental Lean check in the combined scratch
file `/tmp/CheckerCombined.lean`. A scratch `#print axioms` audit covered all
92 public theorems, including every main theorem, and found only
`propext`, `Classical.choice`, and `Quot.sound`. The audit output is
`/tmp/checker-axioms-incremental.log`. The final standalone audit
`LEAN_PATH=… lean /tmp/CheckerAxioms.lean` also passed against the compiled
modules: all 92 public theorems use only the same three axioms; output
`/tmp/checker-axioms.log`. The targeted build
`LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 2400 lake build Rank2ModuleSVP.Checker`
passed (6,647 jobs; `/tmp/checker-build3.log`). All requested non-asymptotic
statements are implemented. No mathematical obligation remains in this job;
the asymptotic gap inequalities remain deferred to a later round as requested.
