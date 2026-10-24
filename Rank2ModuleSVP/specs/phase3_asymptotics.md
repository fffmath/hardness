
YOUR JOB: JOBNAME = r3-asymptotics. Files: Rank2ModuleSVP/Asymptotics.lean (optionally
Rank2ModuleSVP/AsymptoticsAux.lean). Imports: Rank2ModuleSVP.Checker, Rank2ModuleSVP.Completions,
Rank2ModuleSVP.Wan (all finished, read-only) and Mathlib. Do NOT import Descent2/RobustCenter/
BennettPeikert (another job is still editing them).

GOAL: discharge the asymptotic obligations left open in round 2 (see notes/completions.md
"Remaining obligations" and notes/checker.md "deferred"), for the concrete parameters
k = rsK q, h = rsH q, T = rsT q from Completions.lean, eventually in q (Filter.atTop on primes,
or an explicit ∃ X, ∀ q ≥ X statement — explicit thresholds preferred if cheap).
1. (Completions 1) Under hWan : WanPowerSumEstimates, the three Wan relative errors for m = h-t,
   0 ≤ t ≤ T, tend to 0 uniformly; uniform constant-factor completion-count estimates.
2. (Completions 2) The factorial comparison / one- and two-fixed-coordinate ratio bounds of the
   paper (representative.tex, Lemma on uniform completions / fixed coordinates).
3. (Completions 3) Discharge the exact event budget premise of `enhanced_clean_of_budget`, yielding
   the paper's enhanced-clean representative existence theorem for all large q, with hWan explicit.
4. (Checker) The asymptotic parts of gap-and-stability (reduction.tex): with L = 2kq, H = h(q-h),
   Γ² ≈ 99L/(200(q-1)) (use whatever exact rational/real choice Checker.lean's
   `checker_global_stability_real` and the paper fix; if the paper uses a floor/rational
   approximation, define it here), threshold S = B₀ + Γ²(q-1): prove the inequalities needed in the
   four soundness cases and in completeness, for all large q, as named theorems
   (e.g. `gap_inequalities_eventually`), packaged into a single `structure ReductionParameters q`
   / `theorem reductionParameters_eventually` so the later Reduction job can consume them.
   Read reduction.tex carefully to list every numeric inequality used (cases w=0, w unit-ish, etc.).
Record precisely in notes which inequality corresponds to which paper line.
