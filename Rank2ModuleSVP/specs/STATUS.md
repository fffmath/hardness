# Rank2ModuleSVP — director status log

## Setup (2026-10-24)
- Paper downloaded from arXiv:2609.01469 (PDF + TeX source); ePrint 2026/1856 is the same paper
  (ePrint PDF fetch blocked by Cloudflare, arXiv version used).
- Plan: specs/PLAN.md. Round 1 prompt: specs/phase1_prompt.md.

## Round 1 (RUNNING) — prime cyclotomic model, sparse tools, Gauss sum, problem statement, descent (stretch)
- prompt: specs/phase1_prompt.md; log: /workspace/hardness_codex_r2m1.log; PID 1475439
- session id: 01a16cf2-e572-7c43-9ad6-706e58120fed (resume: `codex exec resume <id> -c sandbox_mode='"workspace-write"' -`)
- On interruption: check pgrep; if log stalls >30 min, kill and resume with nudge. After: build/audit/commit/push.
- Result: PrimeCyclotomic model, canonical norm identities, sparse_tools_i/ii, second_shell, Gauss sum
  (theta_sq etc.), Problem (ModuleSVPLang, encSVP), Descent (liftedRS, coset_syndrome, binary_shell).
  64 theorems axiom-clean; full build 7223 jobs. BennettPeikertMinimum still a hypothesis.

## Round 1 commit: 07062aa
## Round 2 (RUNNING, parallel cx-run jobs)
- r2m-p2-checker (Checker.lean) and r2m-p2-descent (Descent2/RobustCenter/BennettPeikert.lean);
  jobs in /workspace/shared/jobs/<name>/{run.log,last.md}. completions job (phase2_completions.md) queued
  until load drops. Prompts = phase2_common.md + phase2_<job>.md.
- r2m-p2-completions (Completions.lean, Wan.lean) launched 18:25 UTC+8.

## Round 2 result (all three jobs DONE; committed)
- Checker/CheckerAux: row_shift_separation, checker_U_properties, checker_V_norm_bound, checker_score,
  E_nonneg_binary, E_eq_zero_of_clean, checker_global_stability_real (no hypotheses; asymptotic gaps deferred).
- Wan/Completions: exact WanPowerSumEstimates Prop, rsK/rsH/rsT parameters + scale lemmas,
  wan_good_count_bounds (uses hWan), enhanced_clean_of_budget (finite union bound). Open: uniform
  eventual Wan error bounds, coordinate ratio, budget discharge.
- Descent2/RobustCenter/BennettPeikert: cyclotomic_descent, ideal_preimage, ramified coset syndrome,
  **bennettPeikertMinimum PROVED** (Newton identities) => ramifiedIdeal_minimum unconditional,
  robust_center_distance for q >= 200^1000.
- Full root build 7076 jobs OK; #print axioms on main theorems: only propext/Classical.choice/Quot.sound.
- Remaining named hypotheses: WanPowerSumEstimates, PrimesThreeModFourDyadic.

## Round 3 (RUNNING): r2m-p3-membership (Membership*.lean, NP membership),
   r2m-p3-asymptotics (Asymptotics*.lean, Wan/Checker asymptotic obligations, ReductionParameters).
   r2m-p3-reduction (Reduction*.lean, Clearing.lean): module M, exact-X3C-encoding, denominator clearing, under explicit GapConditions.

## Round 3 outcome (v1 target)
- r3-asymptotics DONE (v1 parameters; Asymptotics*.lean committed as v1 history).
- r3-membership DONE: Membership*.lean, moduleSVP_mem_NP_of_resource_bounds (certificate-bit premise).
- r3-reduction KILLED at 19:52 (v1 rational checker; superseded by v2). Partial files moved to
  /workspace/hardness_v1_partial (not committed). r4-primes KILLED (v2 only needs Bertrand).
- r4-cert RUNNING (MembershipCert.lean, unconditional NP membership).

## RETARGET to paper v2 (see specs/v2_diff.md)
