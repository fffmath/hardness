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
- Round 5 (v2) RUNNING: r2m-p5-checker (Checker*, GaussSum), r2m-p5-counting (Completions, Asymptotics*, Admissible), r2m-p5-separation (RobustCenter, Separation). Prompts phase5_*.md.
## Round 4/5 result (v2)
- r4-cert: **moduleSVP_mem_NP : ModuleSVPLang ∈ NP encSVP unconditional** (B(N) = (N+1)·16·(2N+1)²+1).
- r5-checker: integral v2 checker g, V = 6Σζ^α, Q = 128W⁴h, U = Q + g²; Lemma 4.2; Thm 4.3
  (checker_score_bounds, 0 ≤ R < κ/8); checker_lower / checker_upper_of_clean / threshold_integral.
  GaussSum removed (no q ≡ 3 mod 4 anywhere in the checker).
- r5-counting: v2 regime k ≥ cntK0 = 10^8, q ≥ (2k)^1000: Thm 3.4 (uniform_completions_div, error < 1/4),
  ratio bound, abstract Thm 4.4 admissible_representative (hWan explicit). v1 parameters removed.
- r5-separation: Thm 3.7 separation_distance_v2 (dist² > L/10, k ≥ 100, q ≥ 2k), c = h + π^{⌊k/2⌋}.
- Full build 7239 jobs OK, axioms clean. PrimesThreeModFourDyadic dropped (v2 uses Bertrand).
## Round 6 RUNNING: r2m-p6-reduction (Reduction*.lean: Cor 4.5, module, Lemma 5.1, Thm 5.2),
   r2m-p6-map (Problem odd-prime, Membership update, ReductionMap*: computable map, Bertrand prime scan, polytime).
## Round 6 result (v2)
- r6-reduction: exact_X3C_encoding (Lemma 5.1/Thm 5.2 core, hWan explicit), red_completeness,
  red_soundness, red_corollary_4_5, nonzero determinant.
- r6-map: WellFormed now q prime ∧ q ≠ 2 (odd primes); computable reductionMap K0 C0 with
  semantics lemmas (m₁, m₂, S, q), fixed YES/NO instances, Bertrand prime scan, polytime pieces
  (primeScan, mapK, mapQ, threshold, sum/single lists). OPEN: full ComputableTidilyInPolyTime of the map.
- Full build 7247 jobs OK, axioms clean, no sorry/axiom/native_decide.
