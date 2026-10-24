COMMON RULES (Rank2ModuleSVP round 5 = RETARGET TO PAPER v2; you are ONE OF SEVERAL Codex jobs running
in parallel in /workspace/hardness). Lean 4 v4.36.0-rc1 + Mathlib + complexitylib under .lake/packages.
Do NOT run `lake update`/`lake exe cache get`, do not edit lakefile / manifest / toolchain, do not use git.
- THE TARGET IS NOW PAPER v2: Rank2ModuleSVP/paper/rank2svp_v2.txt (text of rank2svp_v2.pdf). Read
  Rank2ModuleSVP/specs/v2_diff.md first: v2 works for every odd prime q, has an integral checker
  U = Q + g², V = 6Σζ^{α_j} (no Gauss sum), chooses k first and q ≥ (2k)^{C₀}, h = ⌊21k/20⌋.
  The old v1 paper source (paper/src) is only background.
- ONLY create/edit the files assigned to you below (plus Rank2ModuleSVP/notes/<JOBNAME>.md). Do NOT
  edit Rank2ModuleSVP.lean, NOTES.md, or other files. Read-only for you: PrimeCyclotomic, Sparse,
  SparsePolynomial, Problem, Descent, Descent2, BennettPeikert, Wan, Membership*, and every file not
  assigned to you. If you need an extra lemma about them, put it in your own file.
- Files you own that are v1-specific may be REWRITTEN for v2 (git keeps v1 history); remove dead v1
  material from your files, but keep any lemma that v2 still uses.
- Asymptotic "sufficiently large k₀, C₀" statements: use EXPLICIT natural-number constants (huge is fine)
  defined in your files with names prefixed by your job (e.g. `sepK0`, `sepC0`), and state theorems
  for all k ≥ K0, q prime, q ≥ (2k)^C0 (monotone in the constants so a later job can take a max).
- Build only your own modules: `LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 2400 lake build
  Rank2ModuleSVP.<YourModule>`; never a bare `lake build`, never delete .lake. Machine is loaded:
  prefer `lake env lean <file>` for iteration.
- No `sorry`, `axiom`, `native_decide`. The only allowed named hypothesis is `WanPowerSumEstimates`
  (Wan.lean), passed explicitly; do not introduce others.
- Model: `Coeff R q = ZMod q → R`, `Cyclotomic R q` = AddMonoidAlgebra quotient by Φ_q, `classOf`,
  `normSq` (canonical norm = q Σ z² − (Σ z)²), `conjugate`, `monomial`, `pi`, `ramifiedIdeal`,
  `pairNormSq`. Embedding arguments must be re-proved in this model (adjointness of the canonical
  form, triangle inequality, monomial isometries).
- At the end: `#print axioms` (scratch file in /tmp) on every main theorem (only propext,
  Classical.choice, Quot.sound) and write Rank2ModuleSVP/notes/<JOBNAME>.md: v2 paper label → Lean name,
  done / open, hypotheses. Final answer summarises the same.
