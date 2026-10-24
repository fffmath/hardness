COMMON RULES (Rank2ModuleSVP round 3; you are ONE OF SEVERAL Codex jobs running in parallel in
/workspace/hardness). Lean 4 v4.36.0-rc1 + Mathlib + complexitylib under .lake/packages. Do NOT run
`lake update`/`lake exe cache get`, do not edit lakefile / manifest / toolchain, do not use git.
- ONLY create/edit the files assigned to you below (plus your own section file
  Rank2ModuleSVP/notes/<JOBNAME>.md). Do NOT edit Rank2ModuleSVP.lean, NOTES.md, or any other
  job's files; ALL existing Rank2ModuleSVP files from rounds 1-2 (PrimeCyclotomic, GaussSum, Sparse, SparsePolynomial,
  Descent, Problem, Checker, CheckerAux, Completions, Wan, Descent2, RobustCenter, BennettPeikert) are read-only for you — if you need a small extra lemma about them, put it in
  your own file.
- Build only your own modules: `LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 2400 lake build
  Rank2ModuleSVP.<YourModule>` (this builds its imports). Never run a bare `lake build` and never
  delete .lake. The machine is heavily loaded: builds are slow, be patient, prefer
  `lake env lean <file>` for quick iteration once imports are built.
- No `sorry`, no `axiom`, no `native_decide` in finished code. Named hypotheses only as listed in
  Rank2ModuleSVP/specs/PLAN.md (`WanPowerSumEstimates`, `PrimesThreeModFourDyadic`,
  `BennettPeikertMinimum`), as `def … : Prop` passed explicitly.
- Read Rank2ModuleSVP/specs/PLAN.md, Rank2ModuleSVP/NOTES.md and Rank2ModuleSVP/notes/*.md (rounds 1-2), the round-1 Lean files and
  the paper source Rank2ModuleSVP/paper/src/chapter/*.tex. Reuse IdealCVP by importing it.
- Model facts: `Coeff R q = ZMod q → R`, `Cyclotomic R q` = (AddMonoidAlgebra R (ZMod q))/(Φ_q),
  `classOf`, `normSq` (= canonical norm via q Σ z² − (Σz)²), `conjugate`, `monomial`, `pi`,
  `ramifiedIdeal`, `theta`, `RationalRing q = Cyclotomic ℚ q`. Statements that the paper proves
  with complex embeddings must be re-proved in this model (e.g. via an adjointness identity
  ⟨x·y, z⟩ = ⟨y, conj x · z⟩ for the canonical form, and triangle inequalities with monomial
  isometries) — no complex embeddings needed.
- At the end: `#print axioms` (scratch file in /tmp) on every main theorem you add (only propext,
  Classical.choice, Quot.sound), and write Rank2ModuleSVP/notes/<JOBNAME>.md: paper label → Lean
  name, what is done, what is open, any hypothesis used. Your final answer should summarise the same.
