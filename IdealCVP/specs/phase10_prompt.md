You are continuing work in /workspace/hardness (Lean 4 v4.36.0-rc1 + Mathlib + complexitylib
@ ba134c18 under .lake/packages). Do NOT run `lake update`/`lake exe cache get`, do not change
lakefile/manifest/toolchain, do not use git. Builds: use
`LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 1500 lake build` and
`LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 900 lake env lean <file>`.
No `sorry` in finished code, no `axiom`, no `native_decide` in theorems.

Read NOTES.md (Rounds 6–9, esp. "C — arbitrary principal cyclic CVP membership (not completed)")
and Hardness/Complexity/{CyclicProblem,ModuleProblem,CertificateBits,Verifier,Witness}.lean.

ROUND 10 GOALS (build + NOTES.md "Round 10" after each):

C. Principal cyclic CVP NP-complete on a polytime-recognisable class containing the reduction image.
   Key observation: CyclicFast.compile produces G = B·(1+X^d) + g·(1−X^d) in ℤ[X]/(X^{2d}−1)
   (first half g+B·e₀, second half −g+B·e₀). Via CRT, ℚ[X]/(X^{2d}−1) ≅ ℚ[X]/(X^d−1) × ℚ[X]/(X^d+1),
   G ↦ (2B, 2g). With B ≠ 0 and g ≠ 0 (X^d+1 irreducible over ℚ for d a power of two — see
   ModuleSIVP.lean / Cyclotomic for existing irreducibility/field facts), multiplication by G is
   injective, so the 2d×2d cyclic multiplication matrix is nonsingular and the Cramer/adjugate
   certificate bound used for `principalCVP_mem_NP` applies (the quotient q is unique and its bits are
   polynomially bounded). Either
   (i) prove nonsingularity for every generator whose rotation matrix has nonzero determinant and
       give a polytime check (harder), or
   (ii) (preferred) define `SeparatedCyclicCVP` / restrict `PrincipalCyclicCVP` to "separated"
       generators: G_i + G_{i+d} = 0 for 0<i<d, G_0 + G_d = 2B with B ≠ 0, and the half-difference
       g ≠ 0 — a cheap list check — and prove membership, hardness (the image of CyclicFast.compile
       lies in it; reuse polyTimeReducible_Masked_CyclicCVP), and
       `principalCyclicCVP_npComplete : NPComplete encCVP SeparatedPrincipalCyclicCVP` (name as you like;
       document the restriction exactly like ModuleSIVPLang in Round 9).
   If (ii) is done quickly, try a general-nonsingular version too.

B. (Optional, after C) General Module-SIVP: language over arbitrary bases (b₁,b₂) ∈ (ℤ[X]/(X^d+1))²
   that are K-independent (check u₁v₂ − u₂v₁ ≠ 0 with negacyclicMul — a polytime check since
   ℤ[X]/(X^d+1) is a domain), NP membership via Cramer on the 2d×2d integer basis matrix, hardness by
   the identity-embedding reduction from the separated subclass `ModuleSIVPLang`, headline
   `moduleSIVPGeneral_npComplete`.

If an item cannot be finished, leave only finished building code and document precisely what is
missing. `#print axioms` on all new headlines (scratch in /tmp; only propext, Classical.choice,
Quot.sound). Update README entry points.
