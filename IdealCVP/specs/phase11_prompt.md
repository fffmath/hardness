You are continuing work in /workspace/hardness (Lean 4 v4.36.0-rc1 + Mathlib + complexitylib
@ ba134c18 under .lake/packages). Do NOT run `lake update`/`lake exe cache get`, do not change
lakefile/manifest/toolchain, do not use git. Builds: use
`LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 1500 lake build` and
`LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 900 lake env lean <file>`.
No `sorry` in finished code, no `axiom`, no `native_decide` in theorems.

Read NOTES.md (Rounds 6–10, incl. the deferred items) and Hardness/Complexity/{ModuleProblem,
SeparatedCyclic,CyclicProblem,CertificateBits,Verifier,Witness}.lean, Hardness/{CertificateBound,
Certificates,ModuleSIVP,Cyclic}.lean.

ROUND 11 GOALS — the two remaining NP-membership generalisations. Do 1 first, then 2.
Build + record in NOTES.md "Round 11" after each milestone.

1. GENERAL MODULE-SIVP. New language `ModuleSIVPGeneral` over the same input type
   `ModuleSIVPInput` (or a new one if cleaner): d power of two, two basis vectors
   b₁=(b₁₁,b₁₂), b₂=(b₂₁,b₂₂) ∈ (ℤ[y]/(y^d+1))², well-formed iff lengths ok, Γ ≥ 0 and
   b₁₁·b₂₂ − b₁₂·b₂₁ ≠ 0 (negacyclicMul; polytime check). Prove this check ⇔ K_d-linear
   independence ⇔ nonsingularity of the 2d×2d integer basis matrix (ℤ[y]/(y^d+1) is a domain /
   X^d+1 irreducible over ℚ; the 2d×2d matrix is the ℤ-basis {y^i b₁, y^i b₂}). Language: module
   spanned by b₁,b₂ has two K-independent vectors of squared norm ≤ Γ (bridge to
   `SecondMinimumSq`/`ModuleSIVPInstance.Yes`).
   - Membership: certificate = R-coefficients (a₁,a₂),(c₁,c₂) of the two short vectors, i.e. integer
     coordinates w.r.t. the 2d×2d nonsingular basis; existence of a polynomially bit-bounded
     certificate via Cramer/adjugate (reuse CertificateBound / CertificateBits: entries of short
     vectors ≤ Γ, Hadamard/adjugate bound on the basis matrix). Verifier recomputes the vectors with
     negacyclicMul, checks norms ≤ Γ and independence (u₁v₂−u₂v₁ ≠ 0). Native polytime as in
     Verifier.lean / SeparatedCyclic.lean.
   - Hardness: identity/near-identity map from `ModuleSIVPLang` (triangular subclass, already NP-hard)
     — a triangular well-formed instance is general well-formed (det = Q·g ≠ 0) with the same module
     and Γ; malformed inputs map to a fixed NO instance.
   - Headline `moduleSIVPGeneral_npComplete`.

2. GENERAL PRINCIPAL CYCLIC CVP MEMBERSHIP (arbitrary, possibly singular generators G of
   ℤ[X]/(X^{2d}−1)): `principalCyclicCVPGeneral_mem_NP : PrincipalCyclicCVP ∈ NP encCVP`, then
   `principalCyclicCVPGeneral_npComplete : NPComplete encCVP PrincipalCyclicCVP` (hardness already:
   `principalCyclicCVP_npHard`).
   Key lemma (general linear algebra, state it for any integer matrix M : Matrix (Fin m) (Fin n) ℤ):
   if M q = v has an integer solution q, it has one with ‖q‖∞ ≤ B(M,v) where log B is polynomial in
   the bit size of (M,v). Suggested proof (HNF-free):
   - let r = rank M over ℚ; choose rows I and columns J (|I|=|J|=r) with D := det M_{I,J} ≠ 0;
   - for each non-pivot column j ∉ J, the vector k_j := D·e_j − (adj(M_{I,J})·M_{I,j}) on J is an
     integer kernel vector of M (all rows, since rows outside I are ℚ-combinations of rows in I on the
     column space; or argue via rank: column j is in the ℚ-span of columns J);
   - given any integer solution q*, subtract integer multiples of k_j to bring each non-pivot
     coordinate into [0,|D|); the pivot coordinates are then determined by M_{I,J} q_J =
     v_I − M_{I,N} q_N and bounded by Cramer: |q_J| ≤ |adj|·(|v|+n|M||D|)/|D|.
   - bound |D|, |adj| by Hadamard / n!·max^n (existing CertificateBound lemmas).
   Mathlib facts: `Matrix.rank`, existence of a nonzero r×r minor (e.g. via
   `Matrix.rank_eq_finrank_span_cols`, `LinearIndependent` subfamily extension), `Matrix.adjugate`,
   `Matrix.mul_adjugate`. If the general minor selection is too costly, a fallback is allowed:
   ANY argument specific to circulant matrices / ℤ[X]/(X^{2d}−1) that gives a polynomial bound.
   The closest lattice vector w has entries bounded by |target|+sqrt(threshold), so the certificate is
   q with polynomially many bits; the verifier checks w = cyclicMul G q and the distance.
   NP membership for arbitrary generators then needs only this existence bound plus the existing
   cyclic verifier machinery in SeparatedCyclic.lean.

If either item truly stalls after real effort, keep only finished building code and document
precisely what is missing (named hypothesis only if truly unavoidable, never an axiom).
`#print axioms` on all new headlines (scratch in /tmp; only propext, Classical.choice, Quot.sound).
Update README "Final summary" table and "Remaining gaps" accordingly.
