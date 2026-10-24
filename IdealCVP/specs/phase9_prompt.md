You are continuing work in /workspace/hardness (Lean 4 v4.36.0-rc1 + Mathlib + complexitylib
@ ba134c18 under .lake/packages). Do NOT run `lake update`/`lake exe cache get`, do not change
lakefile/manifest/toolchain, do not use git. Builds: use
`LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 1500 lake build` and
`LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 900 lake env lean <file>`.
No `sorry` in finished code, no `axiom`, no `native_decide` in theorems.

Read NOTES.md (Rounds 6–8) and Hardness/Complexity/*.lean first. Done: `principalCVP_npComplete`,
`x3c_npComplete : NPComplete encX3C X3CLang`, `principalCVP_npHard_via_X3C`,
`principalCyclicCVP_npHard`; list-level compiler `compileFast` (cubic Sidon) with native polytime
proof `poly_compileFast`, `compileX3CList`.

ROUND 9 GOALS (in order; build + record in NOTES.md "Round 9" after each):

A. Module-SIVP NP-completeness at the class level (paper Def. module-SIVP, Hardness/ModuleSIVP.lean:
   `completion`, `completionBasis`, `module_completion`, `completionScale`, `toModuleSIVP`).
   - Define a list-level problem `ModuleSIVPInput` (d in unary, the two basis vectors of a rank-2
     module in (ℤ[X]/(X^d+1))² as coefficient lists, Γ) with encoding `encModuleSIVP`, and the
     language `ModuleSIVPLang` = well-formed (d power of two, lengths, basis independent over K — or
     whatever well-formedness is decidable in polytime) ∧ the module spanned has two K-independent
     vectors of squared norm ≤ Γ. Bridge it to `ModuleSIVPInstance.Yes`/`SecondMinimumSq`.
   - `moduleSIVP_mem_NP`: certificate = R-coefficients of two module vectors (or the vectors with
     an R-combination); check independence via u₁v₂−u₂v₁ ≠ 0 in ℤ[X]/(X^d+1) (negacyclicMul), norms
     ≤ Γ. Certificate size: vectors of squared norm ≤ Γ have entries ≤ Γ; their coefficients w.r.t.
     the basis are bounded via Cramer/adjugate (reuse CertificateBound/CertificateBits machinery; the
     2d×2d integer matrix of the basis is nonsingular under well-formedness). If NP membership of the
     general problem is not reachable, restrict the language to a polytime-recognisable subclass that
     still contains the image of the reduction (e.g. lower-triangular bases (g,T),(0,Q)) and say so.
   - `polyTimeReducible_CVP_ModuleSIVP` (or from MaskedSys/X3C): list-level completion
     (Q = completionScale-like integer computed in polytime, Γ = Q² + Δ, or the paper's choice),
     correctness via `module_completion`, polytime via fun_prop like CompileFastPolyTime.lean.
   - headline `moduleSIVP_npComplete : NPComplete encModuleSIVP ModuleSIVPLang`.

B. CVPP corollary (Karp–Lipton). complexitylib has `PPoly`, `PAdvice`, `PAdvice_subset_PPoly`,
   `PPoly.exists_of_polyTime`, `PH_eq_SigmaP_two_of_SAT`, and
   `PH_eq_SigmaP_two_of_NP_subset_PPoly (h : ∀ {β} (encB : β ↪ List Bool), ∀ B ∈ NP encB,
     ∃ L ∈ PPoly, ∀ b, b ∈ B ↔ encB b ∈ L) : PH enc = SigmaP 2 enc`
   (Complexity/Computability/Complexity/Classes/PH/KarpLipton.lean, Circuit/Boolean/*.lean).
   - Fixed family: for universe size m, the lattice must depend only on m. Build it from
     compileFast applied to the masked system whose columns are ALL 3-subsets of [m] (or all
     ordered triples — any list depending only on m), rhs all 1, mask = presence of the triple in the
     X3C instance. Check (and prove) that the generator g depends only on m (the mask only enters
     the target/threshold); if compileFast's g also depends on the mask, factor it so it doesn't
     (cf. Hardness/Fixed.lean, CVPP.lean `cvpp_advice_decides` for the abstract version).
   - Define `FixedCVPP : Set (ℕ × (List ℤ × ℤ))` (m unary, target, threshold) := distance from the
     target to the fixed principal ideal lattice (generator `fixedGen m`) ≤ threshold, with encoding.
   - Prove `polyTimeReducible_X3C_FixedCVPP` (polytime map X3C instance ↦ (m, target, Δ)).
   - Prove P/poly closure under polytime reductions (if missing in complexitylib):
     `PPoly.of_polyTimeReducible : PolyTimeReducible encA encB A B → (∃ L ∈ PPoly, ∀ b, b ∈ B ↔ encB b ∈ L)
       → ∃ L' ∈ PPoly, ∀ a, a ∈ A ↔ encA a ∈ L'` (circuits for the reduction via
     `PPoly.exists_of_polyTime`/machine simulation, then for input length n combine the
     poly-many circuits for output lengths ≤ p(n), or pad; whichever is easier in the library).
   - Headlines:
     `np_subset_ppoly_of_fixedCVPP (h : ∃ L ∈ PPoly, ∀ x, x ∈ FixedCVPP ↔ encFixedCVPP x ∈ L) :
        ∀ {β} (encB : β ↪ List Bool), ∀ B ∈ NP encB, ∃ L ∈ PPoly, ∀ b, b ∈ B ↔ encB b ∈ L`
     and `PH_eq_SigmaP_two_of_fixedCVPP ... : PH enc = SigmaP 2 enc`.
     Also the preprocessing form: if there is advice `a : ℕ → List Bool` with |a m| ≤ poly(m) and a
     poly-time decider `D` with `D (a m, t, Δ) = true ↔ (m,t,Δ) ∈ FixedCVPP` then the hypothesis above
     holds (via PAdvice/PPoly, padding the advice index to input length as needed) — state it as
     `PH_eq_SigmaP_two_of_polyCVPP`. If this preprocessing form is too costly, do the PPoly form only and
     document.

C. If time remains: NP membership of `PrincipalCyclicCVP` (Hardness/Complexity/CyclicProblem.lean),
   giving `principalCyclicCVP_npComplete`.

If an item cannot be finished, leave only finished building code and document precisely what is
missing (a clearly named hypothesis only if truly unavoidable). `#print axioms` on all new headline
theorems (scratch file in /tmp; only propext, Classical.choice, Quot.sound). Update README entry points.
