You are continuing work in /workspace/hardness (Lean 4 v4.36.0-rc1 + Mathlib + complexitylib
@ ba134c18 under .lake/packages). Do NOT run `lake update`/`lake exe cache get`, do not change
lakefile/manifest/toolchain, do not use git. Builds: use
`LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 1500 lake build` and
`LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 900 lake env lean <file>`.
No `sorry` in finished code, no `axiom`, no `native_decide` in theorems.

Read NOTES.md (Rounds 6–7) and Hardness/Complexity/*.lean first. State: the unconditional
`principalCVP_npComplete : NPComplete encCVP PrincipalCVP` is proved via
complexitylib ExactThreeSAT → MaskedSys (SatToMasked.lean, 1-in-3 gadget) → compileFast → CVP.
`principalCVP_npHard_of_X3C` (NPComplete.lean) is the paper's route, conditional on X3C hardness.

ROUND 8 GOAL: X3C is NP-complete in complexitylib terms, and the paper's route is discharged.
1. Define a list-level X3C problem, e.g. `X3CList := ℕ × List (ℕ × ℕ × ℕ)` (q in unary, triples of
   universe elements < 3q; malformed/degenerate inputs are NO or handled explicitly), `encX3C`
   (complexitylib encodings), `X3CLang : Set X3CList`, and a bridge to the existing
   `X3CInstance.HasExactCover` (X3C.lean; note q>0, n>0 there — handle q=0/n=0 explicitly) and to
   `Fixed.HasExactCover` if convenient.
2. `X3CLang ∈ NP encX3C` (certificate = Boolean selection list; template: SubsetSum/ZeroOneIP
   mem_NP in complexitylib, and Hardness/Complexity/Verifier.lean / Witness.lean).
3. NP-hardness: `PolyTimeReducible encCNF encX3C ExactThreeSAT X3CLang` (or from our `MaskedSys`
   produced by satToMasked, or from complexitylib's ThreeSAT/SAT — whichever is cheapest), via the
   classical 3SAT → 3DM → X3C (Garey–Johnson Thm 3.2 / 3DM ⊂ X3C) or a direct gadget. A semantic
   (correctness-only, no polytime) Apache-2.0 reference is cloned at /tmp/sundogcert
   (Sundogcert/SATReduction*.lean, VarWheel.lean, ClauseGadget.lean, MatchingNPHard.lean, Lean v4.30 —
   do not import it, port ideas only, credit it in NOTES.md). Prove correctness both directions and
   polytime via fun_prop / explicit composition (as in SatToMasked.lean and CompileFastPolyTime.lean).
   Then `x3c_npComplete : NPComplete encX3C X3CLang`.
4. X3C → PrincipalCVP polytime reduction following the paper: a list-level compiler (reuse
   compileFast: X3C → MaskedSys is just the incidence matrix with rhs all-true, mask all-true, so
   `compileFast ∘ x3cToMasked` works) with correctness and polytime; then
   `principalCVP_npHard_via_X3C : NPHard encCVP PrincipalCVP` proved through `x3c_npComplete`
   (and, if the types fit, discharge `principalCVP_npHard_of_X3C`'s hypotheses or add a list-level
   analogue of it).
5. If cheap: principal CYCLIC-ideal CVP (Cyclic.lean: lift to ℤ[X]/(X^{2d}−1), squared distances
   ×8) as a complexitylib problem `PrincipalCyclicCVP`, NP membership (certificate bound: the cyclic
   multiplication matrix may be singular — use the full-rank basis from Cyclic.lean, or a direct
   argument; skip membership if it is not cheap and say so) and NP-hardness via a polytime lift of
   compileFast's output (`principalCyclicCVP_npHard`, ideally `_npComplete`).

Work incrementally; after each item: build, record in NOTES.md (Round 8 section) with exact
theorem names. If an item cannot be finished, leave only finished building code and document
precisely what is missing (a clearly named hypothesis is acceptable only if truly unavoidable).
Run `#print axioms` on all new headline theorems (scratch file in /tmp; only propext,
Classical.choice, Quot.sound). Update README main entry points.
