You are continuing work in the Lean 4 + Mathlib Lake project at /workspace/hardness (library
`Hardness`, toolchain v4.36.0-rc1). Do NOT run `lake update` / `lake exe cache get`, do not
change lakefile.toml / lake-manifest.json / lean-toolchain, do not use git.
NEW: the project now depends on complexitylib (cslib-community/complexitylib @ ba134c18,
sources under .lake/packages/complexitylib, already built). `Hardness/Complexity/Smoke.lean`
shows that a plain (non-`module`) Hardness file can `import Complexity....` and use
`Cslib.Complexity.ExactThreeSAT_npComplete : NPComplete encCNF ExactThreeSAT`.

Read first: NOTES.md, README.md, specs/research_complexity.md (THE PLAN — follow §3), and in
complexitylib: AGENTS.md / README.md / ROADMAP.md, Complexity/Computability/Complexity/Reduction.lean
(PolyTimeReducible, NPHard, NPComplete, NPHard.trans), the NP / verifier definitions
(grep for `def NP`, `IsVerifier`, `Witness`), Problems/ExactThreeSAT.lean, Problems/SubsetSum.lean
(+ SubsetSum/*.lean: the template for mem_NP, a list-level reduction and its polytime proof via
`fun_prop`/`polytime`, lines ~594–664), and the encodings (`encNat`, `encIntBin`, `encList`,
`encPair`, `encCNF`). Rounds 1–5 of Hardness are sorry-free; keep it that way. Never add
`axiom`, never `sorry` in finished code, no `native_decide` in theorems.

Build hygiene: always wrap builds in a timeout (`timeout 1500 lake build`,
`timeout 900 lake env lean Hardness/Complexity/Foo.lean`). If a tactic blows up, replace it by
explicit steps. Put all new files under Hardness/Complexity/ and import them in Hardness.lean.

GOAL (headline): `theorem principalCVP_npComplete : NPComplete encCVP PrincipalCVP` where
PrincipalCVP is exact decision-CVP on principal ideals of ℤ[y]/(y^d+1), d a power of two, with
binary-encoded integer data — via ExactThreeSAT →(1-in-3 gadget) masked system →(our compiler,
Hardness/Main.lean `ReductionData.compiler_correct`, valid for ANY MaskedSystem with M,n>0) → CVP,
and NP membership via Hardness/CertificateBound.lean (`principal_cvp_iff_bounded_certificate`,
`certificateBound`). If some piece genuinely cannot be finished, state the headline conditionally
on a CLEARLY NAMED hypothesis (e.g. `(hpoly : ComputableTidilyInPolyTime compileList encMasked
encCVP)`) — never an axiom — and document it in NOTES.md.

Milestones, in order. Finish, build and record each in NOTES.md (round-6 section) before the next,
so partial progress is usable:

M1. Problem.lean: `CVPInput`, `encCVP`, `PrincipalCVP : Set CVPInput` as in research §3.3
    (pick unary or binary for d, whatever fun_prop handles best; integers via encIntBin), list↔Fin
    bridge (`ofList`, `toList`), and `principalCVP_iff : x ∈ PrincipalCVP ↔ (well-formed ∧
    CVPYes (principalIdealLattice (ofList g)) (ofList T) Δ)`. Also a `MaskedSys` list type
    (rows : List (List Bool), rhs, mask, number of columns) with `encMasked`, semantics
    `MaskedSys.Feasible` and a bridge to Hardness `MaskedSystem M n` / `HasSolution`.

M2. SatToMasked.lean: ExactThreeSAT → MaskedSys via the 1-in-3 gadget (research §3.4 item 2:
    per variable columns x_v, x̄_v with row x_v + x̄_v = 1; per clause 4 fresh columns and three
    1-in-3 rows; check the gadget carefully — the clause (l1∨l2∨l3) is satisfiable iff the three
    rows have a 0/1 solution; repeated literals and literals of the same variable in one clause
    must be handled; prove both directions). Mask all-true. Handle degenerate inputs (no clauses /
    no variables / malformed clause lengths) so that M,n>0 when needed (e.g. pad with a dummy
    always-satisfiable row+column, or map malformed formulas to a fixed NO instance).
    Prove `φ ∈ ExactThreeSAT ↔ satToMasked φ ∈ MaskedSys.Feasible` and
    `PolyTimeReducible encCNF encMasked ExactThreeSAT {S | S.Feasible}` (polytime via fun_prop,
    following SubsetSum's pattern). Hence `maskedSys_npHard`.

M3. Verifier / NP membership (Witness.lean): `PrincipalCVP ∈ NP encCVP` using a certificate
    = list of d integers bounded by certificateBound (bit length polynomial in the input: prove
    an explicit polynomial bit-size bound for certificateBound in terms of encCVP length), and
    a list-level negacyclic product proved equal to Cyclotomic.mul. Use complexitylib's
    witness/verifier API and SubsetSum.mem_NP as template. g = 0 case: lattice {0}.

M4. CompileList.lean + CompileBridge.lean: a computable list-level compiler
    `compileList : MaskedSys → CVPInput` (Erdős–Turán positions via a bounded prime search,
    hExp/crossExp positions, sparse vectors, interleave, P, Δ — mirror Reduction.lean /
    Sidon.lean / Coordinates.lean definitions; count with List.countP instead of Fintype.card)
    and the bridge `compileList S = toCVPInput (ReductionData of S)` for well-formed S with
    M,n>0 (and a fixed NO/YES output for degenerate S), giving
    `S.Feasible ↔ compileList S ∈ PrincipalCVP`. This is the biggest piece: plan the
    index bookkeeping carefully; prefer proving pointwise coefficient equality via List.getD /
    List.ofFn.

M5. CompilePolyTime.lean: `ComputableTidilyInPolyTime compileList encMasked encCVP` via
    fun_prop / polytime, tagging helpers. Size bounds from StrongBounds/SizeBounds generalised
    to ReductionData may be needed.

M6. NPComplete.lean: `principalCVP_npHard`, `principalCVP_npComplete` (unconditional if M1–M5
    are done, otherwise with named hypotheses), plus `principalCVP_npHard_of_X3C`-style
    statement if cheap. `#print axioms` (scratch file in /tmp) must show only propext,
    Classical.choice, Quot.sound.

Rules: finished state must build with `timeout 1500 lake build`. No `sorry`: if a milestone cannot
be finished in this run, leave only finished, building lemmas in the file (move unfinished work
into a comment block or delete it) and record exactly what is missing in NOTES.md. Update README
"Main entry points" with whatever lands.
