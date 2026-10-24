You are continuing work in /workspace/hardness (Lean 4 v4.36.0-rc1 + Mathlib + complexitylib
@ ba134c18 under .lake/packages). Do NOT run `lake update`/`lake exe cache get`, do not change
lakefile/manifest/toolchain, do not use git. Builds: the default artifact cache may be read-only
in your sandbox, so use `LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 1500 lake build` and
`LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 900 lake env lean <file>`.
No `sorry` in finished code, no `axiom`, no `native_decide` in theorems.

Read NOTES.md "Round 6" (all of it) and the Hardness/Complexity/*.lean files first.
State: `principalCVP_npComplete` (Hardness/Complexity/NPComplete.lean) is proved conditional on
exactly one hypothesis
    hcompilePoly : ComputableTidilyInPolyTime compileList encMasked encCVP
for the reference compiler in CompileList.lean (which evaluates Fin/Finset-based ReductionData
with Nat.find prime search and subtype cardinalities — hard to certify).

ROUND 7 GOAL: make the headline UNCONDITIONAL:
    theorem principalCVP_npComplete : NPComplete encCVP PrincipalCVP
(keep the conditional version under a new name, e.g. `principalCVP_npComplete_of_compilePoly`,
or delete it). Strategy (you may deviate if you find something simpler):

1. You are free to change WHICH compiler is used. Correctness only needs SOME `ReductionData`
   per masked system: `ReductionData.compiler_correct` holds for ANY `SidonPositions n`.
   Use `SidonPositions.cubic` (Sidon.lean: α_j = (2n²+1)j + j², c ≤ 3n³+n — plain polynomial
   arithmetic, no prime search) instead of `erdosTuran`. Define
   `S.reductionDataCubic : ReductionData (rows+1) (cols+1)` with the padded system, and a new
   list-level compiler `compileFast : MaskedSys → CVPInput` written ONLY with list/nat/int
   primitives that complexitylib's polytime API certifies (List.range / map / ofFn-style
   patterns, List.any / countP / foldl / sum, binary + − * on ℕ/ℤ, comparisons, unary loops):
     * M = rows.length+1, n = cols+1, padded A/b/μ as lists;
     * α_j, c, L = 2c+1, ρ_i = c + i·L, hExp i j = ρ_i − α_j, crossExp i j k = hExp i j + α_k;
     * N = 2^(clog₂ (M·L)) — compute as the least power of two ≥ M·L by a bounded unary loop
       (M·L is polynomial in the input size, so unary is fine) — d = 2N;
     * h_r = 1 if ∃ (i,j) with A i j ∧ hExp i j = r else 0, for r < N (List.any over ranges);
       t_r = 2·b_i if r = ρ_i, 1 if r = crossExp i j k for some entry (i,j) with k ≠ j, else 0;
       u_r = bit μ_j if r = α_j else 0;
     * W = countP of true entries, ν = (n−1)·W, s = ceilSqrt (n+4), P as in Reduction.lean
       (ceilSqrt via a bounded unary search or complexitylib's sqrt if available; arguments are
       polynomially bounded), weight = countP μ, Δ = P²·weight + ν;
     * g = interleave (2h) (…as in Reduction.lean `g`…), T = interleave t (P·u), as lists.
   Prove the bridge `compileFast S = toCVPInput S.reductionDataCubic.toPrincipalCVPInstance`
   (well-formed S; malformed → cvpNoInput) by pointwise coefficient equality, using injectivity
   facts from Coordinates.lean (hExp_injective, crossExp_injective, row_ne_cross, row_injective)
   to identify `sparse` coefficients with the List.any characterisations. Then
   `compileFast_correct : S.Feasible ↔ compileFast S ∈ PrincipalCVP` (reuse compileList_correct's
   proof pattern with the cubic data).
2. Certify `ComputableTidilyInPolyTime compileFast encMasked encCVP` with fun_prop / explicit
   composition, as was done in SatToMasked.lean and Verifier.lean (which already handle nested
   list lookups — reuse their helper lemmas and the `attribute [local irreducible] List.getD`
   trick). Size contracts: all numbers are polynomial in (rows, cols) — StrongBounds /
   SizeBounds have the pattern; with cubic positions c ≤ 3n³+n.
3. Then `polyTimeReducible_Masked_CVP` unconditionally, `principalCVP_npHard`,
   `principalCVP_npComplete` unconditional. `#print axioms` must show only propext,
   Classical.choice, Quot.sound.

Work incrementally: first the defs + bridge (file CompileFast.lean, CompileFastBridge.lean), build,
record in NOTES.md (Round 7 section); then the runtime certificate (CompileFastPolyTime.lean),
build, record; then the headline. If the runtime certificate cannot be completed, keep the
headline conditional on the smallest clearly named hypothesis about compileFast (or about a
single sub-function), and document precisely which piece is missing. Add smoke checks
(`#eval compileFast` on tiny systems, compare with compileList's output dimension/threshold
semantics) under /tmp. Update README main entry points and NOTES.md.
