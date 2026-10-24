You are continuing work in the Lean 4 + Mathlib Lake project at /workspace/hardness (library
`Hardness`, toolchain leanprover/lean4:v4.36.0-rc1, Mathlib already built — do NOT run
`lake update` / `lake exe cache get`, do not change lakefile.toml / lake-manifest.json /
lean-toolchain, do not use git). Read NOTES.md and README.md first: rounds 1–3 proved the
X3C → principal cyclotomic CVP reduction, quotient/cyclic forms, general full rank,
module-SIVP (ModuleSIVP.lean) and the fixed family (Fixed.lean), all sorry-free.
Keep everything building and sorry-free; never add `axiom`.

IMPORTANT build hygiene: always wrap builds in a timeout, e.g.
`timeout 900 lake build` / `timeout 600 lake env lean Hardness/Foo.lean`. If a `simp` or
`decide` blows up (maxRecDepth / heartbeats), replace it by explicit `rw`/`simp only` steps
instead of retrying. Prefer new files over large edits of existing proven files.

Paper source: paper/src/chapter/pre.tex (Exact CVP with rational data, lem:canonical,
componentwise canonical norm), principal-ideal.tex, sivp-module.tex, fixed.tex.

Round 4 tasks, in priority order (easy to hard):

1. §fixed ↔ indexed X3C. Prove that the set-of-triples input of Fixed.lean is faithful to the
   indexed `X3CInstance` (Hardness/X3C.lean; triples : Fin n → Finset (Fin (3*q)), possibly
   repeated). Define `X3CInstance.toTripleSet : Finset (Fixed.Triple (3*q))` (image of the
   indexed triples) and prove `I.HasExactCover ↔ Fixed.HasExactCover I.toTripleSet`
   (repeated triples can never both be selected in an exact cover since triples are nonempty;
   choose one index per used triple for the converse). Then a corollary
   `fixed_family_correct_indexed : I.HasExactCover ↔ CVPYes (Fixed.lattice (3*q) _) (Fixed.target ..)
   (Fixed.threshold ..)` (needs 3 ≤ 3*q from q_pos), plus yes/no gap versions.
   File: Hardness/FixedIndexed.lean.

2. Rational data. The paper's exact CVP takes rational target and rational threshold, and
   principal cyclotomic CVP takes T ∈ K_d. Formalise this honestly and reduce to the integral
   case by a proved scaling lemma:
   - Define rational decision-CVP for an integral (ℤ-submodule / AddSubgroup) lattice
     L ⊆ (Fin m → ℤ) with target t : Fin m → ℚ and threshold Δ : ℚ:
     ∃ v ∈ L, ∑ (t i - v i)^2 ≤ Δ  (cast to ℚ).
   - Scaling lemma: for N : ℕ, N > 0, the rational instance (L, t, Δ) is YES iff the rational
     instance (N•L, N•t, N²Δ) is YES; and if N•t is integral (N a common denominator) this is
     the integral instance with integer threshold ⌊N²Δ⌋ (prove the floor step: integer sqNorm ≤ x
     ↔ ≤ ⌊x⌋). Also the converse embedding: integral instances are rational instances with the
     same answer (casting), so all existing hardness theorems (x3c_correct etc.) hold verbatim for
     the rational problem — state `x3c_correct_rational`.
   - Analogously for principal cyclotomic CVP with T ∈ K_d (coefficients in ℚ, e.g. Fin d → ℚ or
     the AdjoinRoot / ℚ[X]/(X^d+1) used in ModuleSIVP as `K d`) and for module-SIVP with a
     rational threshold (Γ : ℚ, λ₂² ≤ Γ ↔ λ₂² ≤ ⌊Γ⌋ since norms are integers on integral
     modules). If arbitrary rational module bases (b1, b2 ∈ K_d²) are claimed by the paper, give
     at least the definition and the scaling-to-integral lemma (multiply both basis vectors by a
     common denominator N: squared norms scale by N², independence preserved).
   File: Hardness/Rational.lean.

3. Canonical embedding (lem:canonical). Let d = 2^k ≥ 1, ζ := Complex.exp (π i / d) (primitive
   2d-th root of unity; Mathlib: `Complex.isPrimitiveRoot_exp`). For f with coefficient vector
   c : Fin d → ℚ (or ℤ, or ℝ), σ_k(f) := ∑_r c r * ζ^((2k+1) r), k < d. Prove
       ∑_{k<d} ‖σ_k(f)‖² = d * ∑_r (c r)²
   via orthogonality ∑_{k<d} ζ^{(2k+1)(r-s)} = d·[r=s] for 0 ≤ r,s < d (geometric sum with ratio
   ζ^{2(r-s)} ≠ 1 when r ≠ s, |r-s| < d, ζ^2 primitive d-th root; when r ≠ s ζ^{2d(r−s)}=1).
   Also show σ_k is well defined on R d / K d (it is evaluation at the root ζ^{2k+1} of X^d+1,
   so ring hom: σ_k(fg) = σ_k f σ_k g) — at least that the representative-based definition
   agrees with `Polynomial.aeval` modulo X^d+1. Then transfer: canonical squared distance
   = d · coefficient squared distance for every target and principal ideal; restate
   x3c_correct / yes-gap / no-gap and module-SIVP yes/no with all thresholds multiplied by d
   (componentwise version for pairs). File: Hardness/Canonical.lean.

4. If feasible (skip heavy complexity-class infrastructure):
   (a) NP-membership in certificate form for exact decision-CVP on integer lattices given by a
       basis matrix B : Matrix (Fin m) (Fin n) ℤ: YES ↔ ∃ x : Fin n → ℤ, sqNorm (B x − t) ≤ Δ;
       a computable `Bool` verifier `verify B t Δ x` with `verify = true ↔ sqNorm (B x - t) ≤ Δ`;
       and the certificate-size statement: if YES, there is a witness x with entries bounded
       polynomially is HARD in general — instead, for the full-rank square case or for the
       produced instances, give an explicit witness bound (e.g. for x3cToCVP YES instances the
       witness is the explicit quotient from the cover with explicit coefficient bound). Only do
       what is provable cleanly.
   (b) A computable version of the reduction map (instance data as lists/functions of ℤ) with
       explicit size bounds on output dimension and coefficient magnitudes in terms of q, n
       (dimension bound already exists: x3c_dimension_le). Do not formalise Turing machines.

Rules: run builds with timeouts; finished state must build with `timeout 1500 lake build`.
No `sorry` in finished parts — if a task cannot be finished, remove/comment out the unfinished
part and list it in NOTES.md. Run `#print axioms` on all new main theorems in a scratch file
under /tmp (only propext/Classical.choice/Quot.sound). Update NOTES.md (layout, Lean names ↔
paper numbers, round-4 changes, remaining gaps), add new files to Hardness.lean, and update
the "Main entry points" list in README.md.
