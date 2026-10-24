You are working in the Lean 4 + Mathlib Lake project at /workspace/hardness (library `Hardness`,
toolchain leanprover/lean4:v4.36.0-rc1, Mathlib already built in .lake — do NOT run `lake update`
or `lake exe cache get`, and do not change lakefile.toml / lake-manifest.json / lean-toolchain).
Build with `lake build` from /workspace/hardness. Do not use git (the director commits).

Goal: formalise the core reduction of the paper "Exact CVP Is NP-Complete for Principal Cyclotomic
Ideals" (Liu, Feng, Pan; arXiv:2608.23828). LaTeX source: paper/src/chapter/pre.tex (definitions,
esp. Exact CVP and Definition def:principal-cyclotomic-cvp), paper/src/chapter/principal-ideal.tex
(the whole reduction: masked Boolean system, Lemma lem:sidon, row coordinates, h, t, a_ξ,
Lemma lem:boolean-identity, the "h has W distinct monomials" lemma, s, P, g, T_μ, Δ_μ,
eq. (block-product), Lemma lem:admissible, Theorem thm:compiler, Theorem thm:cyclotomic-cvp).
READ THOSE FILES FIRST and follow the paper's proof.

Priority: the combinatorial/algebraic correctness of the reduction. Polynomial-time complexity
is NOT to be formalised (Mathlib lacks infrastructure); instead put a clearly documented
section/docstring saying which constructions are explicit and of polynomial size (e.g. prove the
size bounds d ≤ poly, or just document them). Never introduce `axiom`s.

Suggested model (you may improve it, but keep definitions honest and faithful):
* `Hardness/X3C.lean`: X3C instance: universe `Fin (3*q)` (or `Fin m`), collection
  `Fin n → Finset (Fin m)` with each card = 3; `HasExactCover`. Masked Boolean system
  (A : Fin M → Fin n → Bool/ℕ in {0,1}, b, μ) and `Feasible`; X3C as the special case
  (A = incidence matrix H, b = 1, μ = 1) with a proved equivalence `HasExactCover ↔ Feasible`,
  and a bijection between exact covers (as sub-collections / index sets) and feasible ξ.
* `Hardness/Lattice.lean`: coefficient vectors `Fin D → ℤ`, squared Euclidean norm
  `sqNorm v = ∑ i, v i ^ 2` (in ℤ), lattice as an `AddSubgroup (Fin D → ℤ)` (or ℤ-span of basis
  vectors), exact decision CVP: `CVPYes L t Δ := ∃ v ∈ L, sqNorm (v - t) ≤ Δ`.
* `Hardness/Cyclotomic.lean`: R_d = ℤ[y]/(y^d+1) for d a power of two. Recommended concrete model:
  elements are coefficient vectors `Fin d → ℤ` with negacyclic multiplication
  (y^i * y^j = ± y^{(i+j) mod d}), so the coefficient embedding is the identity; principal ideal
  lattice (g) = { g * q | q } as an AddSubgroup. If convenient, ALSO relate it to
  `Polynomial ℤ ⧸ Ideal.span {X^d + 1}` (nice to have, lower priority).
* `Hardness/Sidon.lean`: Lemma lem:sidon — the Erdős–Turán construction α_j = 2p(j-1) + ((j-1)^2 mod p)
  with p an odd prime in [n,2n) (Bertrand: `Nat.exists_prime_lt_and_le_two_mul` or similar);
  prove strict monotonicity, α_1 = 0, and distinctness of nonzero ordered differences.
  (If the full Sidon proof is hard, it's acceptable to first take the Sidon property as a
  hypothesis structure on α and prove the reduction relative to any such α, then prove the
  construction satisfies it.)
* `Hardness/Reduction.lean`: c, L, ρ_i, W, ν, N, h, t, a_ξ, u_μ, s, P, g, T_μ, Δ_μ exactly as in
  the paper; Lemma lem:boolean-identity; the distinct-monomials lemma for h; eq. (block-product);
  Lemma lem:admissible (both parts: = Δ_μ + 4‖Aξ−b‖² for Boolean ξ ≤ μ, and > Δ_μ + 4 otherwise);
  Theorem thm:compiler's correctness: YES ⇒ ∃ lattice vector at squared distance exactly Δ_μ
  (and min squared distance = Δ_μ, i.e. every lattice vector has squared distance ≥ Δ_μ);
  NO ⇒ every lattice vector has squared distance ≥ Δ_μ + 4; g ≠ 0.
* `Hardness/Main.lean`: the X3C → principal cyclotomic CVP reduction as a function
  `x3cToCVP : X3CInstance → (d, g, T, Δ)` with `d` a power of two, and the main theorem
  `HasExactCover I ↔ CVPYes (principalIdealLattice g) T Δ` plus the gap statement
  (YES ⇒ min dist² = Δ, NO ⇒ min dist² ≥ Δ+4), plus the bijection/correspondence between exact
  covers and lattice points at distance exactly Δ (ξ ↦ g * a_ξ(y²)) if feasible.
Import all files from Hardness.lean (replace the placeholder Hardness/Basic.lean as you like).

Rules: work incrementally and run `lake build` often (you can also check single files with
`lake env lean Hardness/Foo.lean`). The finished state must build with `lake build`.
Use `sorry` only as a temporary placeholder; at the end, list every remaining `sorry` in
NOTES.md with an explanation. Also write NOTES.md describing the file layout, the main
definitions/theorems with their Lean names and the paper's lemma numbers they correspond to.
Prefer proving things over stating them; avoid vacuous definitions. Keep going until the main
theorem chain (through Lemma lem:admissible and the main X3C theorem) is sorry-free, or you run
out of ideas.
