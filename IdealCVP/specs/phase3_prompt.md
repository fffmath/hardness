You are continuing work in the Lean 4 + Mathlib Lake project at /workspace/hardness (library
`Hardness`, toolchain leanprover/lean4:v4.36.0-rc1, Mathlib already built — do NOT run
`lake update` / `lake exe cache get`, do not change lakefile.toml / lake-manifest.json /
lean-toolchain, do not use git). Read NOTES.md and README.md first: rounds 1–2 proved the
X3C → principal cyclotomic CVP reduction (Main.lean), its quotient-ring form (Quotient.lean),
the Erdős–Turán Sidon lemma (Sidon.lean) and the cyclic extension (Cyclic.lean), all sorry-free.
Keep everything building and sorry-free; never add `axiom`.

Paper source: paper/src/chapter/principal-ideal.tex, sivp-module.tex, fixed.tex, pre.tex.
Round 3 tasks, in priority order:

1. General full rank (no injectivity hypothesis).
   (a) For d a power of two (d = 2^k, k ≥ 0... handle d = 1 too, or require d ≥ 1) prove
       X^d + 1 = cyclotomic (2d) ℤ (Mathlib: `Polynomial.cyclotomic_prime_pow_eq_geom_sum`,
       `cyclotomic_two_pow`-style lemmas, or via `X^(2d) - 1 = (X^d - 1)(X^d + 1)` and
       `prod_cyclotomic_eq_X_pow_sub_one`), and hence it is irreducible over ℚ / ℤ
       (`Polynomial.cyclotomic.irreducible`, `cyclotomic.irreducible_rat`). Conclude that
       `Polynomial ℤ ⧸ Ideal.span {X^d+1}` is an integral domain (prime ideal: monic irreducible,
       primitive; or embed into ℚ[X]/(X^d+1) = AdjoinRoot, a field, via the coefficient basis).
   (b) Deduce: for every nonzero g : R d (d a power of two), `Cyclotomic.mul g` is injective,
       and `principalIdealLattice g` has a ℤ-basis of size d (the multiplication basis) —
       a theorem `principal_full_rank` with no injectivity hypothesis. Replace / complement
       `ReductionData.mul_injective`-based arguments where natural.
   (c) Lemma lem:principal-crt claims J = (G) is full rank for any nonzero g, any B with
       B^2 > 4H. Remove the explicit injectivity hypothesis from Cyclic.multiplicationBasis
       (or add a hypothesis-free corollary) using (b) — follow the paper's proof
       (Q = p + X^d q, r = p+q, z = p−q decomposition) or whatever works.

2. Module-SIVP chapter (sivp-module.tex): Definition def:module-sivp, Lemma
   lem:module-completion, Theorem thm:module-sivp (the reduction correctness, not NP membership /
   runtime). Suggested model: module elements as pairs (R d × R d) with coefficient embedding
   into `Fin d ⊕ Fin d → ℤ` or `R d × R d` with sqNorm = sum of both; M_{Q,g,T} = {(Q a, T a + g b)}
   as an AddSubgroup; K_d-linear dependence: two vectors (u1,u2), (v1,v2) are K_d-dependent iff
   u1*v2 − u2*v1 = 0 in R d (justify this via the domain/field structure from task 1, or define
   it this way and prove the equivalence with the AdjoinRoot ℚ field-span definition — the
   honest definition is via span over K_d = ℚ[X]/(X^d+1); prefer proving equivalence).
   Define λ₂²-statements without infima, e.g. `SecondMinimumSq M Γ` := there exist two
   K_d-independent vectors of M with sqNorm ≤ Γ (decision version: λ₂² ≤ Γ), and the exact value
   statement (∃ two independent with max sqNorm = r², and every pair of independent vectors has
   max sqNorm ≥ r²). Prove lem:module-completion: λ₂² = Q² + dist(T,(g))², including the
   ±y^j case (sqNorm a = 1 ⇒ a = ± monomial, a unit, multiplication isometry — Norms.lean has
   `sqNorm_monomial_mul`), freeness/basis (Q,T),(0,g). Then thm:module-sivp for x3cToCVP
   with Q := 1 + ceilSqrt(max ‖T‖², ‖g‖²), Γ := Q² + Δ: YES ⇒ λ₂² = Γ, NO ⇒ λ₂² ≥ Γ + 4, and
   HasExactCover ↔ decision YES. File: Hardness/ModuleSIVP.lean.

3. If time allows: §fixed (fixed.tex) Theorem thm:fixed-family, combinatorial content only:
   for universe size m ≥ 3, the matrix U_m of all 3-subsets (k_m = choose m 3 columns, any fixed
   enumeration, e.g. `(Finset.univ : Finset (Fin m)).powersetCard 3` via an equiv with
   Fin (choose m 3)), mask μ from a collection; prove the X3C instance has an exact cover iff
   the masked system (U_m, 1, μ) is feasible, and that the generator g / lattice / basis of the
   resulting CVP instance depend only on m (use `generator_mask_independent`), with only T_μ, Δ_μ
   depending on the collection; YES/NO gap. Skip CVPP / P/poly / Karp–Lipton. File:
   Hardness/Fixed.lean. (Collections with repeated triples can be reduced to sets of triples.)

Rules: run `lake build` often (single files: `lake env lean Hardness/Foo.lean`); finished state
must build. No `sorry` in finished parts — list any remaining in NOTES.md. Run `#print axioms`
on all new main theorems in a scratch file under /tmp (only propext/Classical.choice/Quot.sound).
Update NOTES.md (layout, Lean names ↔ paper numbers, round-3 changes, remaining gaps) and the
"Main entry points" list in README.md.
