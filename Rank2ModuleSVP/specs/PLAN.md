# Rank2ModuleSVP — formalisation plan

Paper: Liu–Feng–Pan, *SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules*, arXiv:2609.01469
(= IACR ePrint 2026/1856). Source: `paper/src/chapter/{pre,descent,representative,reduction}.tex`.

## Main theorem (Thm 1.1 / `thm:main-intro`)
As q ranges over primes ≡ 3 (mod 4), decision-SVP (ℓ₂, canonical embedding) on full-rank free
rank-2 submodules of O_K², K = ℚ(ζ_q), is NP-complete under deterministic polytime many-one
reductions. Instance: (q, m₁, m₂ ∈ O_K² in power basis, det ≠ 0, integer squared threshold Ŝ).
Corollary: search-SVP NP-hard under polytime Turing reductions.

## Reduction (X3C → rank-2 module SVP)
- Parameters: k = ⌊q^{1/1000}/2⌋, h = ⌊201k/200⌋, T = ⌊q^{1/2000}⌋, H = h(q−h), L = 2kq.
- Ideal a = π^k O_K (π = 1−ζ) = image of the lifted Reed–Solomon lattice L_{q,k} (Thm descent);
  λ₁(a)² ≥ 2kq via Bennett–Peikert Thm 14 (λ₁(L_{q,k})² ≥ 2k).
- Centre c = h + π^{⌊k/2⌋}; binary weight-h representatives of c + a with prescribed Sidon
  coordinates exist (Wan's power-sum point counts, Prop 2.3) and can be made "clean".
- Checker: Gauss sum ϑ (ϑ² = −q), p = Σ_{(i,j)∈I}(ζ^{d_ij}+ζ^{−d_ij}), U = 1 + ϑp/q,
  D = −3Σζ^{α_j}, V = −D/(q − ϑp); ‖U v_x − V‖² = B₀ + 2‖Aξ−1‖² + E(x), E ≥ 0, E = 0 if clean.
- Module M = O_K(Uπ^k, 0) + O_K(Uc − V, −Γ), Γ ≈ sqrt(99L/(200(q−1))), threshold S = B₀ + Γ²(q−1).
  Soundness by 4 cases on w (0 / root of unity / short non-unit, coset separation Thm robust-center /
  long). Clear denominators by ρ = q|N(q−ϑp)|. Isolated elements → fixed NO instance over ℤ[ζ₃].
- q: a prime ≡ 3 mod 4 in [X, 2X], X = max(X₀, (ℓ+2)^{C₀}) found by scanning + primality testing.

## Non-elementary inputs (cited in the paper, not proved there)
1. Wan's power-sum point-count estimates (Prop `prop:wan-power-sum-estimates`) — Weil-type bounds.
   → named hypothesis `WanPowerSumEstimates` (a `Prop`, never an `axiom`), stated exactly as in the paper.
2. Primes ≡ 3 (mod 4) in every dyadic interval [Y, 2Y], Y ≥ X₀ (PNT in APs).
   → named hypothesis `PrimesThreeModFourDyadic` unless provable cheaply.
3. Bennett–Peikert Thm 14 (λ₁(L_{q,k})² ≥ 2k for 1 ≤ k ≤ q/2) — elementary (Newton identities);
   attempt a proof, fall back to a named hypothesis `BennettPeikertMinimum`.
Everything else must be proved. Headline theorems take the remaining hypotheses explicitly; NP
membership must be unconditional.

## Lean model
- Index set ZMod q; q-coordinate vectors `ZMod q → ℤ` (or ℚ) with cyclic convolution
  = ℤ[X]/(X^q−1); O_K = quotient by the all-ones vector (Φ_q). Canonical form
  ⟨x,y⟩ = q Σ x_a y_a − (Σx)(Σy) (Lemma cyclotomic-form), invariant under adding constants.
- Bridge theorem (faithfulness): for the evaluation x ↦ Σ x_a ζ^a into `CyclotomicField q ℚ`/ℂ,
  Σ_σ |σ(x)|² equals the form. Put in its own file.
- Module vectors are pairs; nonzero ⇔ positive norm.

## Phases
1. Prime cyclotomic model + norm identities, roots of unity / second shell, sparse tools (i)/(ii),
   Gauss sum identities; problem language `Rank2ModuleSVP` (and well-formedness) stated.
2. Descent: L_{q,k} ↔ π^k O_K, coset-syndrome bijection, binary shell, BP minimum, robust centre.
3. Checker: offset separation, U/V, exact checker-score identity, E ≥ 0, E = 0 for clean x.
4. Completions: from `WanPowerSumEstimates` derive uniform completion counts, fixed-coordinate ratio,
   existence of clean completions (union bound), checker interface corollary.
5. Gap lemma + completeness/soundness (Thm exact-X3C-encoding), denominator clearing, integrality of Ŝ.
6. Complexity: encoding, NP membership (reuse IdealCVP certificate bounds), polytime reduction
   (prime search, parameter computation), `rank2ModuleSVP_npHard_of …`, `…_npComplete_of …`,
   search-SVP Turing corollary; bridge to complex canonical embedding.
