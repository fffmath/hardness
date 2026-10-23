# Research: next formalisation targets for `hardness`

*Written 2026-10-24 (Asia/Shanghai). Scope: what comes after the sorry-free Lean 4
formalisation of "Exact CVP Is NP-Complete for Principal Cyclotomic Ideals"
(arXiv:2608.23828 / ePrint 2026/1793, Liu–Feng–Pan). All links below were fetched
or HTTP-checked (200) on the date above.*

## 0. Current state (from README.md / NOTES.md / paper source)

Already done in Lean (v4.36.0-rc1, Mathlib rev 625d8914; standard axioms only):

| Piece | Main Lean names |
|---|---|
| X3C → principal-ideal CVP in ℤ[y]/(y^d+1) | `x3cToCVP`, `x3c_correct`, `x3c_yes_gap` (Δ), `x3c_no_gap` (Δ+4), `exactCoverEquivClosest` |
| Quotient-ring identification, cyclic lift (8Δ, gap 32) | `Cyclotomic.*`, cyclic files |
| Full rank of principal ideals | `Cyclotomic.principal_full_rank` |
| Module-SIVP corollary | `x3cToModuleSIVP` (Γ = Q² + Δ) |
| Fixed family (CVPP core) | `Fixed.fixed_family_correct`, `fixed_family_correct_indexed` |
| Rational / canonical-embedding versions | `Rational*`, `Canonical*` |
| Certificates for the constructed instances | `verify`, `matrixMap`, `matrixLattice`, `matrix_cvp_iff`, `multiplicationMatrix`, `x3c_bounded_certificate` |
| Explicit size bounds of the compiled instance | `penaltyBound`, `compileX3C`, `compileX3C_size` |

Explicitly **not** formalised: polynomial running time, NP membership as a class
statement, the CVPP ⇒ NP ⊆ P/poly corollary (Karp–Lipton), general certificate-size
bounds for arbitrary integer bases.

## 1. Landscape: related formal work

| Project | System | What it has | Relevance |
|---|---|---|---|
| **CVP_Hardness** (Kreuzer, AFP 2023) — <https://isa-afp.org/entries/CVP_Hardness.html>; paper Kreuzer–Nipkow <https://arxiv.org/abs/2306.08375> | Isabelle | CVP NP-hard in ℓ∞ and every ℓp (p ≥ 1) via Subset Sum (van Emde Boas / Micciancio–Goldwasser Thm 3.1); SVP in ℓ∞ via BHLE→Partition. Reductions as functions + correctness only, no complexity classes. Found errors in textbook proofs. | Closest prior art; same "reduction function + iff" style as ours. A good reference/port for a general-lattice CVP baseline. |
| **descriptive-complexity** (Senellart) — <https://github.com/PierreSenellart/descriptive-complexity>, docs <https://pierresenellart.github.io/descriptive-complexity/> | Lean 4 (v4.35) | Machine-free NP = ∃SO (Fagin), Cook–Levin, `DescriptiveComplexity.exactCover_NP_complete` (from 1-in-SAT), 3DM (`threeDimMatching_mem_NP`, SAT→3DM), Knapsack with binary encoding, Partition, 0-1 IP, PH, #P. FO reductions (no multiplication). | Source of an NP-complete Exact-Cover/3DM in Lean. Our reduction uses convolution/squares, so expressing it as an FO reduction is hard, but every number is polynomially bounded *in value* (see target 3). |
| **complexitylib** (Schlesinger) — <https://github.com/SamuelSchlesinger/complexitylib> | Lean 4 (v4.35-rc3) | Multitape TMs (Arora–Barak), P, NP, `NPHard`/`NPComplete`, `MapReducesPoly` (`Classes/NP/Reduction.lean`, incl. `NPHard.of_reduction`), NP-via-witness (`Classes/NP/Witness.lean`), **Cobham's theorem** (`Classes/P/Cobham.lean`), Cook–Levin, 3SAT NP-complete (`SAT/ThreeSAT/Completeness.lean`), P/poly via circuits and via advice (`Classes/PPoly/Advice/Defs.lean`: `Advice`, `PolynomialAdvice`, `PAdvice`), PCP. No X3C/3DM, **no Karp–Lipton**. | The most direct route to genuine `NPComplete` / P/poly statements. |
| **HardnessReductionsLean** (D. Peters) — <https://github.com/DominikPeters/HardnessReductionsLean> | Lean 4 (v4.32) | Garey–Johnson catalogue: `Sets/ExactCover3.lean` (`IsExactSetCover`), `ExactCover3/FromMatching3D` (+ Certified), `Matching3D/FromSat`, Partition, Knapsack. `Cert/Language.lean`: deep-embedded `Code σ τ` combinator language with bit-length cost and `Code.cost_size_le_polyBound`. No P/NP classes. Uses `namespace Hardness` (clashes with ours). | Template for a machine-free polynomial-time certificate of `compileX3C`; X3C hardness chain (SAT→3DM→X3C). |
| **coq-library-complexity** (uds-psl) — <https://github.com/uds-psl/coq-library-complexity>; Gäher–Kunze ITP 2021 | Coq | Cook–Levin in call-by-value λ-calculus L, poly-time reductions. | Methodological reference for time certification. |
| **poly-reductions** — <https://github.com/wimmers/poly-reductions> | Isabelle | Karp's reductions with verified running time (NREST). | Reference for running-time proofs of reductions. |
| **Cook_Levin** (Balbach, AFP) — <https://isa-afp.org/entries/Cook_Levin.html> | Isabelle | TM-based Cook–Levin. | Reference only. |
| **CSLib** — <https://arxiv.org/abs/2602.04846> | Lean 4 | Complexity theory planned, currently minimal. | Watch; not usable yet. |

Toolchain note: all three Lean projects are on older Lean/Mathlib than ours
(v4.32–v4.35 vs v4.36.0-rc1). **Vendoring/porting the small pieces we need is
more practical than a lake dependency**, and a namespace rename is needed for
HardnessReductionsLean.

## 2. Landscape: related mathematics (2026)

* **Companion paper (same authors): "SVP Is NP-Hard for Some Rank-2 Cyclotomic
  Modules"**, ePrint 2026/1856 — <https://eprint.iacr.org/2026/1856>. X3C → SVP₂
  on full-rank free submodules of 𝒪_K² for K = ℚ(ζ_q), q ≡ 3 mod 4 prime. Uses
  Bennett–Peikert Reed–Solomon lattices mapped into a principal ideal, Wan's
  point-count estimates, a quadratic-Gauss-sum checker, and a coset separation
  bound. Output: prime q, 2×2 generator matrix with nonzero det, threshold.
* **D. E. Martin, "NP-Hardness of Ideal Lattice Problems"**, arXiv:2609.15813 —
  <https://arxiv.org/abs/2609.15813> (ePrint 2026/2003,
  <https://eprint.iacr.org/2026/2003>). Dimension-preserving deterministic
  reduction from general lattices to invertible ideals in totally real monogenic
  orders (canonical embedding). Corollaries: SVP₂ NP-hard within √2, CVP₂ within
  n^{1/2−ε}. Formalisable core: Prop 3.4/3.5 (condition-number transfer and
  exact-integrality rounding), Lemma 3.6.
* **H. Wan, "NP-hardness of SVP in Euclidean Space"**, arXiv:2603.27398 —
  <https://arxiv.org/abs/2603.27398>. Deterministic SVP₂ NP-hardness (settles van
  Emde Boas' 1981 conjecture) via Bennett–Peikert + Deligne. Not formalisable in
  the near term (Weil conjectures).
* **Z. Song, CVP₂ within n^{1/2−ε}**, ePrint 2026/1655 —
  <https://eprint.iacr.org/2026/1655>. Binary affine-code gap lifted to a lattice
  where squared distance = Hamming weight. The lifting step is elementary and
  close to our `sqNorm` machinery.
* **Hair–Sahai, SVP_p deterministic for p > 2**, arXiv:2511.04125 —
  <https://arxiv.org/abs/2511.04125>.
* Classics cited by the paper: van Emde Boas 1981; Micciancio 2001 (CVPP);
  Feige–Micciancio 2004; Regev 2004 / Alekhnovich et al. 2005 (CVPP
  inapproximability); Micciancio 2007 (cyclic lattices); Karp–Lipton 1980.

## 3. Prioritised targets

Difficulty: **E** easy (≤ 1–2 days), **M** medium (≤ 1–2 weeks), **H** hard (weeks+).

### T1. Abstract CVPP ⇒ advice decider (the combinatorial half of cor:cvpp) — **E/M**
*Rationale.* The CVPP corollary is the only main-paper statement with no Lean
counterpart. Its non-complexity core is clean: for any "CVPP scheme" `(Pre, Dec)`
with `Dec (Pre B) t Δ ↔ CVPYes B t Δ`, the mask language
`L = {μ | the X3C instance indexed by μ is a yes-instance}` satisfies
`μ ∈ L ↔ Dec (π_m) (t_μ) (Δ_μ)` with advice `π_m = Pre (B_{g_m})` that depends on
`m` only.
*Statement sketch.* `structure CVPPScheme` (`Pre : basis → Advice`, `Dec`, `spec`);
`theorem cvpp_advice_decides_masks : μ ∈ maskLang m ↔ S.Dec (S.Pre (fixedBasis m)) (target μ) (thr μ)`.
Optional follow-on: state it against complexitylib's `PAdvice` with
"Pre has polynomial-size output and Dec ∈ P" as hypotheses, leaving the
polynomial-time conditions as explicit hypotheses (no Karp–Lipton needed).
*Reuses.* `Fixed.fixed_family_correct_indexed`, `fixed_family_correct`,
`CVPYes`, `exactCoverEquivClosest`, `multiplicationMatrix`/`matrixLattice`
for a concrete basis representation.

### T2. Certificate-size bound for every nonsingular square integer basis — **M**
*Rationale.* Generalises `x3c_bounded_certificate` from constructed instances to
all full-rank integer bases, the standard "CVP ∈ NP" witness bound. Needed for a
real NP-membership statement (T5) and independently interesting.
*Statement sketch.* For `B : Matrix (Fin n) (Fin n) ℤ` with `B.det ≠ 0`, if
`sqNorm (B *ᵥ x - t) ≤ Δ` then such an `x` exists with every
`|x i| ≤ n! · c^(n-1) · (‖t‖∞ + √Δ)` (c = max |B i j|), so `CVPYes` is equivalent to
a bounded `∃ x ∈ box, verify B t Δ x = true`.
*Proof route.* `B.det • x = adjugate B *ᵥ (B *ᵥ x)` (`Matrix.adjugate_mul`,
`Matrix.cramer_eq_adjugate_mulVec`, `Matrix.mulVec_cramer`); bound entries of
`adjugate` with `Matrix.det_le` (Mathlib `LinearAlgebra/Matrix/AbsoluteValue.lean`,
|det| ≤ n!·c^n); `|det B| ≥ 1`. Hadamard is optional (tighter but more work).
Corollary for **all principal ideals** of ℤ[y]/(y^d+1) via
`Cyclotomic.principal_full_rank` + `multiplicationMatrix`.
Extension (**H**): dependent generating sets need HNF / a
von zur Gathen–Sieveking bound.
*Reuses.* `verify`, `matrix_cvp_iff`, `matrixMap`, `matrixLattice`, `sqNorm`,
`CVPYes`, `multiplicationMatrix`, `principal_full_rank`.

### T3. Strong NP-hardness / explicit bit-size theorem — **E**
*Rationale.* `compileX3C_size` already bounds every output coefficient by
`2·penaltyBound (3q) n`, the threshold by `penaltyBound²·n + M n²`, and
`d ≤ 4·(3q)·(8n²+1)`; all are polynomials in (q, n). So the reduction stays
valid under **unary** encoding (strong NP-hardness), which the paper does not say
explicitly. Formalise:
`theorem compileX3C_strong : ∀ I, maxAbsCoeff (compileX3C I) ≤ P (I.q + I.n)` for an
explicit polynomial `P`, plus `Nat.size`/`Nat.log 2` bit-length bounds and a total
output-length bound `encLen (compileX3C I) ≤ P' (encLen I)`. Add `#eval`/`decide`
regression tests on the smoke example (d = 8, Δ = 2116).
*Reuses.* `penaltyBound`, `compileX3C`, `compileX3C_size`, `X3CInstance`.

### T4. Machine-free polynomial-time certificate of `compileX3C` — **M/H**
*Rationale.* Gives a real "polynomial time" theorem without Turing machines.
Port `Cert/Language.lean` (the `Code σ τ` combinators with bit-length cost and
`Code.cost_size_le_polyBound`) from HardnessReductionsLean under a new namespace,
write `compileX3C` as a `Code` term, and prove it agrees with the Lean
function. Use the repo's **cubic Sidon alternative** rather than the
Erdős–Turán prime search, because `Code` has no general recursion (`Nat.find`).
*Reuses.* `compileX3C`, `compileX3C_size` (T3 bounds feed the cost bound), the
cubic Sidon construction, `x3cToCVP`, `x3c_correct`.

### T5. Genuine `NPComplete` for principal-ideal CVP via complexitylib — **H**
*Rationale.* The headline theorem stated with real classes.
Plan: (a) vendor the needed complexitylib pieces or bump it to our Mathlib;
(b) X3C NP-hard: port SAT→3DM→X3C (HardnessReductionsLean `Matching3D/FromSat`,
`ExactCover3/FromMatching3D`) or Exact Cover from descriptive-complexity, on top of
complexitylib's `SAT/ThreeSAT` `NPComplete_language`; (c) CVP ∈ NP via the witness
characterisation (`Classes/NP/Witness.lean`) + T2 + `verify`; (d) `compileX3C` ∈ FP
via **Cobham's theorem** (`Classes/P/Cobham.lean`) and T3/T4 bounds; (e)
`NPHard.of_reduction` / `NPComplete.of_mem_of_reduction`.
This step also opens a P/poly-level CVPP statement (T1 + `PAdvice`); full
Karp–Lipton (NP ⊆ P/poly ⇒ PH = Σ₂) is in no library and stays out of scope.
*Reuses.* everything in T1–T3 plus `x3c_correct`, `X3CInstance`.

### T6. Martin-style transfer lemmas (arXiv:2609.15813, Prop 3.4/3.5, Lemma 3.6) — **M**
Condition-number transfer between a lattice and an ideal, and exact-integrality
rounding, stated over the canonical embedding. Fits the existing
`Canonical*`/`Rational*` files and is a stepping stone toward
"approximate CVP/SVP NP-hard on ideals".
*Reuses.* canonical-embedding versions, `sqNorm`, `principal_full_rank`.

### T7. Companion paper: SVP on rank-2 cyclotomic modules (ePrint 2026/1856) — **H**
Natural "volume 2" for this repo (same authors, same X3C source, module
framework). Elementary, formalisable sub-pieces first: the quadratic-Gauss-sum
checker identity (|g|² = q for q ≡ 3 mod 4; Mathlib has `gaussSum`/`gaussSum_sq`),
the 2×2 generator-matrix nonsingularity, and the coset separation bound. The
Wan/Deligne point-count input should be an explicit hypothesis.
*Reuses.* `x3cToModuleSIVP`, `ModuleSIVP`, canonical-embedding files,
`principal_full_rank`, X3C layer.

### T8. Smaller follow-ups — **E–M**
* **Search-to-decision for CVP** on our instances via `exactCoverEquivClosest`
  (closest vectors ↔ exact covers is already a bijection), giving a constructive
  X3C solver from a closest-vector oracle. **E**
* **Baseline ℓp / ℓ∞ CVP via Subset Sum** (port the reduction from AFP
  CVP_Hardness) as a cross-check of the `sqNorm` API on general lattices. **M**
* **Song-style lifting** (ePrint 2026/1655): binary code → lattice with squared
  distance = Hamming weight; it is elementary and reuses `sqNorm`. **M**
* Gap amplification for approximate CVP from Δ vs Δ+4: gap is only
  1 + O(1/Δ), so tensoring is not natural; **low priority**.

## 4. Recommended order

T3 → T1 → T2 → T8 (search-to-decision) → T4 → T5, with T6/T7 as a parallel
mathematics track. T1–T3 need no new complexity infrastructure and each adds a
theorem the paper states or relies on but the Lean code does not yet have.
