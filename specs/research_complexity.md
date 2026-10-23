# Complexity layer for `hardness`: what exists and what to do

Research date: 2026-10-24. Scope: how to state and prove, in Lean 4 + Mathlib
(our pin: `leanprover/lean4:v4.36.0-rc1`, Mathlib `625d8914…` = tag `v4.36.0-rc1`),
that exact decision-CVP on principal cyclotomic ideal lattices is NP-complete, plus
optional CVPP / P/poly. Every repo below was checked with `gh api` or a shallow clone
in `/tmp/rs`.

## 0. TL;DR

* **Use `cslib-community/complexitylib`** (Apache-2.0, built on `leanprover/cslib`).
  It pins **the same Lean toolchain (v4.36.0-rc1) and the exact same Mathlib commit
  (`625d8914199bc567cca9b91f90e8e5afafa5ae51`)** as this repo. Its `Complexity/`
  tree has 0 `sorry` and 0 `axiom`. It already provides:
  * multitape-TM polynomial time (`ComputableTidilyInPolyTime`, which is equivalent to
    cslib's `Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength` plus
    `PolynomiallyBounded`),
  * `NP`, `IsVerifier`, `PolyTimeReducible`, `NPHard`, `NPComplete`, and `NPHard.trans`,
  * **Cook–Levin** (`SAT`, `ThreeSAT_npComplete`, `ExactThreeSAT_npComplete`), plus
    `SubsetSum`, `Partition`, `Knapsack`, `ZeroOneIP`, Clique/VC/HamCycle/TSP NP-complete,
  * binary encodings for ℕ, ℤ (`encNat`, `encIntBin`), lists, pairs, finite tables, and a
    `polytime` / `fun_prop` automation that certifies ordinary functional Lean code
    (lists, folds, binary + - * pow sum, comparisons, primality on unary ℕ,
    bounded `findGreatest`),
  * `PPoly`, `PAdvice_subset_PPoly`, and **Karp–Lipton**
    (`PH_eq_SigmaP_two_of_SAT : (SAT has P/poly circuits) → PH = Σ₂`).
* **No library anywhere has 3DM, X3C, or Exact Cover NP-hardness with a polytime proof.**
  Our reduction does not actually need X3C, though. `compiler_correct` in
  `Hardness/Main.lean` works for **any** `MaskedSystem` (a 0/1 matrix A, a 0/1 vector b,
  and a mask μ). So the cheapest honest chain is
  **`ExactThreeSAT` →(new, simple 1-in-3 gadget) `MaskedSystem` →(our compiler) `PrincipalCVP`**,
  with SAT's NP-hardness imported from complexitylib. X3C NP-completeness (needed only to
  match the paper's wording) can be added afterwards: X3C → MaskedSystem is trivial, and
  3SAT → 3DM → X3C can be ported from the semantic proofs in `humiliati/sundogcert`.
* The real cost is **not** the complexity theory. It is a *list-level, computable*
  re-implementation of the compiler (`reductionData`, `g`, `T`, `Δ`), proved equal to
  the existing `Fin`-indexed definitions and then certified polytime with `fun_prop`.
  NP membership needs one more math lemma: a polynomial bit-size bound on a closest
  coefficient vector q, which follows from Cramer's rule and Hadamard's bound (Mathlib
  has both) together with `principal_full_rank`.
* Estimate: **about 4–7k new Lean lines, or 4–6 Codex rounds of the size of rounds 1–4**
  for full NP-completeness from SAT. CVPP/P/poly costs about 1–2 extra rounds.

## 1. Survey

### 1.1 Mathlib (our pin)
* `Mathlib/Computability/TuringMachine/Computable.lean`: `FinTM2`, `TM2OutputsInTime`,
  `TM2ComputableInPolyTime ea eb f` (a machine, a `Polynomial ℕ` time bound, and a proof).
  The only polytime instance is `idComputableInPolyTime`. **There is no composition lemma**
  (`grep` finds no other use of `TM2ComputableInPolyTime` in Mathlib), no P, no NP, and no
  reductions. `Encoding.lean` has `FinEncoding`, `encodeNat`, and similar. `Primrec`, `Partrec`,
  and `Reduce.lean` (many-one *computable* reducibility) are about computability only.
* Verdict: usable only as a base for definitions. Building TM2 composition yourself is a
  big job; `solresol/lean-np-hardness` has spent thousands of lines just on composing two
  TM2 machines. Not recommended.
* Mathlib math we need for NP membership: `Matrix.det_le`
  (`Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`, a Hadamard-type bound
  |det| ≤ n!·cⁿ), and `Matrix.cramer` / `mulVec_cramer` (`.../Matrix/Adjugate.lean`).

### 1.2 Lean 4 complexity projects

| Repo | Licence | Lean | Status / what is reusable |
|---|---|---|---|
| https://github.com/cslib-community/complexitylib | Apache-2.0 | v4.36.0-rc1, Mathlib 625d891 (= ours) | **Recommended.** Multitape TMs (on cslib), P/NP/coNP/PH/BPP/PP/#P…, Cook–Levin, 3SAT, SubsetSum, ZeroOneIP, Karp reductions, P/poly, Karp–Lipton, `polytime` tactic. Active (last push 2026-10-23). APIs still evolving, so pin a commit. Library is AI-assisted. Latest checked commit `ba134c18`. |
| https://github.com/leanprover/cslib | Apache-2.0 | v4.36.0-rc1 | Upstream base: `Cslib.Computability.Machines.Turing.MultiTape` (`ComputableInTimeAndSpaceOfLength`), `Cslib.Foundations.Data.Nat.PolynomialBound` (`PolynomiallyBounded`), circuits. No NP or Karp reductions upstream yet; those live in complexitylib, which is designed to be upstreamed (`Complexity.` → `Cslib.`). |
| https://github.com/SamuelSchlesinger/complexitylib (redirects to `complexitylib-v1`) | Apache-2.0 | v4.35.0-rc3 | Legacy V1 with a different API. Don't use. |
| https://github.com/TankTechnology/CLRS-Lean (docs: https://tanktechnology.github.io/CLRS-Lean/CLRSLean/Status/) | **no LICENSE file** | v4.32.0-rc1 | CLRS ch. 34: Cook–Levin, SAT, 3-CNF, Clique, VC, HamCycle, TSP, SubsetSum NP-complete over Mathlib **TM2**. Useful design reference (`PolynomialOutputReduction` + `toPolyTimeReducible` split). Old toolchain and no licence, so don't depend on it. |
| https://github.com/solresol/lean-np-hardness | no LICENSE file | v4.35.0 | `PolytimeManyOneReduction` over Mathlib `FinEncoding`/`TM2ComputableInPolyTime`. Mostly TM2 composition plumbing; Cook–Levin not finished. Shows how expensive raw TM2 is. |
| https://github.com/AEjonanonymous/Cook-Levin-Lean | MIT | v4.28.0 | TM → CNF encoding with soundness only; no polytime and no NP class. Not useful. |
| https://github.com/google-deepmind/formal-conjectures (`FormalConjecturesForMathlib/Computability/Complexity`, docs https://firsching.ch/formal-conjectures/src/FormalConjecturesForMathlib/Computability/Complexity/) | Apache-2.0 | recent | Statement-only P, NP (`List Bool → Bool`, verifier with `TM2ComputableInPolyTime`) for P≠NP (issue https://github.com/google-deepmind/formal-conjectures/issues/676). Definitions only, no theory. |
| https://github.com/lean-dojo/LeanMillenniumPrizeProblems (`Problems/PVersusNP/Millennium.lean`) | Apache-2.0 | v4.31.0 | Statement-level P vs NP over Mathlib `FinEncoding`/TM2. Definitions only. |
| https://github.com/facebookresearch/atlas-lean | NOASSERTION | – | Has `theorem_wanted exactCover_npComplete`, `exactCoverBy3Sets_npComplete`, and `threeDimensionalMatching_npComplete` (statements, no proofs). Confirms nobody has a proof yet. |
| https://github.com/humiliati/sundogcert (Zenodo https://doi.org/10.5281/zenodo.20711226) | Apache-2.0 | v4.30.0 | **Semantic** 3SAT ≤ 3DM ≤ X3C ≤ syndrome decoding (≈1.9k lines: `SATReduction*.lean`, `ClauseGadget.lean`, `VarWheel.lean`, `MatchingNPHard.lean`). No polytime ("polynomial is unformalized"). It is a good template if we want X3C hardness via 3DM. |
| arXiv 2609.18261 "Descriptive Complexity in Lean: Completeness by First-Order Reductions" (https://arxiv.org/abs/2609.18261) | – | – | FO reductions, a stronger notion. complexitylib also has `FirstOrderReductions`. Not needed. |

### 1.3 Other provers (design ideas)
* **Coq**, Gäher & Kunze, "Mechanising Complexity Theory: The Cook-Levin Theorem in Coq",
  ITP 2021 (https://doi.org/10.4230/LIPIcs.ITP.2021.20, code https://github.com/uds-psl/cook-levin,
  library https://github.com/uds-psl/coq-library-complexity). They chose the call-by-value
  λ-calculus L as the cost model (time-invariance thesis mechanised in a companion
  ITP 2021 paper), because programs are verified as ordinary functions with an extraction
  plus a resource-analysis framework. Main lesson: **verify functional programs and
  derive machine bounds generically.** complexitylib's `fun_prop`/`polytime` gives us the
  same thing in Lean, with multitape TMs underneath.
* **Isabelle**, Balbach, AFP `Cook_Levin` (https://isa-afp.org/entries/Cook_Levin.html).
  Deterministic multitape TMs, NP via verifiers, SAT NP-complete via an oblivious two-tape
  machine. It is a direct TM approach and very large. complexitylib's definitions follow the
  same textbook (Arora–Barak Def. 2.1).
* **Isabelle**, `wimmers/poly-reductions` (https://github.com/wimmers/poly-reductions),
  Karp's 21 reductions, with runtime proved in IMP-. Cook–Levin is still open there (issue #22).
  Lesson: a separate "reduction function + size/runtime bound" layer.
* **Lattice hardness**: Kreuzer (& Nipkow), AFP `CVP_Hardness`
  (https://isa-afp.org/entries/CVP_Hardness.html; paper "Verification of NP-hardness
  Reduction Functions for Exact Lattice Problems", CADE 2023, https://arxiv.org/abs/2306.08375).
  It proves CVP (ℓ∞ and every ℓp) and SVP (ℓ∞) NP-hard. **It verifies only the reduction
  function's correctness (`x ∈ A ⟺ f x ∈ B`)** plus statements "is_reduction"; no runtime,
  no NP membership. It is still the only prior lattice-hardness formalisation I found in any
  prover, and its scope is exactly what this repo already has. A Lean statement that includes
  polytime and NP membership would therefore go further than all prior lattice work.

### 1.4 Sibling repos on this box
* `/workspace/fastersvp-lean`: its own deep-embedded **log-cost RAM**
  (`FastersvpLean/CostModel/RAM.lean`, word-RAM `GDD26/WordRAM*.lean`) and a program
  compiler/linker (`Compose*.lean`, `A4Program*.lean`, ~70 files) that still has **56 `sorry`s**.
  Its doc comment explains why a deep embedding is needed: a shallow cost model makes "∃
  algorithm with cost ≤ T" trivial. Lesson: a deep model is required, but **writing a
  bespoke machine model and compiler is a huge sink**. Reuse complexitylib's verified one.
* `/workspace/polysvp`: states algorithmic results conditional on explicitly documented
  operation/execution specs ("No complexity claim is assumed as an axiom"). That is the
  same "clearly named hypothesis" style as option B below.

## 2. Options for the NP-completeness statement

| | Option | Trust | Cost |
|---|---|---|---|
| A | Own definitions over Mathlib TM2 | honest, but we would have to build machine composition ourselves | very high (fastersvp/lean-np-hardness experience) |
| B | complexitylib definitions; take `NPHard encX3C X3C` as a **named hypothesis** | clean, standard, audited model; one explicit, true assumption | medium (polytime compiler + NP membership still needed) |
| C | complexitylib; **import** SAT NP-hardness (Cook–Levin) and add 3SAT → MaskedSystem | **unconditional**, only the three standard axioms | B + about 1 round |
| D | C + X3C NP-complete via 3SAT → 3DM → X3C (port sundogcert gadgets + polytime) | unconditional and matches the paper's source problem | C + 2–3 rounds |

Recommendation: **C, then D as an optional extra.** B is just C with the last step left out,
so write the X3C/MaskedSystem theorem in the form `NPHard enc S → NPHard encCVP PrincipalCVP`
first. The headline theorem is then obtained by plugging in either the imported SAT result or
a future X3C proof.

## 3. Concrete recommendation

### 3.1 Dependency
Add to `lakefile` (keep mathlib's root pin; it is the same commit):
```toml
[[require]]
name = "complexitylib"
git = "https://github.com/cslib-community/complexitylib"
rev = "ba134c185f6b76f68bd31c3a6b89abe8afd0f3c6"   # pin; APIs evolve
```
The cslib that comes with it is pinned at `6ff325e8…`. Run `scripts/cache/get.sh` from that
package (or accept a long first build). complexitylib files use the Lean module system
(`module`, `public import`). Plain non-module files like ours can import them, but check this
first with a small `Hardness/Complexity/Smoke.lean` (`import Complexity.Computability.Complexity.Problems.ExactThreeSAT`)
**before** any other work. If lake complains about module/non-module mixing, set
`allowNonModules`/`requiresModuleSystem` as complexitylib's own `ComplexityTests` lib does.

### 3.2 Computation model
Deterministic multitape binary TMs (cslib), via complexitylib's
`ComputableTidilyInPolyTime f encA encB`. Time is measured in the **binary** length of the
encoding, which matches the paper's "polynomial in the input size". Don't introduce a custom RAM.

### 3.3 Instances and encodings (`Hardness/Complexity/Problem.lean`)
```lean
/-- (d, g, T, Δ): coefficient lists of length d; lattice = principal ideal (g) in ℤ[y]/(y^d+1). -/
abbrev CVPInput := ℕ × (List ℤ × (List ℤ × ℤ))
def encCVP : CVPInput ↪ List Bool :=
  encPair encNat (encPair (encList encIntBin) (encPair (encList encIntBin) encIntBin))
def PrincipalCVP : Set CVPInput :=
  {x | (∃ k, x.1 = 2^k) ∧ x.2.1.length = x.1 ∧ x.2.2.1.length = x.1 ∧
       ∃ q : Coeff x.1, sqNorm (Cyclotomic.mul (ofList x.2.1) q - ofList x.2.2.1) ≤ x.2.2.2}
```
* Encode d in **binary** (`encNat`). Because the lists have length d, the input length is
  ≥ d anyway. Unary would also be fine, and some polytime proofs are easier with unary d,
  so pick whichever `fun_prop` handles best.
* Prove `PrincipalCVP` agrees with the existing `CVPYes`/`PrincipalCVPInstance`
  (`ofList`/`toList` bridge lemmas).
* Optional later: a rational variant (`List ℚ` or numerator/denominator pairs), reduced to the
  integer one with `rationalCVP_clear_denominators`.
* Source problems: `ExactThreeSAT : Set (CNF ℕ)` with `encCNF` (complexitylib). Also
  `MaskedSys := List (List Bool × Bool) × List Bool` (rows, rhs, mask), and later
  `X3C := ℕ × List (ℕ × ℕ × ℕ)` with `encPair encNat (encList …)`.

### 3.4 Theorems and how to prove them
1. **NP membership** `PrincipalCVP ∈ NP encCVP`.
   * Math: if `sqNorm(g*q − T) ≤ Δ` for some q, then some such q has
     `‖q‖∞ ≤ B(x) := d!·(maxcoef g)^d·(‖T‖₁ + Δ + 1)` (or a similar bound). If g = 0, take q = 0.
     If g ≠ 0 and d = 2^k, `principal_full_rank` makes the multiplication matrix G invertible
     over ℚ. With v = g*q, Cramer gives `det G · q = adj G · v`, so
     |q_i| ≤ |det G·q_i| ≤ Σ|adj|·|v| ≤ d·(d−1)!·c^{d−1}·‖v‖∞, using `Matrix.det_le` on minors and
     ‖v‖∞ ≤ ‖T‖∞ + √Δ. The bit length is O(d log d + d log c + log ‖T‖ + log Δ), which is polynomial.
   * Verifier: decode the certificate as d framed binary integers (or use the existing
     `IsVerifier.of_padding` / `NP.Witness` helpers), then compute the negacyclic product,
     `sqNorm`, and `≤`. Everything is lists plus binary ℤ arithmetic, so `fun_prop` should
     handle it, given a `List`-based `negacyclicMul` proved equal to `Cyclotomic.mul`.
   * Look at `SubsetSum.mem_NP` and `ZeroOneIP.mem_NP` in complexitylib as templates.
2. **Reduction ExactThreeSAT → MaskedSys** (new and small). For each variable v, add columns
   x_v and x̄_v and the row x_v + x̄_v = 1. For each clause (l₁ ∨ l₂ ∨ l₃), add 4 fresh columns
   a, b, c, e and the three 1-in-3 rows ¬l₁+a+b = 1, b+l₂+c = 1, c+e+¬l₃ = 1 (Schaefer's gadget;
   no row ever repeats a column, so repeated literals are harmless). The mask is all-true.
   Prove `φ ∈ ExactThreeSAT ↔ toMasked φ ∈ MaskedSys.Feasible` (about 400–700 lines), and
   polytime with `fun_prop` (about 150 lines, like `SubsetSum.toSubsetSum`). An alternative,
   "Exact Cover from ZeroOneIP", is not possible because ZeroOneIP has arbitrary
   coefficients and our A is 0/1.
3. **Reduction MaskedSys → PrincipalCVP** (the main work).
   * Write `compileList : MaskedSys → CVPInput` as **plain list code**: Erdős–Turán positions
     with a prime search (complexitylib has polytime `decide Prime` on unary ℕ and
     `findGreatest`; p < 2n and n ≤ input length, so the search can be unary), the `hExp` and
     `crossExp` positions, the sparse h, t, u vectors, `interleave`, P and Δ (use
     `ceilSqrt` via `Nat.sqrt` on a unary bound, or a bounded search). Bit sizes come from
     `compileX3C_size`, generalised to `ReductionData`.
   * Prove `compileList S = toCVPInput (compile (ofMaskedSys S))`, i.e. equal to the existing
     `Fin` definitions (`g`, `T`, `Δ`, `d`). This bridge is where most of the effort goes.
     Avoid `Fintype.card` of subtypes in the list program; count with `List.countP`.
   * `ComputableTidilyInPolyTime compileList encMasked encCVP` by `fun_prop`, after tagging
     each helper `@[fun_prop]` (see `Problems/SubsetSum.lean` lines 594–664 for the pattern).
     Watch out: every loop needs a size-growth contract, and indices into length-d lists must
     use `List.ofFn`/`range`+`map` patterns the tactic knows.
   * Correctness: `S ∈ Feasible ↔ compileList S ∈ PrincipalCVP`, from `compiler_correct`
     plus the bridge.
4. **Headline**:
   ```lean
   theorem principalCVP_npHard : NPHard encCVP PrincipalCVP :=
     (ExactThreeSAT_npHard).trans (polyTimeReducible_ExactThreeSAT_Masked.trans polyTimeReducible_Masked_CVP)
   theorem principalCVP_npComplete : NPComplete encCVP PrincipalCVP := ⟨principalCVP_mem_NP, principalCVP_npHard⟩
   ```
   Also keep `theorem principalCVP_npHard_of_X3C (h : NPHard encX3C X3C) : NPHard encCVP PrincipalCVP`,
   which is option B and documents the paper's route. `#print axioms` should show only
   `propext`, `Classical.choice`, `Quot.sound`.
5. **Optional: X3C NP-complete** (option D). X3C ∈ NP is easy (certificate = selection mask,
   like ZeroOneIP). For hardness, either port sundogcert's 3SAT → 3DM gadget (`VarWheel`,
   `ClauseGadget`, ≈1.3k semantic lines) and the 3DM → X3C step, then add polytime proofs, or
   reduce `MaskedSys`-from-3SAT outputs to X3C with a padding gadget. Only needed to say
   "X3C is NP-complete" verbatim.
6. **Optional: module-SIVP** NP-hardness reuses the same list-compiler pattern on
   `x3cToModuleSIVP`. **CVPP / §fixed**: complexitylib has `PPoly`, `PAdvice_subset_PPoly`, and
   `PH_eq_SigmaP_two_of_SAT`. State "if CVPP on the fixed family `L_m` is solvable by polynomial-size
   circuits given the lattice, then SAT ∈ P/poly, hence PH = Σ₂". This needs (i) a polytime map
   SAT → (m, target, threshold) whose lattice depends only on m (the existing `fixed_family_*`
   plus a polytime proof), and (ii) closure of P/poly under polytime reductions with
   length-padding, which isn't in complexitylib as a single lemma. It can be derived from
   `PPoly.exists_of_polyTime` and circuit substitution, or by padding instances to a fixed
   length per input size.

### 3.5 File plan
`Hardness/Complexity/{Smoke, Problem, ListRing, Witness (coefficient bound), Verifier,
SatToMasked, CompileList, CompileBridge, CompilePolyTime, NPComplete}.lean`, plus optional
`X3CNP.lean`, `ModuleSIVPNP.lean`, `CVPP.lean`. Update NOTES.md and the README.

## 4. Effort estimate (Codex rounds ≈ the size of rounds 1–4, ~0.5–2 h each)
| Step | Lines (rough) | Rounds | Risk |
|---|---|---|---|
| Dependency + smoke import + encodings/problem defs | 200 | 0.5 | module-system / build time |
| NP membership (Cramer/Hadamard bound + verifier polytime) | 800–1500 | 1–1.5 | medium (bound lemma, certificate decoding) |
| 3SAT → MaskedSys (correctness + polytime) | 600–900 | 1 | low |
| List compiler + bridge to Fin defs | 1500–3000 | 1.5–2 | **high** (index bookkeeping) |
| Compiler polytime via `fun_prop` | 400–800 | 0.5–1 | medium (tactic coverage: prime search, sqrt, sparse vectors) |
| Headline + docs | 100 | 0.25 | low |
| **Total for unconditional NP-completeness** | **≈4–7k** | **≈4–6** | |
| Optional X3C NP-complete (3DM chain) | 2–3k | 2–3 | medium |
| Optional CVPP ⇒ P/poly ⇒ PH = Σ₂ | 1–2k | 1–2 | medium-high |

Fallback if `fun_prop` can't handle part of the compiler: state that piece as an explicit,
named hypothesis `(hpoly : ComputableTidilyInPolyTime compileList encMasked encCVP)`, so the
headline becomes conditional and the gap is visible, not hidden as an axiom. Remove it later.
