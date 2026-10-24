You are continuing work in the Lean 4 + Mathlib Lake project at /workspace/hardness (library
`Hardness`, toolchain leanprover/lean4:v4.36.0-rc1, Mathlib already built — do NOT run
`lake update` / `lake exe cache get`, do not change lakefile.toml / lake-manifest.json /
lean-toolchain, do not use git). Read NOTES.md first: round 1 already proved the whole
X3C → principal cyclotomic CVP reduction sorry-free (Main.lean: x3c_correct, x3c_yes_gap,
x3c_no_gap, exactCoverEquivClosest). Keep all of that building and sorry-free.

Paper source: paper/src/chapter/principal-ideal.tex and pre.tex. Round 2 tasks, in priority order:

1. Faithful Lemma lem:sidon. Prove the Erdős–Turán property: for an odd prime p ≥ n,
   α_j = 2p·j + (j^2 mod p) (zero-based j < n) has strictly increasing values, α_0 = 0, and all
   nonzero ordered differences α_k − α_j (j ≠ k) pairwise distinct. (Standard proof: compare
   quotient and remainder mod 2p; uses that p is prime and odd so that x ↦ x^2 differences
   determine the pair.) Obtain p ∈ [n, 2n) via Bertrand (`Nat.exists_prime_lt_and_le_two_mul`
   or similar Mathlib lemma; handle n = 1 / p odd). Build `SidonPositions.erdosTuran` and switch
   `x3cToCVP` to use it, so the dimension bound becomes the paper's O(M n^2); update
   Dimensions.lean accordingly (state d ≤ explicit polynomial). Keep the cubic construction as an
   alternative if you like.

2. Connect the concrete coefficient model to the genuine ring. Prove that `Cyclotomic.R d` with
   `Cyclotomic.mul` is the coefficient image of `Polynomial ℤ ⧸ Ideal.span {X ^ d + 1}`:
   e.g. a map `toQuot : R d → Polynomial ℤ ⧸ Ideal.span {X^d+1}` (sum of coeff • X^i) that is an
   additive bijection (d > 0) with toQuot (mul f g) = toQuot f * toQuot g, and hence
   `principalIdealLattice g` = preimage/image of `Ideal.span {toQuot g}` under toQuot.
   Then restate the main theorem in terms of the quotient-ring ideal (a corollary
   `x3c_correct_quotient` phrased via `Ideal.span {g'}` in `Polynomial ℤ ⧸ Ideal.span {X^d+1}`
   and the coefficient vectors). (Mathlib: `Polynomial.modByMonic`, `AdjoinRoot`,
   `Ideal.Quotient.mk`, `Polynomial.X_pow_add_C`-style monic lemmas, degree < d representatives.)

3. If time permits: the cyclic extension (Section sec:cyclic-cvp, Lemma lem:principal-crt,
   Theorem thm:cyclic-cvp): lift to Z[X]/(X^D − 1), D = 2d, preserving principality and
   multiplying squared distances by 8; give the YES/NO gap for the cyclic instance.

Rules: run `lake build` often; never add `axiom`; no `sorry` in finished parts — list any
remaining `sorry` in NOTES.md. Run `#print axioms` on the main theorems (in a scratch file under
/tmp) to confirm only propext/Classical.choice/Quot.sound. Update NOTES.md (layout, Lean names
↔ paper lemma numbers, what changed in round 2, remaining gaps).
