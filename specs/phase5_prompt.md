You are continuing work in the Lean 4 + Mathlib Lake project at /workspace/hardness (library
`Hardness`, toolchain leanprover/lean4:v4.36.0-rc1, Mathlib already built — do NOT run
`lake update` / `lake exe cache get`, do not change lakefile.toml / lake-manifest.json /
lean-toolchain, do not use git). Read NOTES.md, README.md and specs/research_next_targets.md
first (sections T1, T2, T3, T8). Rounds 1–4 are sorry-free; keep it that way, never add `axiom`,
never use `native_decide` in theorems (it is fine only inside `#eval` smoke tests).

Build hygiene: always wrap builds in a timeout (`timeout 1500 lake build`,
`timeout 600 lake env lean Hardness/Foo.lean`). If `simp`/`decide`/`omega`/`nlinarith` blows
up, replace it by explicit steps rather than retrying. Prefer new files.
Do NOT do T4/T5 (complexity classes, machine models, Turing machines, Code combinators).

Round 5 tasks, in order. Finish and build each one before starting the next, and append to
NOTES.md after each task (so partial progress is usable).

T3. Strong NP-hardness / explicit bit-size theorem. File Hardness/StrongBounds.lean.
   Using `compileX3C`, `compileX3C_size`, `penaltyBound`:
   - an explicit polynomial `valueBound (q n : ℕ) : ℕ` (closed form, e.g. C*(q+n+1)^k with
     explicit C,k) with `penaltyBound (3*q) n ≤ ...` and theorems
     `compileX3C_coeff_le : ∀ i, |generator i| ≤ valueBound I.q I.n` (same for target),
     `compileX3C_threshold_le`, `compileX3C_dim_le` all ≤ explicit polynomials in (q+n);
   - bit lengths: `Int.natAbs` / `Nat.size` (or `Nat.log 2 + 1`) of every coefficient and of Δ
     is O(log(q+n)) – state an explicit bound `Nat.size (Int.natAbs c) ≤ ...`;
   - define a simple total output length `outputLength (D : CompiledCVPData) : ℕ :=
     sum over coefficients of (Nat.size natAbs + 2) for g and T, plus size Δ, plus size d`
     and an input length `inputLength (I : X3CInstance) := q + n + 3*n*(Nat.size(3q)+1)` (or
     similar honest encoding: n triples of 3 elements of Fin (3q)), and prove
     `outputLength (compileX3C I) ≤ P (inputLength I)` for an explicit polynomial P;
   - unary statement (strong NP-hardness): the sum of |coefficients| + Δ + d is ≤ an explicit
     polynomial in inputLength I, i.e. the unary encoding size is polynomial;
   - `#eval` smoke tests on a small instance (e.g. q=1, n=1 one triple, and q=1,n=2 with a
     repeated triple; and a NO instance q=2) printing d, Δ, max coeff, outputLength, and check
     the bounds numerically. Put #eval tests in a separate file Hardness/Smoke.lean NOT imported
     by Hardness.lean if they slow the build, or under `/tmp`; mention them in NOTES.md.
     If compileX3C is noncomputable, make a computable twin and prove equality, or report why.

T1. Abstract CVPP ⇒ advice decider for the fixed family. File Hardness/CVPP.lean.
   `structure CVPPScheme (Advice : Type)` with `Pre : (m n : ℕ) → Matrix (Fin m) (Fin n) ℤ →
   Advice` (or over AddSubgroup lattices / bases of your choice), `Dec : Advice → target →
   threshold → Bool`, `spec : Dec (Pre B) t Δ = true ↔ CVPYes (matrixLattice B) t Δ`. Using
   the fixed family (Fixed.lean, FixedIndexed.lean, and Certificates.matrixLattice /
   multiplicationMatrix to present Fixed.lattice by a basis matrix — prove
   matrixLattice (fixed basis matrix) = Fixed.lattice), prove
   `cvpp_advice_decides : HasExactCover C ↔ S.Dec (advice m) (target m C) (threshold m C) = true`
   where `advice m := S.Pre (fixedBasisMatrix m)` depends only on m, plus the indexed X3C
   version (`I.HasExactCover ↔ S.Dec (advice (3*I.q)) ...`). Also: the advice is a function of
   m alone (state as a definitional/`rfl` lemma, and a theorem that two collections over the same
   m use the identical advice). No complexity classes; if you want, state polynomial-size advice
   as an explicit hypothesis `size (Pre B) ≤ p (size B)` and carry it through as a trivial
   corollary bounding advice size in terms of m (fixed basis size bounded via T3-style bounds).

T2. Certificate-size bound for every nonsingular square integer basis. File
   Hardness/CertificateBound.lean. For `B : Matrix (Fin n) (Fin n) ℤ`, `B.det ≠ 0`, t, Δ:
   if `∃ x, sqNorm (B *ᵥ x - t) ≤ Δ` then for that same x, every |x i| ≤ explicit bound
   (e.g. n! * c^(n-1) * n * (‖t‖∞ + Δ + 1)  with c = max |B i j| (+1 to avoid 0) — anything
   explicit and correct; route: det • x = adjugate B *ᵥ (B *ᵥ x), |det| ≥ 1, entries of
   adjugate bounded via `Matrix.det_le` (Mathlib LinearAlgebra/Matrix/AbsoluteValue.lean),
   |(B x)_i| ≤ |t_i| + |(Bx - t)_i| ≤ |t_i| + Δ (since squares of integers dominate abs:
   |z| ≤ z^2 for integer z) ). Conclude
   `cvp_iff_bounded_certificate : CVPYes (matrixLattice B) t Δ ↔ ∃ x, (∀ i, |x i| ≤ bound) ∧
   verify B t Δ x = true`, and a decidable/finite-box version (Finset of candidate witnesses)
   if easy. Corollary for every principal ideal: for d a power of two and any nonzero g : R d,
   multiplicationMatrix g has nonzero det (via injectivity/full rank: Cyclotomic.mul_injective
   ⇒ mulVec injective ⇒ det ≠ 0 over ℤ via `Matrix.exists_mulVec_eq_zero_iff` or ℚ cast), hence
   `principal_cvp_iff_bounded_certificate`. Show it generalises x3c_bounded_certificate
   (state the X3C instance as a special case).

T8. Search-to-decision on our instances. File Hardness/SearchToDecision.lean. Using
   `exactCoverEquivClosest` / `feasibleEquivClosest` (Main.lean): given any closest-vector
   oracle returning some v with v ∈ lattice and sqNorm(v - T) minimal (as hypothesis), decode an
   exact cover (explicit decode function from lattice vector to Finset (Fin n)), prove the decoded
   set is an exact cover when the instance is YES, and that checking the decoded set (decidable
   `IsExactCover`) decides X3C: `I.HasExactCover ↔ I.IsExactCover (decode (oracle I))`.
   Also a decision-oracle-to-search statement if natural (self-reducibility through the fixed
   family / masks: remove triples one at a time), only if it stays elementary.

Rules: finished state must build with `timeout 1500 lake build`. No `sorry`; if a task cannot be
finished, remove the unfinished part and record it in NOTES.md. Run `#print axioms` on all new
main theorems in a scratch file under /tmp (only propext/Classical.choice/Quot.sound). Add new
files to Hardness.lean (except slow smoke tests), update NOTES.md (round-5 section, Lean names ↔
research targets) and README "Main entry points".
