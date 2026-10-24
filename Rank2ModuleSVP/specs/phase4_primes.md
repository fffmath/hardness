
YOUR JOB: JOBNAME = r4-primes. Files: Rank2ModuleSVP/Primes.lean (optionally PrimesAux.lean).
Imports: Mathlib only (plus Rank2ModuleSVP.PrimeCyclotomic if useful). Independent of other jobs.
CONTEXT: reduction.tex subsec:prime-and-euclidean needs, for the reduction to be polytime, a prime
q ≡ 3 (mod 4) with X ≤ q ≤ 2X for all X ≥ X₀ (paper cites PNT in APs). PLAN.md calls this
`PrimesThreeModFourDyadic`. It has not been stated in Lean yet.
GOALS (in order):
1. State `def PrimesThreeModFourDyadic : Prop := ∃ X₀ : ℕ, ∀ Y ≥ X₀, ∃ p, p.Prime ∧ p % 4 = 3 ∧ Y ≤ p ∧ p ≤ 2*Y`
   and the WEAKEST variant the polytime reduction actually needs, e.g.
   `def PrimesThreeModFourPolyGap : Prop := ∃ C X₀ : ℕ, ∀ Y ≥ X₀, ∃ p, p.Prime ∧ p % 4 = 3 ∧ Y ≤ p ∧ p ≤ C*Y`
   (or p ≤ Y^C), with the implication dyadic → weak.
2. TRY HARD to PROVE one of them unconditionally. Known elementary routes: Breusch (1932) / Erdős (1935)
   style Bertrand postulate for primes ≡ 3 mod 4 (and Moree's / Ramanujan-type elementary proofs), using
   Chebyshev-type bounds on products of primes in progressions via suitable binomial-coefficient-like
   quantities (e.g. analyse prime factorisations of products like ∏ (4j+3) / central binomial ratios),
   mirroring Mathlib's proof of `Nat.bertrand` (Mathlib/NumberTheory/Bertrand.lean, centralBinom bounds).
   Also check what Mathlib v4.36 already has: Dirichlet's theorem (`Nat.setOf_prime_and_eq_mod_infinite`,
   `Nat.forall_exists_prime_gt_and_eq_mod`), Chebyshev ψ/θ bounds, any PNT-in-AP or `Nat.bertrand`
   variants — grep .lake/packages/mathlib. A proof of the weak C·Y version with any explicit C and X₀
   is a full success. A proof with large C and X₀ is fine.
3. If an unconditional proof is out of reach, narrow the hypothesis as far as possible and prove
   everything around it (e.g. reduce to an explicit inequality about a single number-theoretic
   function), recording exactly what remains.
