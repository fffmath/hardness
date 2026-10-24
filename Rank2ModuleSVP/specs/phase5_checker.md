
YOUR JOB: JOBNAME = r5-checker. Files: Rank2ModuleSVP/Checker.lean, Rank2ModuleSVP/CheckerAux.lean,
Rank2ModuleSVP/GaussSum.lean (delete its content usage; if nothing uses it, empty it to a stub or
leave it untouched but stop importing it — tell in notes), and new Rank2ModuleSVP/CheckerV2*.lean if
you prefer. Do NOT import Asymptotics*/Completions/RobustCenter (other jobs rewrite them).
v2 §4 (lines ~800-1132 of rank2svp_v2.txt). The existing v1 Checker already has the v2 offsets
(τ = 2α⋆+1, β_i = τ(i), d_ij), D_wit/D_bad, Lemma 4.1 (`row_shift_separation`), correlations,
E, Clean (= v2 "admissible"), E_nonneg, E_eq_zero_of_clean, and `p` (= v2 g). Re-target:
1. Remove the Gauss-sum / q%4=3 parts. Work for every odd prime q (hypotheses `Fact q.Prime`, q ≠ 2).
2. Define in IntegerRing q (integral!): g, V := 6 Σ_j ζ^{α_j}, Q := 128 W⁴ h, U := Q + g².
   Also their RationalRing images if convenient. κ := 2q/Q, R(x) := ‖g²[x] − V‖²/Q², B₀ (eq. 18).
3. Lemma 4.2: ∀ y w, normSq (U*y) ≥ Q² normSq y and normSq (V*w) ≤ (2W)² normSq w. Prove in the
   model: g self-conjugate ⇒ ⟨Uy,Uy⟩ = Q²‖y‖² + 2Q‖gy‖² + ‖g²y‖² (adjointness); V/g bound via
   triangle inequality over 2W (resp. 6n=2W total weight) monomials (monomial isometry). State them
   for RationalRing (K) as in the paper (y, w ∈ K) since Lemma 5.1 needs arbitrary K elements;
   also give IntegerRing corollaries.
4. Theorem 4.3: for binary weight-h x: ‖U[x] − V‖²/Q² = B₀ + 2κ‖Aξ−1‖² + κE(x) + R(x) and
   0 ≤ R(x) < κ/8 (eq. 17-18, using W ≥ 3, h ≥ 1). Reuse v1 lemmas (quadratic_incidence_identity,
   p_norm_correlations, etc.).
5. Corollary-ready packaging: `checker_lower` (any binary weight-h x: ≥ B₀ + 2κ‖Aξ−1‖²) and
   `checker_upper_of_clean` (admissible x: ≤ B₀ + 2κ‖Aξ−1‖² + κ/8), plus integrality facts used for
   S ∈ ℤ (Q²B₀ ∈ ℤ, Q²κ = 2qQ).
