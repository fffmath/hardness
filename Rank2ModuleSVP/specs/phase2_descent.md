JOBNAME: descent. YOUR FILES: Rank2ModuleSVP/Descent2.lean and Rank2ModuleSVP/RobustCenter.lean
(and optionally Rank2ModuleSVP/BennettPeikert.lean).

Finish paper §3.1/§3.3 (descent.tex) on top of round-1 Descent.lean:
1. Thm cyclotomic-descent: image of L_{q,k} under classOf equals `ramifiedIdeal k` (π^k O_K) for
   1 ≤ k ≤ q/2 (via Hasse derivatives / (X−1)^k and X^q − 1 = (X−1)^q mod q, total ramification
   (q) = (π^{q−1}) in the model); additive iso on 1^⊥; eq. ideal-preimage; λ₁(π^k O_K)² ≥ 2kq from
   BP. Coset version: vectors with syndrome u and sum s ↔ coset (round 1 has coset_syndrome — link
   it to ramifiedIdeal).
2. PROVE Bennett–Peikert Thm 14 (`BennettPeikertMinimum`): for prime q, 1 ≤ k ≤ q/2, every nonzero
   z ∈ L_{q,k} has ‖z‖₂² ≥ 2k. Hint: if z ≡ 0 mod q, ‖z‖² ≥ q² ≥ 2k. Otherwise write z = z⁺ − z⁻;
   power sums Σ z_a a^j agree for j < k, Newton identities (j! invertible for j < k ≤ q/2) give
   Π(1−aX)^{z⁺_a} ≡ Π(1−aX)^{z⁻_a} mod X^k in F_q[X]; degrees ‖z⁺‖₁, ‖z⁻‖₁; show ‖z‖₁ ≥ 2k (e.g. via
   reciprocal polynomials / the rational function argument or the Hasse-derivative formulation
   (X−1)^k | f̄_z in F_q[X] plus counting), then ‖z‖₂² ≥ ‖z‖₁. Look up the BP paper's proof if
   useful (web access allowed). If after real effort it resists, keep the hypothesis and document.
3. Thm robust-center: c = h + π^{⌊k/2⌋}; for all sufficiently large q (k, h from eq. rs-parameters —
   define them locally in your file as in the paper, k largest with (2k)^1000 ≤ q, h = ⌊201k/200⌋;
   another job also defines them in Completions.lean, a later round will unify), every nonzero w with
   ‖w‖² ≤ 3q has dist(wc, π^k O_K)² > L/100, L = 2kq. Uses sparse_tools_i/ii from round 1.
