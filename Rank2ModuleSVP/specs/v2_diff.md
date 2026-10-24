# Paper v1 (arXiv 2609.01469) → v2 (paper/rank2svp_v2.pdf) diff, and Lean impact

| Section | v1 | v2 | Lean impact |
|---|---|---|---|
| Thm 1.1 / problem | q prime ≡ 3 (mod 4) | **any odd prime q** | `Problem.WellFormed`: replace `q % 4 = 3` by `q ≠ 2`; Membership well-formedness check likewise |
| §2.2 Lemma 2.2 (canonical form) | same | same | PrimeCyclotomic reused |
| §2.3 X3C, Sidon (Lemma 2.3) | preprocessing: isolated element → fixed NO, adjoin a block | M = 0 → fixed YES (Z[ζ₃], (2,0),(0,2), S=8); zero row → fixed NO (S=1); assume M,n ≥ 1, no zero row, M ≤ 3n | final reduction wrapper changes |
| §2.4 Prop 2.4 (Wan) | identical | identical | `WanPowerSumEstimates` unchanged |
| §3.1 Lemma 3.1 (BP), Thm 3.2 (descent) | same | same | BennettPeikert / Descent / Descent2 reused (BP proved) |
| §3.2 Lemma 3.3 (coset syndrome, H vs H+2q) | same | same | coset_syndrome / binary_shell reused |
| §3.2 parameters | k = ⌊q^{1/1000}/2⌋, h = ⌊201k/200⌋, T = ⌊q^{1/2000}⌋ (k derived from q) | **k is chosen first** (k = max(k₀,(n+2)²)), q odd prime ≥ (2k)^{C₀}; h = ⌊21k/20⌋; |P| ≤ √k (no T) | Completions' rsK/rsH/rsT and v1 Asymptotics are dead; uniform-count theorem must be re-proved in the (k → ∞, q ≥ (2k)^{C₀}) regime |
| Thm 3.4 (uniform count) | (1+o(1)) q^{h−t−k+1}/(h−t)! | same shape, explicit relative error ≤ q^{−Ω(k)} + 3k²/q < 1/4 | counting skeleton (Completions bijections, wan_good_count_bounds) reusable |
| Lemma 3.5 (sparse rep., root-of-unity gap 2q−4) | same | same | Sparse: sparse_tools_i, second_shell |
| Lemma 3.6 (vanishing order) | same | same | SparsePolynomial: sparse_tools_ii |
| Thm 3.7 (robust centre) | c = h + π^{⌊k/2⌋}; v1 Lean bound dist² > L/100 for q ≥ 200^1000 | same c; **dist(wc,a)² > L/10** for ‖w‖² ≤ 3q, v2 parameters | RobustCenter must be re-targeted (proof idea identical, constants/regime change) |
| §4.1 offsets, Lemma 4.1 | τ = 2α⋆+1, β_i = τ i, d_ij = β_i − α_j, D_wit, D_bad | same | Checker offsets / separation / correlation / E / Clean reused |
| §4.2 checker | Gauss sum ϑ (ϑ² = −q), p, U = 1+ϑp/q, D = −3Σζ^{α_j}, V = −D/(q−ϑp); rational, needs q ≡ 3 mod 4 | **g = Σ(ζ^{d}+ζ^{−d}) (= v1 p), V = 6Σζ^{α_j}, Q = 128W⁴h, U = Q + g² ∈ O_K**; κ = 2q/Q, R(x) = ‖g²[x]−V‖²/Q² | GaussSum dead. New: Lemma 4.2 (‖Uy‖ ≥ Q‖y‖, ‖Vw‖ ≤ 2W‖w‖), Thm 4.3: ‖U[x]−V‖²/Q² = B₀ + 2κ‖Aξ−1‖² + κE(x) + R(x), 0 ≤ R < κ/8, new B₀ (eq. 18) |
| §4.3 admissible reps (Thm 4.4, Cor 4.5) | enhanced-clean via union bound | same idea, ratio bound |F_J|/|F| < 2(h/q)^{|J|}, proportion O(k³/q) | abstract union bound reusable; re-instantiate |
| §5 module | M = O_K(Uπ^k,0)+O_K(Uc−V,−Γ), Γ² ≈ 99L/(200(q−1)), rational → **denominator clearing by ρ = q|N(q−ϑp)|** | **M = O_K(Uπ^k,0)+O_K(Uc−V,−QΓ)**, integral, Γ = ⌊√(9k/10)⌋, F = Γ²(q−1), S = Q²(B₀+F+κ) ∈ Z, ν = 2W/(QΓ) | No denominator clearing (v1 Clearing dead). Lemma 5.1, Thm 5.2 (4 cases, explicit asymptotics H = 21L/40, F = 18L/40, S/Q² = 39L/40) |
| §5.3 choice of q | prime ≡ 3 mod 4 in [X,2X]: PNT in APs (hypothesis `PrimesThreeModFourDyadic`) | **Bertrand's postulate**: odd prime in [Y,2Y], Y = (2k)^{C₀} | hypothesis dropped; Mathlib `Nat.bertrand` |
| §5.4 NP membership | same | certificate = short vector, verifier solves for z₁,z₂ | Membership (+ MembershipCert) reused |
| Cor 1.2 (search, Turing) | same | same, one oracle call | later |

Named hypotheses after v2: only `WanPowerSumEstimates` (Weil-type bound, cited from Wan).
