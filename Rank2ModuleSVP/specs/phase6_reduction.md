
YOUR JOB: JOBNAME = r6-reduction. Files: Rank2ModuleSVP/Reduction.lean (optionally ReductionAux.lean).
Imports: all committed modules (Checker, CheckerAux, Admissible, Asymptotics*, Completions, Wan,
RobustCenter, Descent*, BennettPeikert, Sparse*, PrimeCyclotomic, Problem) and IdealCVP. Do NOT import
or edit Problem/Membership*/ReductionMap* (job r6-map is editing them). Use Problem's `SVPYes`,
`moduleVector`, `pairNormSq` definitions only through Problem as it is now (r6-map changes only
WellFormed's q%4 condition to q ≠ 2, not SVPYes).
Paper v2 §4.3 Cor 4.5, §5 (lines ~1116-1262 of rank2svp_v2.txt). Instance: IdealCVP.X3CInstance I
(universe Fin (3*I.q), I.n sets, I.n ≥ 1), Sidon positions s : IdealCVP.SidonPositions I.n (generic;
the map job will use IdealCVP.cubic or erdosTuran), k, odd prime q with:
k ≥ K0, (2k)^C0 ≤ q, I.n + 2 ≤ Nat.sqrt k, 4·τ·M < q (eq. 16, τ = Checker.tau, M = 3·I.q), where
K0 := max cntK0 sepK0 (and whatever your own asymptotics need), C0 := max cntC0 sepC0 (likewise);
h := cntH k (= sepWeight k = ⌊21k/20⌋; prove they agree).
1. Cor 4.5: for every ξ there is an admissible (Checker.Clean) binary weight-h x with [x] ∈ c + a
   (c = sepCenter k, a = ramifiedIdeal k), x_{α_j} = ξ_j, giving the two-sided bound (21). Instantiate
   `admissible_representative` with P = {α_j}, D = D_wit ∪ D_bad, forbidden pairs from eq. (20); use
   Lemma 3.3 (Descent/Descent2 coset_syndrome / ramified_coset_syndrome) for the coset membership and
   sepCenter_representative for Σ c_a = h.
2. Module: m₁ = (U·π^k, 0), m₂ = (U·c − V, −(QΓ : IntegerRing q)), Γ = Nat.sqrt (9k/10) per eq. (23)
   (check: ⌊√(9k/10)⌋ — define precisely as the paper, e.g. Nat.sqrt (9*k/10) if that equals it, or
   the exact real floor), F = Γ²(q−1), S = Q²(B₀ + F + κ) ∈ ℤ (Checker.threshold_integral), ν.
   determinant ≠ 0.
3. Lemma 5.1 and Thm 5.2: completeness (exact cover ⇒ SVPYes m₁ m₂ S, indeed with < S) and soundness
   (no exact cover ⇒ every nonzero module vector has pairNormSq > S), the four cases, including the
   explicit asymptotic estimates (Γ² = 9k/10 + O(√k), ν = O(k^{-3/2}), κ = O(q/k), |B₀−H| = o(L),
   H = 21L/40+o(L), F = 18L/40+o(L), S/Q² = 39L/40+o(L)) proved with explicit constants for
   k ≥ K0, q ≥ (2k)^C0. Root-of-unity facts: Sparse.second_shell; units ±ζ^j isometry.
4. Headline: `theorem exact_X3C_encoding (hWan : WanPowerSumEstimates) ... :
   I.HasExactCover ↔ SVPYes (m₁ …) (m₂ …) (S …)` (with m₁ m₂ S as named defs `redM1 redM2 redS`
   taking (I, s, k) and q implicit/explicit), plus `redDet_ne_zero`, `redS_nonneg`.
