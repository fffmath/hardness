JOBNAME: checker. YOUR FILES: Rank2ModuleSVP/Checker.lean (and optionally Rank2ModuleSVP/CheckerAux.lean).

Formalise paper §4 (representative.tex) sections "Separated offsets" and "Checker elements and
norm formula", plus the analytic parts of reduction.tex Lemma gap-and-stability that do NOT need
asymptotics:
1. X3C data: use IdealCVP's X3C instance type (or an abstract incidence set I ⊆ [M]×[n] with each
   set of size 3 / W = 3n) and Sidon positions α (IdealCVP.Sidon). Define τ, β_i, d_ij, D_wit,
   D_bad; prove Lemma row-shift-separation under q > 4τM (±d_ij nonzero and pairwise distinct;
   0 ∉ D_bad; D_bad ∩ D_wit = ∅; card bound O(W²) explicit, e.g. ≤ 2W²).
2. p, U = 1 + ϑp/q, D = −3Σζ^{α_j}, V = −D/(q − ϑp) in RationalRing q (q ≡ 3 mod 4). Prove
   Lemma checker-U-properties in the model: U·conj U = 1 + p²/q, U ≠ 0 / invertible, ‖Uy‖² ≥ ‖y‖²
   for all y; and ‖Vw‖ ≤ (W/q)‖w‖ (squared form fine).
3. Theorem checker-score: for binary weight-h x with ξ_j = x_{α_j},
   ‖U v_x − V‖² = B₀ + 2‖Aξ − 1‖² + E(x), with B₀ as in the paper, E(x) ≥ 0, and E(x) = 0 when x
   is clean (cleanness exactly eq. enhanced-clean-correlations). Define B₀, E, Clean.
4. The stability estimate eq. global-stability-exact: ‖Uy − Vw‖² + Γ²‖w‖² ≥ (1−ν)(‖y‖² + Γ²‖w‖²)
   with ν = W/(qΓ), for 0 < ν < 1 (any Γ > 0).
Keep the asymptotic inequalities of Lemma gap-and-stability for a later round.
