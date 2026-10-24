JOBNAME: completions. YOUR FILES: Rank2ModuleSVP/Completions.lean (and optionally Rank2ModuleSVP/Wan.lean).

Formalise paper §3.2 (descent.tex, "Binary representatives in ideal cosets") and the counting part
of §4.3 (representative.tex Thm enhanced-clean), parametrised by Wan's estimates:
1. `WanPowerSumEstimates : Prop` stating Proposition prop:wan-power-sum-estimates EXACTLY as in
   pre.tex (all primes q, 2 ≤ k ≤ m−2 < q−2, all b, parts (i)–(iii), real-valued bounds).
2. Parameters k, h, T from eq. rs-parameters (integer definitions: k largest with (2k)^1000 ≤ q,
   T largest with T^2000 ≤ q, h = ⌊201k/200⌋) and their scale relations as eventually-statements
   (Filter.atTop on q) — prove what you need: T = o(k), h = 201k/200 + O(1), h = o(q), k → ∞.
3. F(u; P, η) as a Finset of binary vectors ZMod q → ℤ (syndrome u, weight h, prescribed on P).
   Thm uniform-completions and Cor fixed-coordinate-ratio under `WanPowerSumEstimates`, for all
   sufficiently large q, uniformly. You may state Θ/O with explicit constants (e.g. ½·main ≤ |F|
   ≤ 2·main) — choose whatever is cleanest for the union bound below.
4. Thm enhanced-clean in ABSTRACT form (no checker definitions — another job owns those): given
   n ≤ T − 2 positions α_j (distinct, Sidon in ZMod q), a finite set of "bad" offsets Dbad with
   0 ∉ Dbad, Dbad ∩ Dwit = ∅, |Dbad| ≤ C·n² (C explicit, e.g. 2·(3n)²/n² ⇒ use |Dbad| ≤ 18 n²+…;
   take the bound as a parameter), and any ξ ∈ {0,1}^n and syndrome u with u₀ = h: there exists a
   binary x ∈ F(u; P, η^ξ) with C_x(α_ℓ − α_j) = ξ_j ξ_ℓ (j ≠ ℓ) and C_x(d) = 0 for d ∈ Dbad, for all
   sufficiently large q (threshold may depend on C only). Cyclic correlation C_x(d) = Σ_a x_a x_{a+d}.
If the full analytic counting is too long, prioritise: exact bijection/counting identities, then
the union-bound skeleton with the asymptotic facts as clearly separated lemmas; never leave sorry.
