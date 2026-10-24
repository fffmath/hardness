# Can a formalised (weak) Weil bound discharge `WanPowerSumEstimates`?

Date: 2026-10-24. Short answer: **no**. No existing Lean result fits. The estimate needs
Deligne-strength square-root cancellation on a variety of growing dimension, and no
curve-level Weil bound gives that.

## What exists in Lean 4
* math-inc/RiemannHypothesisCurves (Gauss, Bombieri–Stepanov, ~4k lines)
  https://github.com/math-inc/RiemannHypothesisCurves, commit c99880d (2026-01-16).
  - Toolchain: Lean v4.26.0-rc2, Mathlib d5c9558.
  - **No LICENSE file** (GitHub API reports license: null), so the code cannot be vendored or copied.
  - Main theorem `riemann_hypothesis_hec`: for `f : F[X]`, `3 ≤ natDegree f`, f not a square
    over the algebraic closure, `q = |F| > 6 deg f`, it proves
    `|q - #{(x,y) : y^2 = f x}| < 5 * deg f * sqrt q`.
    This covers only hyperelliptic curves (dimension 1, quadratic character).
* AINTLIB (CBirkbeck), https://github.com/CBirkbeck/AINTLIB: `HasseWeil.WeilPairing.hasse_bound`,
  the Hasse bound for elliptic curves (genus 1). It allows `sorry`; the source repo is said to be private.
* Polarnova/CryptBoolean: the Weil character-sum bound is an **open (unproved)** blueprint item.
* Mathlib: Gauss and Jacobi sums and quadratic reciprocity only. There is no Weil, Lang–Weil or Deligne bound.
* The Weil conjectures (point-count form) appear on the Lean eval leaderboard only as a `sorry` statement.

## What the paper needs
Prop 2.4 = Wan26c (arXiv:2603.27398) Props 5.2 and 6.2. The variety X_{k,m}(b) ⊂ A^m is cut out by
k-1 power sums. It is applied with m = m0 ≈ 21k/20, so its dimension is m-k+1 ≈ k/20 → ∞.
Theorem 3.4 needs relative error q^{-Ω(k)} with q only polynomial in k (q ≥ (2k)^{C0}).

* Wan proves this from **Deligne's Weil II** for singular complete intersections (Prop 5.1, via
  Hooley–Katz), together with Betti-number bounds [WZ26]. His Remark 5.5 says Weil and Lang–Weil only
  work when m > 2k (ε > 1). He calls an elementary proof for ε < 1 an **open question**.
* Character-sum route, even with an exact Weil bound |Σψ(f)| ≤ (k-1)√q: the error is ≤ k^m q^{m/2},
  but the main term is q^{m-k+1}. This is nontrivial only for m > 2(k-1). The paper cannot raise m
  that far: the checker separation needs H/L ≈ h/(2k) < 1, i.e. h < 2k.
* Lang–Weil (Cafure–Matera): the degree is about (k-1)!, so it needs q > ((k-1)!)^2. That is
  superpolynomial, so the reduction would no longer be polynomial time.
* Weakened bounds such as C·d·√q are fine where they apply. Here the obstruction is the exponent
  (dimension), not the constant. Weyl-differencing bounds q^{1-2^{1-d}} are far too weak.
* Second-moment / averaging variant: the variance needs Σ_λ|S_λ|^{2m}, with 2m > 2(k-1). There the
  additive-character Weil bound (Artin–Schreier curves, which Stepanov's method can handle) gives
  relative variance ≤ k^{2m} q^{-(m-k+1)} = q^{-Ω(k)} for C0 > ~42. This shows that *most* syndromes
  u are good, but it does not give "every b". So it would yield only a randomized or non-uniform
  reduction, not the paper's deterministic theorem. It would still need a new Lean proof of the
  additive-character Weil bound for degree < k polynomials over F_p. The Math Inc repo does not
  cover that (it is quadratic-character only and unlicensed).

## Feasibility of Stepanov directly
Stepanov's method only covers curves. Fibring the k/20-dimensional X into curves gives only
Lang–Weil-quality errors, with constants exponential in k. Formalising Deligne is out of reach
(rated P5, about 15 years of mathematics). Recommendation: keep `WanPowerSumEstimates` as the single
explicit hypothesis. Optionally, add the averaging variant as a separate randomized corollary.
