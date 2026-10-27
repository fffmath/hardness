# hp2n-bsrc progress

Continued the interrupted run in this worktree. Own scope: Source/, Ideal/, and
Algebra/IdealBasic.lean. Problem interfaces, root imports, other subprojects, package files,
and runtime certificates are unchanged.

Read INFRA.md, the paper, and AUDIT_B.md, especially Sections 4–5 and 11–12.
All Lean invocations use `/workspace/shared/bin/lake-locked` and
`LAKE_CACHE_DIR=/tmp/hardness-lake-cache`.

## Source interface

Import `Power2IdealSVP.Source.Labels`. Namespace `Power2IdealSVP.Source`.

Files: ThreeTerm.lean, RowColumn.lean, Extraction.lean, Labels.lean.

- `base v = 3*v^3+1`; vertices are `Fin v`, with `index i = i.val+1`.
- `label i = index i + base v * index i^2 + (base v)^2 * index i^3` over integers.
- `three_term_unique`: equality of label triple sums implies equality of index multisets,
  including repeated indices. Proof: no-carry digit extraction and explicit Newton identities.
- `two_term_unique` follows by padding and cancelling a repeated label.
- `ordered_difference_unique`: if `i ≠ j` and `label i-label j=label k-label l`,
  then `i=k ∧ j=l`.
- `edgeDifferences Γ : Finset ℤ`: absolute differences of labels at graph edges.
- `PositiveDifferences P D := ∀ x∈P, ∀ y∈P, x<y → y-x∈D`.
- `difference_clique_extraction Γ (hcard : 2 ≤ P.card)
  (hP : PositiveDifferences P (edgeDifferences Γ))` proves
  `∃ C : Finset (Fin v), ∃ t ε : ℤ, (ε=-1 ∨ ε=1) ∧
   Γ.IsClique (C : Set (Fin v)) ∧
   P = C.image (fun i => t+ε*label i) ∧ P.card=C.card ∧ C.card≤v`.
  The coordinate cancellation and full row/column argument are checked separately.
- `clique_positions_nonneg Γ hC hne`: a nonempty clique gives `P` with `0∈P`, equal
  cardinality, allowed positive differences, and every `p∈P` in `[0,labelBound v]`.
- `clique_iff_positions Γ (hh : 2 ≤ h)` proves
  `(∃ C, h≤C.card ∧ Γ.IsClique (C : Set (Fin v))) ↔
   ∃ P : Finset ℤ, h≤P.card ∧ PositiveDifferences P (edgeDifferences Γ) ∧ 0∈P`.
- Empty/singleton cases are explicit; singleton extraction requires `v>0`.
- Bounds: positive strictly increasing labels, `base v≤4*v^3` for `v≥1`,
  `labelBound v≤21*(v:ℤ)^9`; `labelBound` equals the last label for `v>0`.
  Every member of D is positive and ≤labelBound; `D.card≤v*v`.

Source targeted build passed; central source axiom checks report only propext,
Classical.choice, Quot.sound.

## Ideal interface

Import `Power2IdealSVP.Ideal.Construction`. Namespace `Power2IdealSVP.Ideal`.
All degree assumptions are just `hn : 0<n`, except the target well-formedness corollary
also requires `Dyadic n`. G and K are arbitrary integer coefficient arrays.

Files: Parity.lean, FullSigns.lean, Walls.lean, Theta.lean, Minimum.lean, Construction.lean.
Generic helper: Algebra/IdealBasic.lean (namespace Power2IdealSVP.Algebra).

- `normInf a : ℤ := (Power2ModuleSVP.coeffSup a : ℤ)`;
  `coeffL1 a : ℤ := ∑ i, |a i|`. Checked l1/linfinity convolution inequality,
  coercivity `(M-coeffL1 K)*normInf y ≤ normInf (M • y-mul K y)`, and injectivity
  under strict scalar domination.
- `sumPoly n` is all-one coefficients, `xPoly hn` is X (including X=-1 when n=1),
  and `difference hn=coeffOne hn-xPoly hn`.
  Checked `(1-X)S=2`, `XS=S-2`, injectivity of both factors and explicit prefix formula.
- `CommonParity y := ∀ i j, Even (y i-y j)`.
  `mem_sumPoly_ideal_iff hn y` proves `(∃ a, mul (sumPoly n) a=y) ↔ CommonParity y`.
  `commonParity_iff` also proves the exact `2R_n+ℤS` representation.
  Nonzero parity vectors in the unit cube are full signs.
- `OddAlternating σ` is LOCAL and independent of Spin/Defs.lean:
  `∃ η : ℤ, (η=-1 ∨ η=1) ∧ (∑ i,σ i)=η ∧
   ∀ k≤n, prefixSum σ k=0 ∨ prefixSum σ k=η`.
  This intrinsic prefix characterization includes both initial signs and excludes zero.
  `oddAlternating_iff_signs_sumPoly hn σ` identifies it with `Signs (Sσ)`.
  `wallSpin hn` and multiplication by S are inverse maps between these classes.
  `oddAlternating_iff_existsUnique_sign` makes the bijection explicit.
  `OddAlternating.odd_card` proves odd support cardinality;
  `OddAlternating.consecutive` proves opposite signs at consecutive active indices.
- `signSet n`: finite image of Boolean coefficient arrays; membership iff Signs.
  `minField hn K s`: inf' of `s i * (mul K s) i` over all coordinates.
  `psi hn K`: sup' of minField over signSet. Extrema are attained.
- `spinSupport σ`: nonzero coordinates. `spinMin G σ`: inf' of
  `σ i*(mul G σ) i` on this nonempty support for OddAlternating σ
  (arbitrary default zero outside that class, unused).
  `spinSet hn`: finite image of signSet under wallSpin; membership iff OddAlternating.
  `thetaOf hn G`: sup' of spinMin over spinSet. Extrema are attained.
  Dispatcher should prove equivalence of the Spin predicate to the prefix predicate, then
  extrema equality follows from the membership/attainment/threshold theorems.
- `clockMultiplier hn G B := B • xPoly hn + mul G (difference hn)`.
  `psi_clock_eq hn G B (hB : coeffL1 (mul G (difference hn)) < B)` proves exactly
  `psi hn (clockMultiplier hn G B) = -B+2*thetaOf hn G` (equation 2).
- `amplitude K := 3*coeffL1 K+1`;
  `generator hn K := mul (amplitude K • coeffOne hn-K) (sumPoly n)`.
  `lambdaInf f : ℕ` is the natural infimum of norms of actual nonzero products `mul f a`.
  It is not defined by the sign-layer formula. An explicit sign image attains the infimum.
  `lambdaInf_generator hn K` proves
  `(lambdaInf (generator hn K) : ℤ) = amplitude K-psi hn K`.
  `generator_ne_zero hn K` and exact `IdealYes` threshold equivalence are proved.
- Construction names: perturbation=H, perturbationNorm=R_H, clockAmplitude=B,
  constructedK=K, clockNorm=R_K, constructedM=M, constructedF=f, radius=r.
  `B=R_H+2τ+1`, `M=3R_K+1`, `f=(M-K)S`, `r=M+B-2τ`.
  For `hτ : 0≤τ`, `lambdaInf_constructedF` proves exactly
  `(lambdaInf (constructedF hn G τ) : ℤ) = M+B-2*thetaOf hn G` (equation 3).
  No hypothesis `τ≤thetaOf G` or source promise is used.
- `constructedF_ne_zero`, `radius_eq` (`r=M+R_H+1`), `radius_pos` (`1≤r`),
  `idealYes_constructedF_iff` (`IdealYes f r.toNat ↔ τ≤thetaOf hn G`),
  `no_gap` (`thetaOf hn G<τ → r+2≤lambdaInf f`) and vector-level gap.
  `constructedF_explicit` gives `(M-B) • S+(2*B) • 1-2 • G`.
  `outputInput` gives the exact coefficient-list problem input; its well-formedness and
  membership equivalence connect to the fixed problem definitions, without runtime claims.

## Verification / continuation

Final aggregate build PASSED:

```
LAKE_CACHE_DIR=/tmp/hardness-lake-cache /workspace/shared/bin/lake-locked build \
  Power2IdealSVP.Source.Labels Power2IdealSVP.Ideal.Construction
```

Result: `Build completed successfully (7105 jobs)`.
Log: `/tmp/bsrc-final-build.log`. All 11 Lean source files have compiled artifacts.
Only module-system import warnings (in Source modules and existing dependencies);
no proof or unused-variable/simp warnings.
Static scan: no sorry/admit/axiom/native_decide; all lines ≤100 characters.
Axiom audit PASSED: all 16 inspected central theorems depend only on `propext`,
`Classical.choice`, `Quot.sound`. Script: `/tmp/bsrc-final-audit.lean`;
log: `/tmp/bsrc-final-audit.log`.
There are no open proof obligations in this job.

No commits (git is read-only). Final cross-job glue, unification with Spin/Defs.lean, runtime
certificates, and root imports belong to the dispatcher/other jobs and are outside this scope.

Style note: Lean rejects module docstrings before imports, so each new module has its
module docstring immediately after its import header. All lines are at most 100 characters.

## Exact principal declaration signatures

`Source/Labels.lean`:

```lean
theorem three_term_unique {v : ℕ} {i j k p q r : Fin v}
    (h : label i + label j + label k = label p + label q + label r) :
    ({i, j, k} : Multiset (Fin v)) = {p, q, r}

theorem two_term_unique {v : ℕ} {i j k l : Fin v}
    (h : label i + label j = label k + label l) :
    ({i, j} : Multiset (Fin v)) = {k, l}

theorem ordered_difference_unique {v : ℕ} {i j k l : Fin v} (hne : i ≠ j)
    (h : label i - label j = label k - label l) : i = k ∧ j = l

theorem difference_clique_extraction {v : ℕ} (Γ : SimpleGraph (Fin v))
    {P : Finset ℤ} (hcard : 2 ≤ P.card)
    (hP : PositiveDifferences P (edgeDifferences Γ)) :
    ∃ C : Finset (Fin v), ∃ t ε : ℤ, (ε = -1 ∨ ε = 1) ∧
      Γ.IsClique (C : Set (Fin v)) ∧
      P = C.image (fun i => t + ε * label i) ∧ P.card = C.card ∧ C.card ≤ v

theorem clique_positions_nonneg {v : ℕ} (Γ : SimpleGraph (Fin v))
    {C : Finset (Fin v)} (hC : Γ.IsClique (C : Set (Fin v))) (hne : C.Nonempty) :
    ∃ P : Finset ℤ, 0 ∈ P ∧ P.card = C.card ∧
      PositiveDifferences P (edgeDifferences Γ) ∧
      ∀ p ∈ P, 0 ≤ p ∧ p ≤ labelBound v

theorem clique_iff_positions {v h : ℕ} (Γ : SimpleGraph (Fin v)) (hh : 2 ≤ h) :
    (∃ C : Finset (Fin v), h ≤ C.card ∧ Γ.IsClique (C : Set (Fin v))) ↔
      ∃ P : Finset ℤ, h ≤ P.card ∧
        PositiveDifferences P (edgeDifferences Γ) ∧ 0 ∈ P
```

`Ideal/Parity.lean`:

```lean
theorem difference_sumPoly {n : ℕ} (hn : 0 < n) :
    mul (difference hn) (sumPoly n) = (2 : ℤ) • coeffOne hn

theorem xPoly_sumPoly {n : ℕ} (hn : 0 < n) :
    mul (xPoly hn) (sumPoly n) = sumPoly n - (2 : ℤ) • coeffOne hn

theorem mem_sumPoly_ideal_iff {n : ℕ} (hn : 0 < n) (y : Coeff n) :
    (∃ a, mul (sumPoly n) a = y) ↔ CommonParity y
```

`Ideal/Walls.lean`:

```lean
theorem oddAlternating_iff_existsUnique_sign {n : ℕ} (hn : 0 < n) (σ : Coeff n) :
    OddAlternating σ ↔ ∃! s : Coeff n, Signs s ∧ wallSpin hn s = σ
```

`Ideal/Theta.lean`:

```lean
theorem le_thetaOf_iff {n : ℕ} (hn : 0 < n) (G : Coeff n) (b : ℤ) :
    b ≤ thetaOf hn G ↔
      ∃ σ, OddAlternating σ ∧ ∀ i, σ i ≠ 0 → b ≤ σ i * mul G σ i

theorem psi_clock_eq {n : ℕ} (hn : 0 < n) (G : Coeff n) (B : ℤ)
    (hB : coeffL1 (mul G (difference hn)) < B) :
    psi hn (clockMultiplier hn G B) = -B + 2 * thetaOf hn G

theorem OddAlternating.odd_card {n : ℕ} {σ : Coeff n} (hσ : OddAlternating σ) :
    Odd (spinSupport σ).card

theorem OddAlternating.consecutive {n : ℕ} {σ : Coeff n} (hσ : OddAlternating σ)
    {i j : Fin n} (hij : i.val < j.val) (hi : σ i ≠ 0) (hj : σ j ≠ 0)
    (hgap : ∀ k : Fin n, i.val < k.val → k.val < j.val → σ k = 0) :
    σ j = -σ i
```

`Ideal/Minimum.lean`:

```lean
theorem lambdaInf_generator {n : ℕ} (hn : 0 < n) (K : Coeff n) :
    (lambdaInf (generator hn K) : ℤ) = amplitude K - psi hn K

theorem generator_ne_zero {n : ℕ} (hn : 0 < n) (K : Coeff n) : generator hn K ≠ 0
```

`Ideal/Construction.lean`:

```lean
theorem lambdaInf_constructedF {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ)
    (hτ : 0 ≤ τ) :
    (lambdaInf (constructedF hn G τ) : ℤ) =
      constructedM hn G τ + clockAmplitude hn G τ - 2 * thetaOf hn G

theorem constructedF_ne_zero {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) :
    constructedF hn G τ ≠ 0

theorem radius_pos {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) : 1 ≤ radius hn G τ

theorem idealYes_constructedF_iff {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ)
    (hτ : 0 ≤ τ) :
    IdealYes (constructedF hn G τ) (radius hn G τ).toNat ↔ τ ≤ thetaOf hn G

theorem no_gap {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) (hτ : 0 ≤ τ)
    (hno : thetaOf hn G < τ) :
    radius hn G τ + 2 ≤ (lambdaInf (constructedF hn G τ) : ℤ)

theorem constructedF_explicit {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) :
    constructedF hn G τ =
      (constructedM hn G τ - clockAmplitude hn G τ) • sumPoly n +
        (2 * clockAmplitude hn G τ) • coeffOne hn - (2 : ℤ) • G

theorem outputInput_wellFormed {n : ℕ} (hn : 0 < n) (hd : Dyadic n)
    (G : Coeff n) (τ : ℤ) : IdealInput.WellFormed (outputInput hn G τ)

theorem outputInput_mem_iff {n : ℕ} (hn : 0 < n) (hd : Dyadic n)
    (G : Coeff n) (τ : ℤ) (hτ : 0 ≤ τ) :
    outputInput hn G τ ∈ IdealSVPLang ↔ τ ≤ thetaOf hn G
```

