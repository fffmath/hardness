# hp2n-bspin status — complete

Paper: `Power2IdealSVP/paper/power2-ideal-svp.txt`, Sections 1.2–1.4.
Reference: `/workspace/shared/jobs/hardness-power2-new/out/AUDIT_B.md`, Sections 2–10.

Continued the interrupted worktree on 2026-10-28. All requested mathematical obligations
are proved. No runtime certificates, source labels, Section 1.5 ideal bridge, root imports,
fixed problem definitions, or shared package files were changed.

## Files and proved content

- `Algebra/SpinBasic.lean`: signed integer powers, antiperiodic lift, signed convolution,
  coefficient one-norm bound, shift adjoint/skew pairing, balanced base-five uniqueness,
  dyadic orbit exclusion, and explicit weighted antipodal coefficient `2 * w`.
- `Spin/Defs.lean`: shared antiperiodic extension, sparse-spin predicate, local fields,
  finite max/min objective, nonempty witnesses, threshold semantics, alternating construction,
  and uniqueness of signs up to global reversal.
- `Spin/Parameters.lean`: all `Q,R0,n,Eplus,A,T,RT,C,tau,L,G` definitions, dimension bounds,
  four-point window arithmetic, forbidden enumeration, positivity and exact margins.
- `Spin/Guard.lean`: full Lemma 2, guard vanishing, digit splitting, lifted/cyclic forbidden
  exclusion, active neighbours, no distance three, and short-support alias lemmas.
- `Spin/Shifts.lean`: signed monomial support/field/minimum invariance and preservation of
  odd alternation after changing the cut.
- `Spin/Runs.lean`: run partition into dimers/trimers, gap bounds and odd-cardinality argument.
- `Spin/ShortArc.lean`: short circular difference and common short-lift theorems.
- `Spin/Geometry.lean`: unique trimer, exact left/right dimer offsets, canonical integer
  classification, component differences, cardinality, and converse support construction.
- `Spin/Normalization.lean`: signed shift of an allowed circular support into `[0,R0]`,
  followed by ordinary positive allowed differences.
- `Spin/Support.lean`: integer/coefficient support embeddings, ranks, and canonical signs.
- `Spin/Classification.lean`: full coefficient form of Lemma 3, retaining the signed shift.
- `Spin/Interaction.lean`: all directed endpoint interactions, exact totals, nearest-neighbour
  contributions, exact small-field minimum and threshold, and actual negacyclic kernel bridges.
- `Spin/Converse.lean`: actual odd alternating coefficient configurations, guard zero,
  full field formula, exact spin minimum, and converse passing-spin construction.
- `Spin/Equivalence.lean`: equation (1), with the abstract difference-set source interface.

All new Lean files have module documentation, main declaration documentation, lines at most
100 characters, and no `sorry`, `admit`, new `axiom`, or `native_decide`. All proof modules
build at default heartbeats; no diagnostic traces or heartbeat overrides remain.

## Shared interface and definition conventions

Namespace: `Power2IdealSVP.Spin`. Coefficients: `Power2ModuleSVP.Coeff n = Fin n → ℤ`.
Multiplication is explicitly `IdealCVP.Cyclotomic.mul`, never pointwise multiplication.

`Spin/Defs.lean` imports and exports the generic signed lift and provides
`antiperiodicExtension σ := lift σ`. Euclidean quotient parity gives every wrap its sign,
including negative indices.

`OddAlternating σ` is ternarity, odd support cardinality, and the existence of η=±1 such
that `σ i = η * (-1)^supportRank σ i` on support. Both choices of initial sign are retained.
`fieldAt G σ i := σ i * (mul G σ) i`.

For positive degree, `Theta G` is the `Finset.sup'` over `spinSet n` of `spinValue G`;
`spinValue` is the `Finset.inf'` over nonempty support of `fieldAt G σ`. Both sets are proved
nonempty. Totalized degree-zero/default empty-support values are zero and never used in the
positive-degree theorems. The objective and its threshold semantics impose no promise on G.

`DValid D A0 := ∀ d∈D, 0<d ∧ d≤A0`.
`PositiveDifferences D P := ∀ x∈P, ∀ y∈P, x<y → (y-x).toNat∈D`.

Equation (1) is proved for every positive target (hence in particular for h≥3), and arbitrary
DValid distance sets. The separate source-label job can glue its extraction theorem directly.

## Validation

Successful final locked build:

```sh
LAKE_CACHE_DIR=/tmp/hardness-lake-cache /workspace/shared/bin/lake-locked build \
  Power2IdealSVP.Spin.Equivalence
```

Result: `Build completed successfully (7069 jobs).` Final module compiled in 2.3 seconds.
Log: `/tmp/bspin-final-03.log`. Only inherited/module-system import warnings remain.

Successful interface and axiom audit:

```sh
LAKE_CACHE_DIR=/tmp/hardness-lake-cache /workspace/shared/bin/lake-locked env lean \
  /tmp/bspin-final-check.lean
```

Log: `/tmp/bspin-final-check.log`. The main equivalence, coefficient classification and actual
configuration field theorem use only `propext`, `Classical.choice`, `Quot.sound`.
The guard, dyadic orbit exclusion and weighted antipodal coefficient have the same audit
result in `/tmp/bspin-guard-axioms.log`.

No obligations remain open in hp2n-bspin. No commits were attempted because git metadata is
read-only; all deliverables are left in this worktree.

## Exact principal declarations

The following statements are copied from the checked sources; implicit variables and
hypotheses are retained exactly. Names are in `Power2IdealSVP.Spin`.

From `Spin/Defs.lean`:

```lean
theorem le_Theta_iff {n : ℕ} (hn : 0 < n) (G : Coeff n) (t : ℤ) :
    t ≤ Theta G ↔ ∃ σ : Coeff n, OddAlternating σ ∧
      ∀ i ∈ support σ, t ≤ fieldAt G σ i
```

From `Algebra/SpinBasic.lean`:

```lean
theorem antipodal_guard_coefficient {n d : ℕ} (hn : 0 < n) (hnd : n = 2 * d)
    (w : ℤ) :
    (w • (xpow n d - xpow n (-(d : ℤ))))
      ⟨d, by omega⟩ = 2 * w
```

From `Spin/Guard.lean`:

```lean
theorem guard_zero {D : Finset ℕ} {A0 h : ℕ} (hh : 0 < h)
    {σ : Coeff (n A0)} (hσ : Ternary σ)
    (hf : ∀ i ∈ support σ, tau D A0 h ≤ fieldAt (G D A0 h) σ i) :
    ∀ i ∈ support σ, mul (A D A0) σ i = 0
```

From `Spin/Guard.lean`:

```lean
theorem guard_cyclic_pair_allowed {D : Finset ℕ} {A0 h : ℕ} (hh : 0 < h)
    {σ : Coeff (n A0)} (hσ : Ternary σ)
    (hf : ∀ i ∈ support σ, tau D A0 h ≤ fieldAt (G D A0 h) σ i)
    {i j : Fin (n A0)} (hi : i ∈ support σ) (hj : j ∈ support σ) (hij : i ≠ j) :
    cyclicDistance i j ∈ Eplus D
```

From `Spin/Shifts.lean`:

```lean
theorem OddAlternating.monomial_mul {n : ℕ} {σ : Coeff n}
    (hσ : OddAlternating σ) (e : Fin n) : OddAlternating (mul (monomial e 1) σ)
```

From `Spin/Shifts.lean`:

```lean
theorem fieldAt_monomial_mul {n : ℕ} (e : Fin n) (G σ : Coeff n) (j : Fin n) :
    fieldAt G (mul (monomial e 1) σ) (e + j) = fieldAt G σ j
```

From `Spin/Geometry.lean`:

```lean
theorem integer_geometry_with_card {D : Finset ℕ} {A0 : ℕ} {W : Finset ℤ}
    (hD : DValid D A0) (hW : PositiveDifferences (Eplus D) W)
    (hI : NoIsolated W) (hodd : Odd W.card) :
    ∃ t : ℤ, ∃ P : Finset ℤ, 0 ∈ P ∧ PositiveDifferences D P ∧
      W.image (fun x => x - t) = configuration P ∧ W.card = 2 * P.card + 1
```

From `Spin/Classification.lean`:

```lean
theorem classify_passing_spin {D : Finset ℕ} {A0 h : ℕ} (hD : DValid D A0)
    (hh : 0 < h) {σ : Coeff (n A0)} (hσ : OddAlternating σ)
    (hf : ∀ i ∈ support σ, tau D A0 h ≤ fieldAt (G D A0 h) σ i) :
    ∃ (e : Fin (n A0)) (t : ℤ) (P : Finset ℤ),
      0 ∈ P ∧ PositiveDifferences D P ∧
      integerSupport (mul (monomial e 1) σ) =
        (configuration P).image (fun x => x + t) ∧
      (∀ x ∈ integerSupport (mul (monomial e 1) σ), 0 ≤ x ∧ x ≤ R0 A0)
```

From `Spin/Interaction.lean`:

```lean
theorem componentField_table {D : Finset ℕ} {A0 : ℕ} {P : Finset ℤ}
    (hD : DValid D A0) (hP : PositiveDifferences D P)
    {q r x : ℤ} (hq : q ∈ P) (hr : r ∈ P) (hx : x ∈ component q) :
    componentField D q r x = (1 - if r = q then 1 else 0) +
      if r = 0 ∧ extraEndpoint q x then 1 else 0
```

From `Spin/Interaction.lean`:

```lean
theorem configurationField_eq {D : Finset ℕ} {A0 : ℕ} {P : Finset ℤ}
    (hD : DValid D A0) (hP : PositiveDifferences D P) (h0 : 0 ∈ P)
    {q x : ℤ} (hq : q ∈ P) (hx : x ∈ component q) :
    configurationField D P q x = (P.card : ℤ) - 1 +
      if extraEndpoint q x then 1 else 0
```

From `Spin/Converse.lean`:

```lean
theorem configurationSpin_field {D : Finset ℕ} {A0 h : ℕ} {P : Finset ℤ}
    (hD : DValid D A0) (hP : PositiveDifferences D P) (h0 : 0 ∈ P) {t q x : ℤ}
    (ht : ∀ y ∈ configuration P, 0 ≤ y + t ∧ y + t ≤ R0 A0)
    (hq : q ∈ P) (hx : x ∈ component q) (i : Fin (n A0))
    (hi : (i.val : ℤ) = x + t) :
    fieldAt (G D A0 h) (configurationSpin A0 P t) i =
      smallConfigurationField (C D A0 h) D P q x
```

From `Spin/Converse.lean`:

```lean
theorem configurationSpin_threshold_iff {D : Finset ℕ} {A0 h : ℕ} {P : Finset ℤ}
    (hD : DValid D A0) (hP : PositiveDifferences D P) (h0 : 0 ∈ P) {t : ℤ}
    (ht : ∀ y ∈ configuration P, 0 ≤ y + t ∧ y + t ≤ R0 A0) :
    (∀ i ∈ support (configurationSpin A0 P t),
      tau D A0 h ≤ fieldAt (G D A0 h) (configurationSpin A0 P t) i) ↔ h ≤ P.card
```

From `Spin/Converse.lean`:

```lean
theorem spinValue_configurationSpin {D : Finset ℕ} {A0 h : ℕ} {P : Finset ℤ}
    (hD : DValid D A0) (hP : PositiveDifferences D P) (h0 : 0 ∈ P) {t : ℤ}
    (ht : ∀ y ∈ configuration P, 0 ≤ y + t ∧ y + t ≤ R0 A0) :
    spinValue (G D A0 h) (configurationSpin A0 P t) = C D A0 h + P.card - 1
```

From `Spin/Converse.lean`:

```lean
theorem exists_spin_of_differences {D : Finset ℕ} {A0 h : ℕ} {P : Finset ℤ}
    (hD : DValid D A0) (hP : PositiveDifferences D P) (h0 : 0 ∈ P)
    (hh : h ≤ P.card) :
    ∃ σ : Coeff (n A0), OddAlternating σ ∧
      ∀ i ∈ support σ, tau D A0 h ≤ fieldAt (G D A0 h) σ i
```

From `Spin/Equivalence.lean`:

```lean
theorem theta_threshold_iff_differences {D : Finset ℕ} {A0 h : ℕ}
    (hD : DValid D A0) (hh : 0 < h) :
    tau D A0 h ≤ Theta (G D A0 h) ↔
      ∃ P : Finset ℤ, 0 ∈ P ∧ h ≤ P.card ∧ PositiveDifferences D P
```

