# Power2ModuleSVPSubsetSum — paper ↔ Lean map

Paper: [power2svp-subsetsum.pdf](paper/power2svp-subsetsum.pdf).
Names are in `Power2ModuleSVPSubsetSum` unless qualified. Section and result numbers
refer to that paper. Runtime certificates formalise its bit-time claims with native
multitape Turing machines on explicitly encoded coefficient lists.

| Paper | Lean declaration | File |
| --- | --- | --- |
| §2.1, coefficient arithmetic and norms | `coeffL1`, `coeffSup_mul_le`, `monomial_mul_apply` | [Algebra/Norms.lean](Algebra/Norms.lean) |
| §2.1, signed monomial units | `SignedMonomial.coeffSup_mul`, `SignedMonomial.exists_inverse` | [Algebra/Units.lean](Algebra/Units.lean) |
| §2.1, involution and adjoint pairing (2.4) | `star_involutive`, `star_mul`, `coeffInner_mul_adjoint` | [Algebra/Adjoint.lean](Algebra/Adjoint.lean) |
| §2.2, encoded decision language | `SVPInput`, `encSVP`, `ModuleYes`, `SVPInput.WellFormed`, `ModuleSVPLang` | [Problem.lean](Problem.lean) |
| Proposition 2.2, verifier | `moduleVerifier`, `moduleVerifier_correct` | [Membership/Verifier.lean](Membership/Verifier.lean) |
| Proposition 2.2, bounded certificates | `Membership.module_certificate_bound`, `Membership.module_certificate_length` | [Membership/Certificates.lean](Membership/Certificates.lean) |
| Proposition 2.2, polynomial verification | `moduleVerifier_polytime`, `Membership.moduleNormInput_polytime`, `Membership.moduleBoundInput_polytime` | [Membership/PolyTime.lean](Membership/PolyTime.lean) |
| Proposition 2.2, NP membership | `moduleSVP_mem_NP` | [Membership/NP.lean](Membership/NP.lean) |
| §2.3, multiplier recovery for verification | `moduleVerifier_spec`, `Membership.module_certificate_bound` (reuse `IdealCVP` matrix/Cramer machinery) | [Membership/Verifier.lean](Membership/Verifier.lean), [Membership/Certificates.lean](Membership/Certificates.lean) |
| §2.4, full multiset source | `positiveWeights_subsetSum_iff`, `subsetSum_iff_bool` | [Reduction/Source.lean](Reduction/Source.lean) |
| §3, filter (3.1), opposite pairs | `Rigidity.D`, `Rigidity.S`, `Rigidity.K`, `Rigidity.D_mul_low`, `Rigidity.D_mul_high` | [Rigidity/Filter.lean](Rigidity/Filter.lean) |
| Lemma 3.1, exact norm (3.2) and l1 bound (3.4) | `Rigidity.coeffSup_D_mul`, `Rigidity.coeffL1_DK_le` | [Rigidity/Bounds.lean](Rigidity/Bounds.lean) |
| Lemma 3.1, adjoint identities (3.3) | `Rigidity.star_K`, `Rigidity.star_D_mul_D`, `Rigidity.D_K_inner_zero` | [Rigidity/Skew.lean](Rigidity/Skew.lean) |
| Lemma 3.2, support rigidity | `Rigidity.sum_five_pow_eq_zero`, `Rigidity.support_rigidity` | [Rigidity/Support.lean](Rigidity/Support.lean) |
| Proposition 3.3, scales | `Rigidity.F`, `Rigidity.nu`, `Rigidity.rho`, `Rigidity.L`, `Rigidity.M`, `Rigidity.Q` | [Rigidity/Parameters.lean](Rigidity/Parameters.lean) |
| Proposition 3.3, multiplier rigidity | `Rigidity.multiplier_rigidity`, `Rigidity.Q_add_V_mul_injective` | [Rigidity/Multiplier.lean](Rigidity/Multiplier.lean) |
| §4, formulas (4.1)–(4.3) | `Reduction.gadget`, `Reduction.positiveReduce`, `reduce` | [Reduction/Construction.lean](Reduction/Construction.lean), [Reduction/Map.lean](Reduction/Map.lean) |
| §4, list/coefficient parameter bridge | `Reduction.gadget_M`, `Reduction.gadget_Q` | [Reduction/Bridge.lean](Reduction/Bridge.lean) |
| Lemma 4.1, Boolean encoding | `Reduction.boolean_encoding` | [Reduction/Boolean.lean](Reduction/Boolean.lean) |
| §4.1, equality-test coefficients | `Reduction.H_centered_zero`, `Reduction.H_centered_half` | [Reduction/WeightIdentity.lean](Reduction/WeightIdentity.lean) |
| §4.1, exact norm identity | `Reduction.gadget_exactNorm` | [Reduction/ExactNorm.lean](Reduction/ExactNorm.lean) |
| Proposition 4.2, determinant and validity | `Reduction.gadget_determinant_ne_zero`, `Reduction.positiveReduce_wellFormed` | [Reduction/Validity.lean](Reduction/Validity.lean) |
| Proposition 4.2, normalize short vectors | `Reduction.short_normalizes_to_boolean` | [Reduction/Soundness.lean](Reduction/Soundness.lean) |
| Proposition 4.2, correctness and exact gap | `reduce_correct`, `reduce_wellFormed`, `reduce_yes_gap`, `reduce_no_gap`, `Reduction.gadget_no_minimum_bounds` | [Reduction/Correctness.lean](Reduction/Correctness.lean) |
| Proposition 4.2, upper bound `2M` | `Reduction.gadget_firstMinimum_exists_le_two_M` | [Reduction/UpperBound.lean](Reduction/UpperBound.lean) |
| §4.2, polynomial size and bit time | `reduce_polytime` | [Runtime/Reduction.lean](Runtime/Reduction.lean) |
| Theorem 1.1 | `subsetSum_polyTimeReducible_moduleSVP`, `moduleSVP_npHard`, `moduleSVP_npComplete` | [Main.lean](Main.lean) |
| Corollary 4.3, bijection and count | `Search.witnessEquiv`, `Search.card_shortVectors` | [Search/Witness.lean](Search/Witness.lean) |
| Corollary 4.3, recovery from multipliers | `Search.recover_correct`, `Search.recover_signed_boolean` | [Search/Witness.lean](Search/Witness.lean) |
| Corollary 4.4, mathematical threshold test and answer bounds | `Search.positiveReduce_search`, `Search.reduce_search_correct`, `Search.reduce_shortest_bound` | [Search/Shortest.lean](Search/Shortest.lean) |
| Corollary 4.4, encoded search reduction and bounded oracle runtime | `Search.subsetSum_searchReducible_exactShortest`, `Search.answer_length_polyBounded`, `Search.shortestProgram_polytime`, `Search.shortestProgram_correct`, `Search.shortestProgram_queries` | [Search/Turing.lean](Search/Turing.lean) |
| Corollary 4.4, hardness for every NP language | `moduleSVP_search_npHard`, `moduleSVP_search_turing_npHard` | [Main.lean](Main.lean) |

The §2.3 row describes reused verification infrastructure; no separate polynomial-time
algorithm recovering multipliers from an arbitrary vector is claimed by `Search/Witness`.
Corollary 4.4 is proved in [Search/Turing.lean](Search/Turing.lean) and exported by
[Main.lean](Main.lean). The exact statements below use namespace
`Power2ModuleSVPSubsetSum`, with `Turing.MultiTapeTM` and `Cslib.Complexity` open.

```lean
theorem Search.subsetSum_searchReducible_exactShortest :
    SearchReducible Reduction.encSource IdealCVP.encPairRingArgs
      (Search.DecisionAnswer SubsetSum) Search.ExactShortest

theorem moduleSVP_search_npHard :
    HardUnder (fun enc L S => SearchReducible enc IdealCVP.encPairRingArgs
      (Search.DecisionAnswer L) S) @NP Search.ExactShortest

theorem moduleSVP_search_turing_npHard {α : Type} (enc : α ↪ List Bool) (L : Set α)
    (hL : L ∈ NP enc) :
    ∃ program : α → WordQueryComp Unit Bool,
      Cslib.Probability.IsOraclePPTOn enc encBool
        (fun a => Cslib.OracleComp.interpret Cslib.ProbOracleComp.query (program a)) ∧
      (∀ (oracle : Unit × List Bool → List Bool),
        (∀ x, Power2ModuleSVP.SVPInput.WellFormed x →
          Search.ExactShortest x (oracle ((), IdealCVP.encPairRingArgs x))) →
        ∀ a, a ∈ L ↔ Cslib.OracleComp.interpret (m := Id) oracle (program a) = true) ∧
      (∀ a, ∃ query, ∀ oracle : Unit × List Bool → List Bool,
        Cslib.OracleComp.queriesWith oracle (program a) = [((), query)])
```

`Search.ExactShortest` takes a module without a radius, encoded by
`IdealCVP.encPairRingArgs`, and returns the actual shortest nonzero vector as two
exact-length signed-binary coefficient lists. Its domain is precisely the wellformed
module inputs. `Search.DecisionAnswer` represents a decision language by its correct bit.
The `HardUnder` statement uses that adapter because `NPHard` itself has a decision target.

The deterministic `Search.shortestProgram` makes exactly one query and tests the
returned vector against the reduction's radius. Its strict `IsOraclePPTOn` certificate
holds against arbitrary stateful word handlers, including malformed or arbitrarily long
replies: it reads only `Search.answerLimit x` bits. Every valid shortest answer fits in
that budget, including signs and list/pair framing; `Search.answer_length_polyBounded`
bounds it by a polynomial in the binary source length. The budget uses `2M + 1` to
cover the radius-zero constant NO case. Correctness holds for every valid shortest-vector
oracle, independent of which shortest vector it returns.

The total source map removes zeros and uses fixed identity instances when normalization
empties the list. The gadget degree is `2 * 2 ^ Nat.clog 2 (max 2 weights.length)`.
Its exact `rho` is computed by `listL1 DK`; the upper estimate is used only in proofs.
All loops depend on list length or unary degree. Binary weights, targets, and scales enter
binary arithmetic; the runtime proof tracks their encoded size, including powers of five.

## Detailed mathematical API

The following signatures consolidate `specs/API-hp2n-amath.md`. Paths are relative to
this folder. `Coeff`, `coeffSup`, `pairSup`, `moduleVector`, `FirstMinimum`, and `coeffOne`
come from `Power2ModuleSVP`; `mul` is `IdealCVP.Cyclotomic.mul`. Open the root namespace
and, for gadget statements, `Reduction`; rigidity declarations are in `Rigidity`.

## `Algebra/Norms.lean`

```lean
theorem coeffSup_mul_le {d : ℕ} (a b : Coeff d) :
    coeffSup (mul a b) ≤ coeffL1 a * coeffSup b
```

```lean
theorem monomial_mul_apply {d : ℕ} (e r : Fin d) (a : Coeff d) :
    mul (monomial e 1) a r =
      if h : e.val ≤ r.val then a ⟨r.val - e.val, by omega⟩
      else -a ⟨d + r.val - e.val, by omega⟩
```

## `Algebra/Adjoint.lean`

```lean
@[simp] theorem star_involutive {d : ℕ} (a : Coeff d) : star (star a) = a
```

```lean
theorem coeffInner_mul_adjoint {d : ℕ} (_hd : 0 < d) (f g h : Coeff d) :
    coeffInner (mul f g) h = coeffInner g (mul (star f) h)
```

```lean
theorem coeffInner_mul_self_eq_zero {d : ℕ} (hd : 0 < d) {K : Coeff d}
    (hK : star K = -K) (b : Coeff d) : coeffInner b (mul K b) = 0
```

```lean
theorem star_mul {d : ℕ} (hd : 0 < d) (a b : Coeff d) :
    star (mul a b) = mul (star a) (star b)
```

## `Algebra/Units.lean`

```lean
theorem SignedMonomial.coeffSup_mul {d : ℕ} {v : Coeff d}
    (hv : SignedMonomial v) (a : Coeff d) : coeffSup (mul v a) = coeffSup a
```

```lean
theorem SignedMonomial.exists_inverse {d : ℕ} {v : Coeff d}
    (hv : SignedMonomial v) (hd : 0 < d) :
    ∃ w : Coeff d, SignedMonomial w ∧ mul v w = coeffOne hd ∧
      mul w v = coeffOne hd
```

## `Rigidity/Filter.lean`

```lean
theorem D_mul_low {m : ℕ} (hm : 0 < m) (b : Coeff (2 * m)) (j : Fin m) :
    mul (D m) b ⟨j.val, by omega⟩ =
      b ⟨j.val, by omega⟩ - b ⟨j.val + m, by omega⟩
```

```lean
theorem D_mul_high {m : ℕ} (hm : 0 < m) (b : Coeff (2 * m)) (j : Fin m) :
    mul (D m) b ⟨j.val + m, by omega⟩ =
      b ⟨j.val, by omega⟩ + b ⟨j.val + m, by omega⟩
```

```lean
theorem coeffSup_le_D_mul {m : ℕ} (hm : 0 < m) (b : Coeff (2 * m)) :
    coeffSup b ≤ coeffSup (mul (D m) b)
```

```lean
theorem K_apply {m : ℕ} (i : Fin (2 * m)) :
    K m i = if 0 < i.val ∧ i.val < m then (5 : ℤ) ^ (i.val - 1)
      else if m < i.val then (5 : ℤ) ^ (2 * m - i.val - 1) else 0
```

## `Rigidity/Bounds.lean`

```lean
theorem coeffSup_D_mul {m : ℕ} (hm : 0 < m) (b : Coeff (2 * m)) :
    coeffSup (mul (D m) b) = Finset.univ.sup (fun j : Fin m =>
      (b ⟨j.val, by omega⟩).natAbs + (b ⟨j.val + m, by omega⟩).natAbs)
```

```lean
theorem coeffL1_DK_le (m : ℕ) : coeffL1 (mul (D m) (K m)) ≤ 5 ^ (m - 1) - 1
```

## `Rigidity/Skew.lean`

```lean
theorem star_K (m : ℕ) : star (K m) = -K m
```

```lean
theorem D_K_inner_zero {m : ℕ} (hm : 0 < m) (b : Coeff (2 * m)) :
    coeffInner (mul (D m) b) (mul (D m) (mul (K m) b)) = 0
```

```lean
theorem star_D_mul_D {m : ℕ} (hm : 0 < m) :
    mul (star (D m)) (D m) = (2 : ℤ) • coeffOne (by omega)
```

## `Rigidity/Support.lean`

```lean
theorem sum_five_pow_eq_zero {k : ℕ} (c : Fin k → ℤ)
    (hbound : ∀ i, |c i| ≤ 2) (hsum : ∑ i, (5 ^ i.val : ℤ) * c i = 0) :
    ∀ i, c i = 0
```

```lean
theorem support_rigidity {m : ℕ} (hm : 0 < m) (b : Coeff (2 * m))
    (hD : coeffSup (mul (D m) b) ≤ 1)
    (hK : ∀ j : Fin m,
      (b ⟨j.val, by omega⟩ ≠ 0 ∨ b ⟨j.val + m, by omega⟩ ≠ 0) →
      mul (K m) b ⟨j.val, by omega⟩ = 0 ∧
      mul (K m) b ⟨j.val + m, by omega⟩ = 0) :
    b = 0 ∨ SignedMonomial b
```

## `Rigidity/Multiplier.lean`

```lean
theorem multiplier_rigidity {m : ℕ} (hm : 0 < m) (H V b z : Coeff (2 * m))
    (hz : coeffSup z ≤ 1)
    (hshort : coeffSup (mul H z - mul (Q H V + V) b) ≤ M H V) :
    b = 0 ∨ SignedMonomial b
```

```lean
theorem Q_add_V_mul_injective {m : ℕ} (hm : 0 < m) (H V : Coeff (2 * m)) :
    Function.Injective (mul (Q H V + V))
```

## `Reduction/Source.lean`

```lean
theorem positiveWeights_subsetSum_iff (weights : List ℕ) (target : ℕ) :
    (positiveWeights weights, target) ∈ Cslib.Complexity.SubsetSum ↔
      (weights, target) ∈ Cslib.Complexity.SubsetSum
```

```lean
theorem subsetSum_iff_bool (weights : List ℕ) (target : ℕ) :
    (weights, target) ∈ Cslib.Complexity.SubsetSum ↔
      ∃ ξ : Fin weights.length → Bool,
        ∑ j : Fin weights.length, weights.get j * (if ξ j then 1 else 0) = target
```

## `Reduction/Boolean.lean`

```lean
theorem boolean_encoding {n s : ℕ} (hs : s ≤ n) (a : Coeff n) :
    coeffSup ((2 : ℤ) • a - IdealCVP.ofList (mask n s)) ≤ 1 ↔
      ∃! ξ : Fin s → Bool, a = booleanWord hs ξ
```

## `Reduction/Bridge.lean`

```lean
theorem gadget_M (w : List ℕ) (B : ℕ) :
    let p := gadget w B
    p.M = M (IdealCVP.ofList (d := 2 * p.m) p.H) (IdealCVP.ofList p.V)
```

```lean
theorem gadget_Q (w : List ℕ) (B : ℕ) :
    let p := gadget w B
    IdealCVP.ofList (d := 2 * p.m) p.Q =
      Q (IdealCVP.ofList (d := 2 * p.m) p.H) (IdealCVP.ofList p.V)
```

## `Reduction/Validity.lean`

```lean
theorem positiveReduce_interpretation (w : List ℕ) (B : ℕ) :
    let x := positiveReduce w B
    (IdealCVP.ofList (d := degree w.length) x.1.2.1.1,
      IdealCVP.ofList (d := degree w.length) x.1.2.1.2) = gadgetA w B ∧
    (IdealCVP.ofList (d := degree w.length) x.1.2.2.1,
      IdealCVP.ofList (d := degree w.length) x.1.2.2.2) = gadgetB w B
```

```lean
theorem positiveReduce_wellFormed (w : List ℕ) (B : ℕ) :
    (positiveReduce w B).WellFormed
```

## `Reduction/ExactNorm.lean`

```lean
theorem gadget_exactNorm (w : List ℕ) (B : ℕ) (ξ : Fin w.length → Bool) :
    let p := gadget w B
    let z := (2 : ℤ) • booleanWord
      (by have := length_le_halfDegree w.length; dsimp [p, gadget]; omega :
        w.length ≤ 2 * p.m) ξ - IdealCVP.ofList (mask (2 * p.m) w.length)
    pairSup (mul (IdealCVP.ofList p.H) z - IdealCVP.ofList p.Q - IdealCVP.ofList p.V,
      (p.M : ℤ) • z) =
      p.M + 2 * ((∑ j : Fin w.length,
        (w.get j : ℤ) * (if ξ j then 1 else 0)) - (B : ℤ)).natAbs
```

## `Reduction/Correctness.lean`

```lean
theorem gadget_no_minimum_bounds (w : List ℕ) (B : ℕ)
    (hn : (w, B) ∉ Cslib.Complexity.SubsetSum) :
    ∃ r : ℕ, FirstMinimum (gadgetA w B) (gadgetB w B) r ∧
      (gadget w B).M + 1 ≤ r ∧ r ≤ 2 * (gadget w B).M
```

```lean
theorem reduce_wellFormed (x : List ℕ × ℕ) : (reduce x).WellFormed
```

```lean
theorem reduce_correct : ∀ x : List ℕ × ℕ,
    x ∈ Cslib.Complexity.SubsetSum ↔ reduce x ∈ ModuleSVPLang
```

```lean
theorem reduce_yes_gap (x : List ℕ × ℕ) (hy : x ∈ Cslib.Complexity.SubsetSum) :
    FirstMinimum (inputA (reduce x)) (inputB (reduce x)) (reduce x).2
```

```lean
theorem reduce_no_gap (x : List ℕ × ℕ) (hn : x ∉ Cslib.Complexity.SubsetSum)
    (a b : Coeff (reduce x).1.1)
    (hne : moduleVector (inputA (reduce x)) (inputB (reduce x)) a b ≠ 0) :
    (reduce x).2 + 1 ≤ pairSup (moduleVector (inputA (reduce x)) (inputB (reduce x)) a b)
```
