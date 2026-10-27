# hp2n-amath: main declaration signatures

All paths below are relative to `Power2ModuleSVPSubsetSum/`. Signatures are copied from
source; `Coeff`, `coeffSup`, `pairSup`, `moduleVector`, `FirstMinimum`, and `coeffOne`
are reused from `Power2ModuleSVP`, and `mul` is `IdealCVP.Cyclotomic.mul`.
`Rigidity` and `Reduction` are namespaces below `Power2ModuleSVPSubsetSum`.
Root-level endpoints are `Power2ModuleSVPSubsetSum.reduce_correct`,
`reduce_wellFormed`, `reduce_yes_gap`, and `reduce_no_gap`.

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
