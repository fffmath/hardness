import Power2ModuleSVPSubsetSum.Algebra.Units

/-! # Signed unit action on module vectors

Multiplying a coefficient pair by a signed monomial preserves its maximum norm and
nonzeroness. This normalizes a signed monomial second multiplier to one.

Paper: `paper/power2svp-subsetsum.pdf`, Proposition 4.2.
-/
namespace Power2ModuleSVPSubsetSum.Reduction
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- Componentwise multiplication of a coefficient pair by a ring element. -/
def pairMul {d : ℕ} (t : Coeff d) (v : Coeff d × Coeff d) : Coeff d × Coeff d :=
  (mul t v.1, mul t v.2)

/-- A coefficient pair has maximum norm zero exactly when it vanishes. -/
@[simp] theorem pairSup_eq_zero_iff {d : ℕ} (v : Coeff d × Coeff d) :
    pairSup v = 0 ↔ v = 0 := by
  rcases v with ⟨a, b⟩
  simp [pairSup, coeffSup_eq_zero_iff]

/-- A signed monomial preserves the maximum norm of coefficient pairs. -/
theorem SignedMonomial.pairSup_mul {d : ℕ} {t : Coeff d}
    (ht : SignedMonomial t) (v : Coeff d × Coeff d) :
    pairSup (pairMul t v) = pairSup v := by
  simp only [pairSup, pairMul]
  rw [Power2ModuleSVPSubsetSum.SignedMonomial.coeffSup_mul ht,
    Power2ModuleSVPSubsetSum.SignedMonomial.coeffSup_mul ht]

/-- A signed monomial preserves nonzeroness of coefficient pairs. -/
theorem SignedMonomial.pairMul_ne_zero_iff {d : ℕ} {t : Coeff d}
    (ht : SignedMonomial t) (v : Coeff d × Coeff d) :
    pairMul t v ≠ 0 ↔ v ≠ 0 := by
  apply not_congr
  rw [← pairSup_eq_zero_iff (pairMul t v), ← pairSup_eq_zero_iff v,
    SignedMonomial.pairSup_mul ht]

/-- Multiplication of the multipliers multiplies the resulting module vector. -/
theorem moduleVector_mul {d : ℕ} (hd : 0 < d) (c₁ c₂ : Coeff d × Coeff d)
    (t a b : Coeff d) :
    moduleVector c₁ c₂ (mul t a) (mul t b) =
      pairMul t (moduleVector c₁ c₂ a b) := by
  have hc (c x : Coeff d) : mul c (mul t x) = mul t (mul c x) := by
    rw [← coeff_mul_assoc hd, IdealCVP.Cyclotomic.mul_comm c t, coeff_mul_assoc hd]
  simp only [moduleVector, pairMul, hc, mul_add]

/-- A signed monomial second multiplier can be normalized to one, preserving the vector norm
and nonzeroness. The witness explicitly records the inverse used by the normalization. -/
theorem normalize_signedMonomial {d : ℕ} (hd : 0 < d)
    (c₁ c₂ : Coeff d × Coeff d) (a b : Coeff d) (hb : SignedMonomial b) :
    ∃ t : Coeff d, SignedMonomial t ∧ mul t b = coeffOne hd ∧
      pairSup (moduleVector c₁ c₂ (mul t a) (coeffOne hd)) =
        pairSup (moduleVector c₁ c₂ a b) ∧
      (moduleVector c₁ c₂ (mul t a) (coeffOne hd) ≠ 0 ↔
        moduleVector c₁ c₂ a b ≠ 0) := by
  obtain ⟨t, ht, _, htb⟩ := Power2ModuleSVPSubsetSum.SignedMonomial.exists_inverse hb hd
  refine ⟨t, ht, htb, ?_, ?_⟩
  · rw [← htb, moduleVector_mul hd, SignedMonomial.pairSup_mul ht]
  · rw [← htb, moduleVector_mul hd]
    exact SignedMonomial.pairMul_ne_zero_iff ht _

/-- Every nonzero short vector with a signed monomial second multiplier has a normalized
nonzero vector with second multiplier one and exactly the same norm. -/
theorem normalize_short_vector {d : ℕ} (hd : 0 < d)
    (c₁ c₂ : Coeff d × Coeff d) (a b : Coeff d) (hb : SignedMonomial b)
    (hne : moduleVector c₁ c₂ a b ≠ 0) :
    ∃ a' : Coeff d, moduleVector c₁ c₂ a' (coeffOne hd) ≠ 0 ∧
      pairSup (moduleVector c₁ c₂ a' (coeffOne hd)) =
        pairSup (moduleVector c₁ c₂ a b) := by
  obtain ⟨t, _, _, hnorm, hnz⟩ := normalize_signedMonomial hd c₁ c₂ a b hb
  exact ⟨mul t a, hnz.mpr hne, hnorm⟩

end Power2ModuleSVPSubsetSum.Reduction
