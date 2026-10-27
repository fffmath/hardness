import Power2ModuleSVPSubsetSum.Algebra.Norms

/-! # Signed monomial units

Explicit inverses and norm invariance of the signed coordinate monomials.
Paper: `paper/power2svp-subsetsum.pdf`, Section 2.1.
-/
namespace Power2ModuleSVPSubsetSum
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- The inverse of `X^e`, with the negacyclic wraparound sign. -/
def monomialInv {d : ℕ} (e : Fin d) : Coeff d :=
  if h : e.val = 0 then coeffOne (by have := e.isLt; omega)
  else -monomial ⟨d - e.val, by omega⟩ 1

/-- Product of two coordinate monomials, with one possible wraparound. -/
theorem monomial_mul_monomial {d : ℕ} (e f : Fin d) :
    mul (monomial e 1) (monomial f 1) =
      monomial ⟨(e.val + f.val) % d, Nat.mod_lt _ (by have := e.isLt; omega)⟩
        (if e.val + f.val < d then 1 else -1) := by
  ext r
  rw [mul_monomial_left]
  have heq (j : Fin d) :
      (if (e.val + j.val) % d = r.val then
        (if e.val + j.val < d then (1 : ℤ) else -1) * 1 * monomial f 1 j else 0) =
      if j = f then (if (e.val + f.val) % d = r.val then
        (if e.val + f.val < d then 1 else -1) else 0) else 0 := by
    by_cases hj : j = f <;> simp [monomial, hj]
  simp_rw [heq]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp [monomial, Fin.ext_iff, eq_comm]

@[simp] theorem monomial_mul_inv {d : ℕ} (e : Fin d) :
    mul (monomial e 1) (monomialInv e) = coeffOne (by have := e.isLt; omega) := by
  unfold monomialInv
  split_ifs with h
  · rw [mul_coeffOne_right]
    ext r
    simp [coeffOne, monomial, Fin.ext_iff, h]
  · rw [IdealCVP.Cyclotomic.mul_neg, monomial_mul_monomial]
    have he : e.val + (d - e.val) = d := by omega
    ext r
    by_cases hr : r.val = 0 <;> simp [he, coeffOne, monomial, Fin.ext_iff, hr]

/-- Signed monomial multiplication preserves the coefficient maximum norm. -/
theorem SignedMonomial.coeffSup_mul {d : ℕ} {v : Coeff d}
    (hv : SignedMonomial v) (a : Coeff d) : coeffSup (mul v a) = coeffSup a := by
  obtain ⟨j, rfl | rfl⟩ := hv
  · exact coeffSup_monomial_mul j a
  · rw [coeff_mul_neg_left, coeffSup_neg, coeffSup_monomial_mul]

/-- Signed monomial multiplication preserves the coefficient l1 norm. -/
theorem SignedMonomial.coeffL1_mul {d : ℕ} {v : Coeff d}
    (hv : SignedMonomial v) (a : Coeff d) : coeffL1 (mul v a) = coeffL1 a := by
  obtain ⟨j, rfl | rfl⟩ := hv
  · exact coeffL1_monomial_mul j a
  · rw [coeff_mul_neg_left, coeffL1_neg, coeffL1_monomial_mul]

/-- Every signed monomial has an explicit signed monomial two-sided inverse. -/
theorem SignedMonomial.exists_inverse {d : ℕ} {v : Coeff d}
    (hv : SignedMonomial v) (hd : 0 < d) :
    ∃ w : Coeff d, SignedMonomial w ∧ mul v w = coeffOne hd ∧
      mul w v = coeffOne hd := by
  have hi (e : Fin d) : SignedMonomial (monomialInv e) := by
    unfold monomialInv
    split_ifs with h
    · exact ⟨⟨0, hd⟩, Or.inl rfl⟩
    · exact ⟨⟨d - e.val, by omega⟩, Or.inr rfl⟩
  obtain ⟨e, rfl | rfl⟩ := hv
  · exact ⟨monomialInv e, hi e, monomial_mul_inv e, by rw [mul_comm, monomial_mul_inv]⟩
  · refine ⟨-monomialInv e, ?_, ?_, ?_⟩
    · obtain ⟨j, h | h⟩ := hi e
      · exact ⟨j, Or.inr (congrArg Neg.neg h)⟩
      · exact ⟨j, Or.inl (by simp [h])⟩
    · simp
    · rw [mul_comm]
      simp

end Power2ModuleSVPSubsetSum
