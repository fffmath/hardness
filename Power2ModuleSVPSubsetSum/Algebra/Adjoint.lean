import Power2ModuleSVPSubsetSum.Algebra.Units

/-! # The coefficient adjoint

The involution `X ↦ X⁻¹` and adjointness for the integer coefficient pairing.
Paper: `paper/power2svp-subsetsum.pdf`, Section 2.1.
-/
namespace Power2ModuleSVPSubsetSum
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- The integer coefficient pairing. -/
def coeffInner {d : ℕ} (a b : Coeff d) : ℤ := ∑ i, a i * b i

/-- Substitution of the inverse variable in the negacyclic coefficient model. -/
def star {d : ℕ} (a : Coeff d) : Coeff d := fun i =>
  if h : i.val = 0 then a i else -a ⟨d - i.val, by omega⟩

@[simp] theorem star_involutive {d : ℕ} (a : Coeff d) : star (star a) = a := by
  ext i
  by_cases hi : i.val = 0
  · simp [star, hi]
  · have hrev : d - i.val ≠ 0 := by omega
    have heq : (⟨d - (d - i.val), by omega⟩ : Fin d) = i := by
      apply Fin.ext
      change d - (d - i.val) = i.val
      omega
    simp [star, hi, hrev, heq]

@[simp] theorem star_add {d : ℕ} (a b : Coeff d) : star (a + b) = star a + star b := by
  ext i
  simp only [star, Pi.add_apply]
  split_ifs <;> ring

@[simp] theorem star_smul {d : ℕ} (z : ℤ) (a : Coeff d) : star (z • a) = z • star a := by
  ext i
  simp only [star, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

@[simp] theorem star_neg {d : ℕ} (a : Coeff d) : star (-a) = -star a := by
  simpa only [neg_one_smul] using star_smul (-1) a

@[simp] theorem star_sum {ι : Type*} [Fintype ι] {d : ℕ} (a : ι → Coeff d) :
    star (∑ j, a j) = ∑ j, star (a j) := by
  ext i
  simp only [star, Finset.sum_apply]
  split_ifs <;> simp [Finset.sum_neg_distrib]

/-- The involution commutes with arbitrary finite sums. -/
theorem star_sum_finset {ι : Type*} {d : ℕ} (s : Finset ι) (a : ι → Coeff d) :
    star (∑ j ∈ s, a j) = ∑ j ∈ s, star (a j) := by
  ext i
  simp only [star, Finset.sum_apply]
  split_ifs <;> simp [Finset.sum_neg_distrib]

/-- The star of a coordinate monomial is its explicit inverse. -/
@[simp] theorem star_monomial {d : ℕ} (e : Fin d) :
    star (monomial e 1) = monomialInv e := by
  ext r
  by_cases he : e.val = 0 <;> by_cases hr : r.val = 0
  · simp [star, monomialInv, he, hr, coeffOne, monomial, Fin.ext_iff]
  · have hre : r.val ≠ e.val := by omega
    have hrrev : d - r.val ≠ e.val := by omega
    simp [star, monomialInv, he, hr, coeffOne, monomial, Fin.ext_iff]
    omega
  · have hre : r.val ≠ e.val := by omega
    have hri : r.val ≠ d - e.val := by omega
    simp [star, monomialInv, he, hr, monomial, Fin.ext_iff,
      show (0 : ℕ) ≠ e.val by omega, show (0 : ℕ) ≠ d - e.val by omega]
  · have heq : d - r.val = e.val ↔ r.val = d - e.val := by omega
    simp [star, monomialInv, he, hr, monomial, Fin.ext_iff, heq]

@[simp] theorem coeffInner_comm {d : ℕ} (a b : Coeff d) :
    coeffInner a b = coeffInner b a := by
  simp only [coeffInner, _root_.mul_comm]

@[simp] theorem coeffInner_neg_right {d : ℕ} (a b : Coeff d) :
    coeffInner a (-b) = -coeffInner a b := by
  simp [coeffInner, Finset.sum_neg_distrib]

/-- Multiplying both arguments by one monomial preserves their pairing. -/
theorem coeffInner_monomial_mul {d : ℕ} (e : Fin d) (a b : Coeff d) :
    coeffInner (mul (monomial e 1) a) (mul (monomial e 1) b) = coeffInner a b := by
  have hd : 0 < d := by have := e.isLt; omega
  let : NeZero d := ⟨by omega⟩
  rw [coeffInner, ← Equiv.sum_comp (Equiv.addLeft e)]
  apply Finset.sum_congr rfl
  intro j _
  have hs (c : Coeff d) : mul (monomial e 1) c (e + j) =
      (if e.val + j.val < d then 1 else -1) * c j := by
    rw [mul_monomial_left]
    have hh (k : Fin d) : (e.val + k.val) % d = (e+j).val ↔ k = j := by
      change (e+k).val = (e+j).val ↔ _
      rw [← Fin.ext_iff]
      exact add_left_cancel_iff
    simp only [hh]
    simp
  change mul (monomial e 1) a (e+j) * mul (monomial e 1) b (e+j) = _
  rw [hs a, hs b]
  split_ifs <;> ring

/-- Multiplication by the inverse monomial is the coefficient adjoint shift. -/
theorem coeffInner_monomial_adjoint {d : ℕ} (e : Fin d) (g h : Coeff d) :
    coeffInner (mul (monomial e 1) g) h = coeffInner g (mul (monomialInv e) h) := by
  have hd : 0 < d := by have := e.isLt; omega
  have he : mul (monomial e 1) (mul (monomialInv e) h) = h := by
    rw [← coeff_mul_assoc hd, monomial_mul_inv, mul_coeffOne]
  conv_lhs => rw [← he]
  exact coeffInner_monomial_mul e _ _

/-- Coefficient adjointness of negacyclic multiplication. -/
theorem coeffInner_mul_adjoint {d : ℕ} (_hd : 0 < d) (f g h : Coeff d) :
    coeffInner (mul f g) h = coeffInner g (mul (star f) h) := by
  have hs : star f = ∑ i, (f i) • monomialInv i := by
    conv_lhs => rw [eq_sum_monomial f]
    simp only [star_sum, star_smul, star_monomial]
  conv_lhs => rw [eq_sum_monomial f]
  rw [mul_sum_left, hs, mul_sum_left]
  simp only [mul_smul_left, coeffInner, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hi := coeffInner_monomial_adjoint i g h
  unfold coeffInner at hi
  calc
    _ = f i * ∑ j, mul (monomial i 1) g j * h j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = f i * ∑ j, g j * mul (monomialInv i) h j := by rw [hi]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- A skew-adjoint multiplier pairs to zero with every vector. -/
theorem coeffInner_mul_self_eq_zero {d : ℕ} (hd : 0 < d) {K : Coeff d}
    (hK : star K = -K) (b : Coeff d) : coeffInner b (mul K b) = 0 := by
  have h := coeffInner_mul_adjoint hd K b b
  rw [hK, coeff_mul_neg_left, coeffInner_neg_right, coeffInner_comm] at h
  omega

/-- The coefficient pairing separates coefficient vectors. -/
theorem coeffInner_ext {d : ℕ} {a b : Coeff d}
    (h : ∀ c, coeffInner a c = coeffInner b c) : a = b := by
  ext i
  simpa [coeffInner, monomial] using h (monomial i 1)

/-- The constant coefficient of a product pairs with the adjoint. -/
theorem coeffInner_star {d : ℕ} (hd : 0 < d) (a b : Coeff d) :
    coeffInner (star a) b = coeffInner (coeffOne hd) (mul a b) := by
  have h := coeffInner_mul_adjoint hd a b (coeffOne hd)
  simpa only [mul_coeffOne_right, coeffInner_comm] using h.symm

/-- The coefficient involution preserves multiplication. -/
theorem star_mul {d : ℕ} (hd : 0 < d) (a b : Coeff d) :
    star (mul a b) = mul (star a) (star b) := by
  apply coeffInner_ext
  intro c
  rw [coeffInner_star hd, coeffInner_mul_adjoint hd, star_involutive,
    coeffInner_star hd]
  congr 1
  simp only [← coeff_mul_assoc hd]
  rw [IdealCVP.Cyclotomic.mul_comm a b]

/-- The coefficient involution preserves the maximum norm. -/
@[simp] theorem coeffSup_star {d : ℕ} (a : Coeff d) : coeffSup (star a) = coeffSup a := by
  have h (b : Coeff d) : coeffSup (star b) ≤ coeffSup b := by
    rw [coeffSup_le_iff]
    intro i
    by_cases hi : i.val = 0
    · simpa [star, hi] using natAbs_le_coeffSup b i
    · simpa [star, hi] using
        natAbs_le_coeffSup b ⟨d - i.val, by omega⟩
  exact Nat.le_antisymm (h a) (by simpa using h (star a))

end Power2ModuleSVPSubsetSum
