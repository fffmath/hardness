import Power2ModuleSVP.Coset.ParityBlock

/-!
# The sum polynomial and the parity ideal

Coefficient identities for `S = 1 + X + ⋯ + X^(n-1)`, including dimension one.
All multiplication below is negacyclic multiplication, never pointwise multiplication.

Paper: `paper/power2-ideal-svp.pdf`, Section 1.5; audit Sections 11–12.
-/

namespace Power2IdealSVP.Ideal
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- The sum polynomial, with every coefficient equal to one. -/
def sumPoly (n : ℕ) : Coeff n := fun _ => 1

/-- The xPoly in the negacyclic coefficient model (equal to `-1` in dimension one). -/
def xPoly {n : ℕ} (hn : 0 < n) : Coeff n :=
  if h : 1 < n then monomial ⟨1, h⟩ 1 else -coeffOne hn

/-- Multiplication by the xPoly is the signed cyclic shift, in every positive dimension. -/
theorem xPoly_mul {n : ℕ} (hn : 0 < n) (a : Coeff n) :
    mul (xPoly hn) a = shift hn a := by
  unfold xPoly
  split_ifs with h
  · simpa using mul_y h 1 a
  · have h1 : n = 1 := by omega
    subst n
    rw [coeff_mul_neg_left, mul_coeffOne]
    funext i
    have hi : i = ⟨0, hn⟩ := Fin.ext (by omega)
    subst i
    simp [shift]

/-- The finite-difference multiplier `1-X`. -/
def difference {n : ℕ} (hn : 0 < n) : Coeff n := coeffOne hn - xPoly hn

/-- Applying `1-X` subtracts the signed predecessor. -/
theorem difference_mul {n : ℕ} (hn : 0 < n) (a : Coeff n) :
    mul (difference hn) a = a - shift hn a := by
  rw [difference, coeff_mul_sub_left, mul_coeffOne, xPoly_mul]

/-- The telescoping identity `(1-X) S = 2`. -/
theorem difference_sumPoly {n : ℕ} (hn : 0 < n) :
    mul (difference hn) (sumPoly n) = (2 : ℤ) • coeffOne hn := by
  rw [difference_mul]
  funext i
  simp only [Pi.sub_apply, sumPoly, shift, Pi.smul_apply, smul_eq_mul, coeffOne,
    monomial]
  by_cases hi : i.val = 0
  · have hi' : i = ⟨0, hn⟩ := Fin.ext hi
    simp [hi']
  · have hi' : i ≠ ⟨0, hn⟩ := fun h => hi (congrArg Fin.val h)
    simp [hi', hi]

/-- The second sum identity `XS = S-2`. -/
theorem xPoly_sumPoly {n : ℕ} (hn : 0 < n) :
    mul (xPoly hn) (sumPoly n) = sumPoly n - (2 : ℤ) • coeffOne hn := by
  have := difference_sumPoly hn
  rw [difference_mul, ← xPoly_mul] at this
  linear_combination -this

/-- Multiplying the sum polynomial and then taking a difference gives twice the input. -/
theorem difference_mul_sumPoly {n : ℕ} (hn : 0 < n) (a : Coeff n) :
    mul (difference hn) (mul (sumPoly n) a) = (2 : ℤ) • a := by
  rw [← coeff_mul_assoc hn, difference_sumPoly, mul_smul_left, mul_coeffOne]

/-- The reverse order of the telescoping identity. -/
theorem sumPoly_mul_difference {n : ℕ} (hn : 0 < n) (a : Coeff n) :
    mul (sumPoly n) (mul (difference hn) a) = (2 : ℤ) • a := by
  rw [← coeff_mul_assoc hn, IdealCVP.Cyclotomic.mul_comm (sumPoly n), difference_sumPoly,
    mul_smul_left, mul_coeffOne]

/-- Multiplication by `S` is injective, without irreducibility assumptions. -/
theorem sumPoly_mul_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (mul (sumPoly n)) := by
  intro a b hab
  have h := congrArg (mul (difference hn)) hab
  rw [difference_mul_sumPoly, difference_mul_sumPoly] at h
  funext i
  have := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  omega

/-- The difference multiplier is also injective over integer coefficients. -/
theorem difference_mul_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (mul (difference hn)) := by
  intro a b hab
  have h := congrArg (mul (sumPoly n)) hab
  rw [sumPoly_mul_difference, sumPoly_mul_difference] at h
  funext i
  have := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  omega

/-- The prefixSum sum through the first `k` positions. -/
def prefixSum {n : ℕ} (a : Coeff n) (k : ℕ) : ℤ :=
  ∑ i : Fin n, if i.val < k then a i else 0

/-- The empty prefix has sum zero. -/
@[simp] theorem prefixSum_zero {n : ℕ} (a : Coeff n) : prefixSum a 0 = 0 := by
  simp [prefixSum]

/-- The full prefix sums all coefficients. -/
@[simp] theorem prefixSum_all {n : ℕ} (a : Coeff n) : prefixSum a n = ∑ i, a i := by
  simp [prefixSum]

/-- One step of the prefixSum sum. -/
theorem prefixSum_succ {n : ℕ} (a : Coeff n) (k : Fin n) :
    prefixSum a (k.val + 1) = prefixSum a k.val + a k := by
  have he (i : Fin n) :
      (if i.val < k.val + 1 then a i else 0) =
        (if i.val < k.val then a i else 0) + if i = k then a k else 0 := by
    by_cases h : i = k
    · subst i; simp
    · have : i.val ≠ k.val := fun e => h (Fin.ext e)
      by_cases hlt : i.val < k.val <;> simp [h, hlt, show
        (i.val < k.val + 1) ↔ (i.val < k.val) by omega]
  simp only [prefixSum, he, Finset.sum_add_distrib]
  simp

/-- Explicit coefficient formula for convolution by `S`. -/
theorem sumPoly_mul_apply {n : ℕ} (hn : 0 < n) (a : Coeff n) (i : Fin n) :
    mul (sumPoly n) a i = 2 * prefixSum a (i.val + 1) - ∑ j, a j := by
  let b : Coeff n := fun i => 2 * prefixSum a (i.val + 1) - ∑ j, a j
  have hb : mul (difference hn) b = (2 : ℤ) • a := by
    rw [difference_mul]
    funext k
    simp only [Pi.sub_apply, shift, Pi.smul_apply, smul_eq_mul]
    by_cases hk : k.val = 0
    · rw [ite_eq_left hk]
      have hlast : n - 1 + 1 = n := by omega
      have hp : prefixSum a (k.val + 1) = a k := by
        rw [prefixSum_succ, hk, prefixSum_zero, zero_add]
      dsimp [b]
      rw [hlast, prefixSum_all, hp]
      ring
    · rw [ite_eq_right hk]
      have hp := prefixSum_succ a k
      have hk' : k.val - 1 + 1 = k.val := by omega
      dsimp [b]
      rw [hk', hp]
      ring
  have h := difference_mul_injective hn
    (hb.trans (difference_mul_sumPoly hn a).symm)
  exact (congrFun h i).symm

/-- All coefficients have the same residue modulo two. -/
def CommonParity {n : ℕ} (y : Coeff n) : Prop :=
  ∀ i j, Even (y i - y j)

/-- A common-parity vector is exactly an even vector plus a constant vector. -/
theorem commonParity_iff {n : ℕ} (hn : 0 < n) (y : Coeff n) :
    CommonParity y ↔ ∃ (z : Coeff n) (c : ℤ),
      y = (2 : ℤ) • z + c • sumPoly n := by
  classical
  constructor
  · intro h
    let j : Fin n := ⟨0, hn⟩
    choose z hz using fun i => h i j
    refine ⟨z, y j, ?_⟩
    funext i
    have := hz i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sumPoly]
    omega
  · rintro ⟨z, c, rfl⟩ i j
    refine ⟨z i - z j, ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sumPoly]
    ring

/-- The exact parity-ideal identity `SR_n = 2R_n + ℤS`. -/
theorem mem_sumPoly_ideal_iff {n : ℕ} (hn : 0 < n) (y : Coeff n) :
    (∃ a, mul (sumPoly n) a = y) ↔ CommonParity y := by
  constructor
  · rintro ⟨a, rfl⟩ i j
    refine ⟨prefixSum a (i.val + 1) - prefixSum a (j.val + 1), ?_⟩
    rw [sumPoly_mul_apply hn, sumPoly_mul_apply hn]
    ring
  · intro h
    obtain ⟨z, c, rfl⟩ := (commonParity_iff hn y).mp h
    refine ⟨mul (difference hn) z + c • coeffOne hn, ?_⟩
    rw [mul_add, sumPoly_mul_difference, mul_smul_right, mul_coeffOne_right]

/-- Every full sign belongs to the parity ideal. -/
theorem signs_commonParity {n : ℕ} {s : Coeff n} (hs : Signs s) :
    CommonParity s := by
  intro i j
  rcases hs i with hi | hi <;> rcases hs j with hj | hj
  · exact ⟨0, by simp [hi, hj]⟩
  · exact ⟨-1, by simp [hi, hj]⟩
  · exact ⟨1, by simp [hi, hj]⟩
  · exact ⟨0, by simp [hi, hj]⟩

/-- A nonzero parity vector in the unit cube is a full sign. -/
theorem commonParity_cube_signs {n : ℕ} {y : Coeff n} (hp : CommonParity y)
    (hy : y ≠ 0) (hb : Cube y) : Signs y := by
  classical
  have he : ∃ j, y j ≠ 0 := by
    by_contra! h
    exact hy (funext h)
  obtain ⟨j, hj⟩ := he
  have hjb := abs_le.mp (hb j)
  intro i
  have hib := abs_le.mp (hb i)
  obtain ⟨k, hk⟩ := hp i j
  omega

end Power2IdealSVP.Ideal
