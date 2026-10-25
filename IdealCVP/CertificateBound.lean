import IdealCVP.Certificates
import IdealCVP.GeneralFullRank
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Fintype.Pi

/-! # Explicit certificates for every nonsingular integer basis

Cramer's rule gives the deliberately loose bound
`n! * (1 + Σᵢⱼ |Bᵢⱼ| + Σᵢ |tᵢ| + |Δ|)^n`.
It bounds the *same* coefficient witness, without changing the lattice vector.
-/
namespace IdealCVP

/-- Sum bounds avoid choices of maximizing indices, including in dimension zero. -/
def basisMagnitude {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : ℤ :=
  ∑ i, ∑ j, |B i j|

/-- The sum of absolute target coefficients used in the certificate bound. -/
def targetMagnitude {n : ℕ} (t : Coeff n) : ℤ := ∑ i, |t i|

/-- An explicit bound in the basis, target, threshold and dimension. -/
def certificateBound {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (t : Coeff n) (Δ : ℤ) : ℤ :=
  n.factorial * (1 + basisMagnitude B + targetMagnitude t + |Δ|) ^ n

theorem basisMagnitude_nonneg {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    0 ≤ basisMagnitude B :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem targetMagnitude_nonneg {n : ℕ} (t : Coeff n) :
    0 ≤ targetMagnitude t := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem basis_entry_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    |B i j| ≤ basisMagnitude B := by
  calc
    _ ≤ ∑ j, |B i j| := Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ basisMagnitude B := by
      unfold basisMagnitude
      exact Finset.single_le_sum
        (f := fun k => ∑ j, |B k j|)
        (fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg (B k j)) (Finset.mem_univ i)

theorem target_entry_le {n : ℕ} (t : Coeff n) (i : Fin n) :
    |t i| ≤ targetMagnitude t := by
  unfold targetMagnitude
  exact Finset.single_le_sum (f := fun j => |t j|)
    (fun j _ => abs_nonneg (t j)) (Finset.mem_univ i)

/-- Integrality removes the square root from a residual-coordinate bound. -/
theorem int_abs_le_sq (z : ℤ) : |z| ≤ z ^ 2 := by
  rcases le_or_gt 0 z with h | h
  · rw [abs_of_nonneg h]
    by_cases hz : z = 0
    · subst z; norm_num
    · have : 1 ≤ z := by omega
      nlinarith
  · rw [abs_of_neg h]
    have : z ≤ - 1 := by omega
    nlinarith

theorem residual_coordinate_le {n : ℕ} (v : Coeff n) (i : Fin n) :
    |v i| ≤ sqNorm v :=
  (int_abs_le_sq _).trans
    (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i))

/-- Every witness for a nonsingular square basis satisfies this explicit bound. -/
theorem certificate_coeff_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (t : Coeff n) (Δ : ℤ) (x : Coeff n)
    (hx : sqNorm (B.mulVec x - t) ≤ Δ) (i : Fin n) :
    |x i| ≤ certificateBound B t Δ := by
  have hb := basisMagnitude_nonneg B
  have ht := targetMagnitude_nonneg t
  have hy (j : Fin n) : |B.mulVec x j| ≤ targetMagnitude t + |Δ| := by
    have hr := (residual_coordinate_le (B.mulVec x - t) j).trans hx
    have he : B.mulVec x j = t j + (B.mulVec x - t) j := by simp
    calc
      _ = |t j + (B.mulVec x - t) j| := congrArg abs he
      _ ≤ |t j| + |(B.mulVec x - t) j| := abs_add_le _ _
      _ ≤ _ := add_le_add (target_entry_le t j) (hr.trans (le_abs_self Δ))
  have hentries (j k : Fin n) :
      |(B.updateCol i (B.mulVec x)) j k| ≤
        1 + basisMagnitude B + targetMagnitude t + |Δ| := by
    by_cases hk : k = i
    · subst k
      rw [Matrix.updateCol_self]
      exact (hy j).trans (by omega)
    · rw [Matrix.updateCol_ne hk]
      exact (basis_entry_le B j k).trans (by have := abs_nonneg Δ; omega)
  have hdet := Matrix.det_le (abv := AbsoluteValue.abs) hentries
  have hcr : Matrix.cramer B (B.mulVec x) = B.det • x := by
    rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
      Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hcoord : (B.updateCol i (B.mulVec x)).det = B.det * x i := by
    simpa only [Matrix.cramer_apply, Pi.smul_apply, smul_eq_mul] using congrFun hcr i
  have hdetpos : 1 ≤ |B.det| := by
    have := abs_nonneg B.det
    have := abs_ne_zero.mpr hB
    omega
  calc
    |x i| ≤ |B.det| * |x i| := by nlinarith only [hdetpos, abs_nonneg (x i)]
    _ = |(B.updateCol i (B.mulVec x)).det| := by rw [hcoord, abs_mul]
    _ ≤ certificateBound B t Δ := by
      simpa only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul,
        certificateBound] using hdet

/-- General bounded-certificate form of integer CVP. -/
theorem cvp_iff_bounded_certificate {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (t : Coeff n) (Δ : ℤ) :
    CVPYes (matrixLattice B) t Δ ↔ ∃ x : Coeff n,
      (∀ i, |x i| ≤ certificateBound B t Δ) ∧ verify B t Δ x = true := by
  rw [matrix_cvp_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, certificate_coeff_le B hB t Δ x hx, (verify_eq_true B t Δ x).mpr hx⟩
  · rintro ⟨x, _, hx⟩
    exact ⟨x, (verify_eq_true B t Δ x).mp hx⟩

/-- A computable finite box of integer coefficient vectors. -/
def certificateBox {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (t : Coeff n) (Δ : ℤ) : Finset (Coeff n) :=
  Fintype.piFinset fun _ => Finset.Icc (-certificateBound B t Δ) (certificateBound B t Δ)

theorem mem_certificateBox {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (t : Coeff n) (Δ : ℤ) (x : Coeff n) :
    x ∈ certificateBox B t Δ ↔ ∀ i, |x i| ≤ certificateBound B t Δ := by
  simp only [certificateBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

/-- CVP has a witness in the explicitly bounded finite coefficient box. -/
theorem cvp_iff_finite_certificate {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (t : Coeff n) (Δ : ℤ) :
    CVPYes (matrixLattice B) t Δ ↔
      ∃ x ∈ certificateBox B t Δ, verify B t Δ x = true := by
  rw [cvp_iff_bounded_certificate B hB]
  simp only [mem_certificateBox]

/-- Exhaustive finite-box decision, with no efficiency claim. -/
def decideBoundedCVP {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (t : Coeff n) (Δ : ℤ) : Bool :=
  decide (∃ x ∈ certificateBox B t Δ, verify B t Δ x = true)

/-- The bounded exhaustive decision procedure decides nonsingular matrix CVP. -/
theorem decideBoundedCVP_eq_true {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (t : Coeff n) (Δ : ℤ) :
    decideBoundedCVP B t Δ = true ↔ CVPYes (matrixLattice B) t Δ := by
  rw [cvp_iff_finite_certificate B hB]
  exact decide_eq_true_iff

/-- General domain injectivity makes the principal multiplication matrix nonsingular. -/
theorem multiplicationMatrix_det_ne_zero {d : ℕ} (hd : ∃ k, d = 2 ^ k)
    (g : Cyclotomic.R d) (hg : g ≠ 0) : (multiplicationMatrix g).det ≠ 0 := by
  intro hz
  obtain ⟨x, hx, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  apply hx
  apply Cyclotomic.mul_injective hd hg
  rw [← multiplicationMatrix_mulVec, hzero, Cyclotomic.mul_zero]

/-- Every nonzero principal power-of-two cyclotomic ideal has bounded certificates. -/
theorem principal_cvp_iff_bounded_certificate {d : ℕ} (hd : ∃ k, d = 2 ^ k)
    (g : Cyclotomic.R d) (hg : g ≠ 0) (t : Coeff d) (Δ : ℤ) :
    CVPYes (Cyclotomic.principalIdealLattice g) t Δ ↔ ∃ x : Coeff d,
      (∀ i, |x i| ≤ certificateBound (multiplicationMatrix g) t Δ) ∧
      verify (multiplicationMatrix g) t Δ x = true := by
  rw [← matrixLattice_multiplication]
  exact cvp_iff_bounded_certificate _ (multiplicationMatrix_det_ne_zero hd g hg) t Δ

/-- The X3C construction is a special case; `x3c_bounded_certificate` gives
its sharper zero/one certificate bound. -/
theorem x3c_general_bounded_certificate (I : X3CInstance) :
    I.HasExactCover ↔ ∃ x : Coeff (x3cToCVP I).d,
      (∀ i, |x i| ≤ certificateBound (multiplicationMatrix (x3cToCVP I).g)
        (x3cToCVP I).T (x3cToCVP I).Δ) ∧
      verify (multiplicationMatrix (x3cToCVP I).g) (x3cToCVP I).T (x3cToCVP I).Δ x = true :=
  (x3c_correct I).trans (principal_cvp_iff_bounded_certificate
    (x3cToCVP I).power_two _ (x3cToCVP I).g_ne_zero _ _)

end IdealCVP
