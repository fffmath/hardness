import Hardness.Reduction

/-! # Injectivity of the multiplication basis

For the generators produced by the compiler, P>W and Young's inequality give
injectivity directly. Thus this result does not need a quotient-ring domain
instance or a formal irreducibility proof for X^d+1.
-/
namespace Hardness.ReductionData
open Hardness Hardness.Cyclotomic
variable {M n : ℕ} (D : ReductionData M n)

theorem mul_eq_zero (q : R D.d) (hq : mul D.g q = 0) : q = 0 := by
  obtain ⟨a, b, rfl⟩ := exists_interleave q
  rw [D.generator_product] at hq
  have hz : (0 : R D.d) = interleave (0 : R D.N) 0 := by funext r; simp [interleave]
  rw [hz] at hq
  obtain ⟨he, ho⟩ := interleave_injective hq
  have he' : mul D.h a = -(D.P : ℤ) • D.xmul b := by
    funext r
    have h := congrFun he r
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h ⊢
    linarith
  have ho' : mul D.h b = -(D.P : ℤ) • a := by
    funext r
    have h := congrFun ho r
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h ⊢
    linarith
  have ha := sparse_mul_bound D.hPosition a
  have hb := sparse_mul_bound D.hPosition b
  change sqNorm (mul D.h a) ≤ (D.W : ℤ)^2 * sqNorm a at ha
  change sqNorm (mul D.h b) ≤ (D.W : ℤ)^2 * sqNorm b at hb
  rw [he', sqNorm_smul] at ha
  rw [ho', sqNorm_smul] at hb
  have hx : sqNorm (D.xmul b) = sqNorm b := sqNorm_shift D.positions.N_pos b
  rw [hx] at ha
  have hp : (D.W : ℤ) < D.P := by exact_mod_cast D.W_lt_P
  have hw : (0 : ℤ) ≤ D.W := by positivity
  have hdiff : 0 < (D.P : ℤ)^2 - (D.W : ℤ)^2 := by nlinarith
  have hs0 : 0 ≤ sqNorm a + sqNorm b := add_nonneg (sqNorm_nonneg a) (sqNorm_nonneg b)
  have hzsum : sqNorm a + sqNorm b = 0 := by
    by_contra hh
    have hprod := mul_pos hdiff (show 0 < sqNorm a + sqNorm b by omega)
    nlinarith [ha, hb]
  have ha0 := sqNorm_nonneg a
  have hb0 := sqNorm_nonneg b
  have az : a = 0 := (sqNorm_eq_zero_iff a).mp (by have := sqNorm_nonneg b; omega)
  have bz : b = 0 := (sqNorm_eq_zero_iff b).mp (by have := sqNorm_nonneg a; omega)
  subst a; subst b
  funext r; simp [interleave]

/-- The compiler's multiplication map is injective over ℤ. -/
theorem mul_injective : Function.Injective (mul D.g) := by
  intro a b h
  have hz : mul D.g (a - b) = 0 := by
    change (mulHom D.g) (a - b) = 0
    rw [map_sub]
    change mul D.g a - mul D.g b = 0
    rw [h, sub_self]
  exact sub_eq_zero.mp (D.mul_eq_zero (a - b) hz)

/-- Multiplication identifies the free coefficient module with the ideal lattice. -/
noncomputable def multiplicationEquiv : Coeff D.d ≃+ D.lattice :=
  AddEquiv.ofBijective (mulHom D.g).rangeRestrict
    ⟨(fun _ _ h => D.mul_injective (congrArg Subtype.val h)),
      (mulHom D.g).rangeRestrict_surjective⟩

/-- A basis of exactly d vectors. Its j-th column is g times the j-th unit
coefficient vector, i.e. the multiplication basis from `pre.tex`. -/
noncomputable def multiplicationBasis : Module.Basis (Fin D.d) ℤ D.lattice :=
  (Pi.basisFun ℤ (Fin D.d)).map D.multiplicationEquiv.toIntLinearEquiv

end Hardness.ReductionData
