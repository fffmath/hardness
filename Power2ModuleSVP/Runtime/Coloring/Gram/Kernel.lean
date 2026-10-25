import Power2ModuleSVP.Runtime.Coloring.Gram.Projection

/-!
# Kernel

A nonzero projection residual makes an enlarged rational row Gram
matrix nonsingular. The proof uses a kernel vector and positivity of the
coefficient dot product, with no determinant block reindexing.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime
open PartialColoringAlg
open scoped BigOperators Matrix
set_option maxHeartbeats 500000

theorem rationalGramComplement_annihilate_transpose {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) ℚ) (hG : (A * Aᵀ).det ≠ 0) :
    rationalGramComplement A * Aᵀ = 0 := by
  have h := congrArg Matrix.transpose (rationalGramComplement_annihilate A hG)
  simpa only [Matrix.transpose_mul, rationalGramComplement_symmetric,
    Matrix.transpose_zero] using h

def consRows {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ) (a : Vec r) :
    Matrix (Fin (n + 1)) (Fin r) ℚ := Matrix.of (fun i j => Fin.cases (a j) (fun k => A k j) i)

theorem cons_transpose_mulVec {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ)
    (a : Vec r) (u : Vec (n + 1)) :
    (consRows A a)ᵀ *ᵥ u = u 0 • a + Aᵀ *ᵥ Fin.tail u := by
  funext j
  simp [consRows, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.tail, Matrix.transpose_apply, mul_comm]

/-- Nonsingularity of the enlarged Gram matrix is an elementary kernel
argument, independent of any list implementation or bit-size estimate. -/
theorem gram_cons_det_ne_zero {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ)
    (a : Vec r) (hG : (A * Aᵀ).det ≠ 0)
    (hq : rationalGramComplement A *ᵥ a ≠ 0) :
    (consRows A a * (consRows A a)ᵀ).det ≠ 0 := by
  let B : Matrix (Fin (n + 1)) (Fin r) ℚ := consRows A a
  have hker (u : Vec (n + 1)) (hu : (B * Bᵀ) *ᵥ u = 0) : u = 0 := by
    let v : Vec r := Bᵀ *ᵥ u
    have hv : v = 0 := by
      apply (dot_self_eq_zero v).mp
      change (Bᵀ *ᵥ u) ⬝ᵥ (Bᵀ *ᵥ u) = 0
      rw [Matrix.dotProduct_transpose_mulVec,
        Matrix.mulVec_mulVec, hu, dotProduct_zero]
    have hv' : u 0 • a + Aᵀ *ᵥ Fin.tail u = 0 := by
      rw [← cons_transpose_mulVec]
      exact hv
    have hproject := congrArg (fun z : Vec r => rationalGramComplement A *ᵥ z) hv'
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      rationalGramComplement_annihilate_transpose A hG, Matrix.zero_mulVec,
      add_zero, Matrix.mulVec_zero] at hproject
    have hu0 : u 0 = 0 := (smul_eq_zero.mp hproject).resolve_right hq
    have htail : Aᵀ *ᵥ Fin.tail u = 0 := by simpa [hu0] using hv'
    have hgramtail : (A * Aᵀ) *ᵥ Fin.tail u = 0 := by
      rw [← Matrix.mulVec_mulVec, htail, Matrix.mulVec_zero]
    have hinj : Function.Injective (fun z : Vec n => (A * Aᵀ) *ᵥ z) :=
      Matrix.mulVec_injective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hG))
    have hutail : Fin.tail u = 0 := hinj (hgramtail.trans (Matrix.mulVec_zero _).symm)
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact hu0
    · exact congrFun hutail k
  have hinj : Function.Injective (fun z : Vec (n + 1) => (B * Bᵀ) *ᵥ z) := by
    intro u v huv
    change (B * Bᵀ) *ᵥ u = (B * Bᵀ) *ᵥ v at huv
    have he : (B * Bᵀ) *ᵥ (u - v) = 0 := by
      rw [Matrix.mulVec_sub, huv, sub_self]
    exact sub_eq_zero.mp (hker (u - v) he)
  have hunit := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

end Power2ModuleSVP.ColoringRuntime
