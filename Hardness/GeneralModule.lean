import Hardness.ModuleSIVP
import Hardness.Cyclic
import Hardness.CertificateBound

/-! # Arbitrary independent rank-two cyclotomic bases -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Hardness.ModuleSIVP
open Hardness Hardness.Cyclotomic

variable {d : ℕ} [Fact (∃ k, d = 2^k)]

/-- The integral span map, with the supplied vectors as its columns. -/
def basisMap (u v : QuotRing d × QuotRing d) :
    (QuotRing d × QuotRing d) →ₗ[QuotRing d] (QuotRing d × QuotRing d) where
  toFun a := (u.1*a.1 + v.1*a.2, u.2*a.1 + v.2*a.2)
  map_add' a b := by ext <;> dsimp <;> ring
  map_smul' c a := by ext <;> dsimp <;> ring

def basisSpan (u v : QuotRing d × QuotRing d) := (basisMap u v).range

theorem basisMap_injective_iff (u v : QuotRing d × QuotRing d) :
    Function.Injective (basisMap u v) ↔ Independent u v := by
  rw [independent_iff]
  constructor
  · intro hinj hdet
    have hk (a b : QuotRing d) (h₁ : u.1*a+v.1*b=0) (h₂ : u.2*a+v.2*b=0) :
        (a,b) = (0,0) := by
      apply hinj
      exact Prod.ext (by simpa [basisMap] using h₁) (by simpa [basisMap] using h₂)
    have h := hk v.1 (-u.1) (by ring) (by linear_combination -hdet)
    have hu₁ : u.1 = 0 := by have := congrArg Prod.snd h; simpa using this
    have h := hk v.2 (-u.2) (by linear_combination hdet) (by ring)
    have hu₂ : u.2 = 0 := by have := congrArg Prod.snd h; simpa using this
    have h := hk 1 0 (by simp [hu₁]) (by simp [hu₂])
    exact one_ne_zero (congrArg Prod.fst h)
  · intro hdet a b hab
    have h₁ := congrArg Prod.fst hab
    have h₂ := congrArg Prod.snd hab
    change u.1*a.1 + v.1*a.2 = u.1*b.1 + v.1*b.2 at h₁
    change u.2*a.1 + v.2*a.2 = u.2*b.1 + v.2*b.2 at h₂
    have ha : (u.1*v.2-u.2*v.1)*(a.1-b.1) = 0 := by
      linear_combination v.2*h₁ - v.1*h₂
    have hb : (u.1*v.2-u.2*v.1)*(a.2-b.2) = 0 := by
      linear_combination u.1*h₂ - u.2*h₁
    exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp ha).resolve_left hdet))
      (sub_eq_zero.mp ((mul_eq_zero.mp hb).resolve_left hdet))

/-- The two supplied columns are a free basis of their actual integral span. -/
def generalBasis (u v : QuotRing d × QuotRing d) (h : Independent u v) :
    Module.Basis (Fin 2) (QuotRing d) (basisSpan u v) :=
  (Pi.basisFun (QuotRing d) (Fin 2)).map
    ((LinearEquiv.finTwoArrow (QuotRing d) (QuotRing d)).trans
      (LinearEquiv.ofBijective (basisMap u v).rangeRestrict
        ⟨(fun _ _ hh => (basisMap_injective_iff u v).mpr h (congrArg Subtype.val hh)),
          (by rintro ⟨w,a,rfl⟩; exact ⟨a,rfl⟩)⟩))

theorem generalBasis_columns (u v : QuotRing d × QuotRing d) (h : Independent u v) :
    (generalBasis u v h 0).val = u ∧ (generalBasis u v h 1).val = v := by
  constructor
  · simp only [generalBasis, Module.Basis.map_apply, LinearEquiv.trans_apply,
      LinearEquiv.finTwoArrow_apply, Pi.basisFun_apply]
    change (u.1*1+v.1*0, u.2*1+v.2*0) = u
    simp
  · simp only [generalBasis, Module.Basis.map_apply, LinearEquiv.trans_apply,
      LinearEquiv.finTwoArrow_apply, Pi.basisFun_apply]
    change (u.1*0+v.1*1, u.2*0+v.2*1) = v
    simp

/-- Contiguous ordinary coefficient coordinates for a pair of ring elements. -/
def pairEquiv : Coeff (2*d) ≃ₗ[ℤ] (QuotRing d × QuotRing d) :=
  (LinearEquiv.funCongrLeft ℤ ℤ (Cyclic.blockEquiv d)).trans
    ((LinearEquiv.sumArrowLequivProdArrow (Fin d) (Fin d) ℤ ℤ).trans
      ((quotEquiv dimension_pos).prodCongr (quotEquiv dimension_pos)))

@[simp] theorem pairEquiv_concat (a b : Coeff d) :
    pairEquiv (Cyclic.concat a b) = (toQuot a, toQuot b) := by
  simp [pairEquiv, Cyclic.concat, LinearEquiv.funCongrLeft, LinearMap.funLeft,
    LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow, Function.comp_def]

/-- Integer matrix on the monomial translates of the two supplied columns. -/
def generalMatrix (u v : QuotRing d × QuotRing d) :
    Matrix (Fin (2*d)) (Fin (2*d)) ℤ :=
  LinearMap.toMatrix' (pairEquiv.symm.toLinearMap.comp
    (((basisMap u v).restrictScalars ℤ).comp pairEquiv.toLinearMap))

@[simp] theorem generalMatrix_mulVec (u v : QuotRing d × QuotRing d) (q : Coeff (2*d)) :
    (generalMatrix u v).mulVec q = pairEquiv.symm (basisMap u v (pairEquiv q)) :=
  LinearMap.toMatrix'_mulVec _ _

@[simp] theorem pairEquiv_symm_toQuot (a b : Coeff d) :
    pairEquiv.symm (toQuot a, toQuot b) = Cyclic.concat a b := by
  apply pairEquiv.injective
  simp

theorem generalMatrix_mulVec_concat (a b c e p q : Coeff d) :
    (generalMatrix (toQuot a, toQuot b) (toQuot c, toQuot e)).mulVec
      (Cyclic.concat p q) =
      Cyclic.concat (mul a p + mul c q) (mul b p + mul e q) := by
  rw [generalMatrix_mulVec, pairEquiv_concat]
  change pairEquiv.symm (toQuot a * toQuot p + toQuot c * toQuot q,
    toQuot b * toQuot p + toQuot e * toQuot q) = _
  simp only [← toQuot_mul dimension_pos, ← toQuot_add, pairEquiv_symm_toQuot]

theorem generalMatrix_det_iff (u v : QuotRing d × QuotRing d) :
    (generalMatrix u v).det ≠ 0 ↔ Independent u v := by
  constructor
  · intro h
    apply (basisMap_injective_iff u v).mp
    intro a b hab
    apply pairEquiv.symm.injective
    apply Matrix.mulVec_injective_of_det_ne_zero h
    simpa using congrArg pairEquiv.symm hab
  · intro h hz
    obtain ⟨q,hq,hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
    apply hq
    apply pairEquiv.injective
    apply (basisMap_injective_iff u v).mpr h
    apply pairEquiv.symm.injective
    simpa using hzero

theorem generalMatrix_columns (u v : QuotRing d × QuotRing d) (i : Fin d) :
    pairEquiv (fun r => generalMatrix u v r (Cyclic.blockEquiv d (.inl i))) =
      toQuot (monomial i 1) • u ∧
    pairEquiv (fun r => generalMatrix u v r (Cyclic.blockEquiv d (.inr i))) =
      toQuot (monomial i 1) • v := by
  have hl : (Pi.single (Cyclic.blockEquiv d (.inl i)) 1 : Coeff (2*d)) =
      Cyclic.concat (monomial i 1) 0 := by
    funext r
    obtain ⟨j,rfl⟩ := (Cyclic.blockEquiv d).surjective r
    cases j <;> simp [Pi.single_apply, monomial]
  have hr : (Pi.single (Cyclic.blockEquiv d (.inr i)) 1 : Coeff (2*d)) =
      Cyclic.concat 0 (monomial i 1) := by
    funext r
    obtain ⟨j,rfl⟩ := (Cyclic.blockEquiv d).surjective r
    cases j <;> simp [Pi.single_apply, monomial]
  constructor
  · change pairEquiv ((generalMatrix u v).col _) = _
    rw [← Matrix.mulVec_single_one, generalMatrix_mulVec, LinearEquiv.apply_symm_apply,
      hl, pairEquiv_concat]
    ext <;> simp [basisMap, smul_eq_mul, _root_.mul_comm]
  · change pairEquiv ((generalMatrix u v).col _) = _
    rw [← Matrix.mulVec_single_one, generalMatrix_mulVec, LinearEquiv.apply_symm_apply,
      hr, pairEquiv_concat]
    ext <;> simp [basisMap, smul_eq_mul, _root_.mul_comm]

theorem sqNorm_pairEquiv (q : Coeff (2*d)) :
    vectorNormSq (pairEquiv q) = sqNorm q := by
  obtain ⟨a,b,rfl⟩ := Cyclic.exists_concat q
  simp [vectorNormSq, pairEquiv_concat, Cyclic.sqNorm_concat]

theorem generalMatrix_column_eq (a b c e : Coeff d) (j : Fin d) :
    (fun r => generalMatrix (toQuot a,toQuot b) (toQuot c,toQuot e) r
      (Cyclic.blockEquiv d (.inl j))) = Cyclic.concat (mul a (monomial j 1)) (mul b (monomial j 1)) ∧
    (fun r => generalMatrix (toQuot a,toQuot b) (toQuot c,toQuot e) r
      (Cyclic.blockEquiv d (.inr j))) = Cyclic.concat (mul c (monomial j 1)) (mul e (monomial j 1)) := by
  constructor
  · apply pairEquiv.injective
    rw [pairEquiv_concat]
    simpa [smul_eq_mul, toQuot_mul dimension_pos, _root_.mul_comm] using
      (generalMatrix_columns (toQuot a,toQuot b) (toQuot c,toQuot e) j).1
  · apply pairEquiv.injective
    rw [pairEquiv_concat]
    simpa [smul_eq_mul, toQuot_mul dimension_pos, _root_.mul_comm] using
      (generalMatrix_columns (toQuot a,toQuot b) (toQuot c,toQuot e) j).2

end Hardness.ModuleSIVP
