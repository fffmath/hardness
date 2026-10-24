import IdealCVP.Complexity.SatToX3C
import IdealCVP.Cyclic

/-! # Principal cyclic CVP and a certified lift of the masked compiler

The first input coordinate is the half-dimension d: coefficients represent the
actual quotient ℤ[X]/(X^(2d)-1). NP membership for arbitrary cyclic generators
is not asserted here.
-/
namespace IdealCVP
open Turing.MultiTapeTM Cslib.Complexity
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

def PrincipalCyclicCVP : Set CVPInput := {x |
  (∃ k : ℕ, x.1 = 2^k) ∧ x.2.1.length = 2*x.1 ∧ x.2.2.1.length = 2*x.1 ∧
    ∃ w : Coeff (2*x.1), Cyclic.toRing w ∈ Ideal.span {Cyclic.toRing (ofList x.2.1)} ∧
      sqNorm (w - ofList x.2.2.1) ≤ x.2.2.2}

theorem cyclic_list_mem_iff {d : ℕ} (hd : ∃ k, d = 2^k)
    (g T : Coeff d) (B H : ℤ) :
    (d,toList (Cyclic.generator (Cyclotomic.power_two_pos hd) g B),
      toList (Cyclic.lift T),8*H) ∈ PrincipalCyclicCVP ↔
      CVPYes (Cyclic.lattice (Cyclotomic.power_two_pos hd) g B) (Cyclic.lift T) (8*H) := by
  simp only [PrincipalCyclicCVP, Set.mem_setOf_eq, length_toList, ofList_toList,
    and_self, true_and, hd]
  unfold CVPYes
  simp only [Cyclic.mem_lattice]

namespace CyclicFast

abbrev d (S : MaskedSys) : ℕ := 2*Fast.N S
def H (S : MaskedSys) : ℕ := (Fast.P S)^2 * Fast.weight S + Fast.nu S
def B (S : MaskedSys) : ℕ := 2*Fast.sqrtCeil (H S+4)+1

def gCoeff (S : MaskedSys) (r : ℕ) : ℤ :=
  if r < d S then Fast.gCoeff S r + (if r = 0 then (B S : ℤ) else 0)
  else -Fast.gCoeff S (r-d S) + (if r-d S = 0 then (B S : ℤ) else 0)

def TCoeff (S : MaskedSys) (r : ℕ) : ℤ :=
  if r < d S then 2*Fast.TCoeff S r else -2*Fast.TCoeff S (r-d S)

def compile (S : MaskedSys) : CVPInput :=
  (d S,(List.range (2*d S)).map (gCoeff S),
    (List.range (2*d S)).map (TCoeff S),8*(H S : ℤ))

theorem H_eq (S : MaskedSys) : (H S : ℤ) = S.reductionDataCubic.Δ := by
  simp [H, Fast.P_eq, Fast.weight_eq, Fast.nu_eq, ReductionData.Δ]

theorem B_eq (S : MaskedSys) : (B S : ℤ) = Cyclic.penalty (S.reductionDataCubic.Δ+4) := by
  rw [← H_eq]
  simp only [B, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Cyclic.penalty, Fast.sqrtCeil_eq]
  rw [show ((H S : ℤ)+4).toNat = H S+4 by omega]
  norm_num


theorem concat_apply {d : ℕ} (a b : Coeff d) (r : Fin (2*d)) :
    Cyclic.concat a b r =
      if h : r.val < d then a ⟨r.val,h⟩ else b ⟨r.val-d,by omega⟩ := by
  obtain ⟨i,rfl⟩ := (Cyclic.blockEquiv d).surjective r
  rcases i with i | i
  · have hv : (Cyclic.blockEquiv d (.inl i)).val = i.val := by
      simp [Cyclic.blockEquiv, finSumFinEquiv]
    simp [hv, i.isLt]
  · have hv : (Cyclic.blockEquiv d (.inr i)).val = d+i.val := by
      simp [Cyclic.blockEquiv, finSumFinEquiv, Nat.add_comm]
    simp [hv, show ¬d+i.val < d by omega]

theorem gCoeff_eq (S : MaskedSys) (r : Fin (2*S.reductionDataCubic.d)) :
    gCoeff S r.val = Cyclic.generator
      (Cyclotomic.power_two_pos S.reductionDataCubic.d_power_two)
      S.reductionDataCubic.g (B S) r := by
  have hone (i : Fin S.reductionDataCubic.d) : (B S : ℤ) *
      Cyclic.one (Cyclotomic.power_two_pos S.reductionDataCubic.d_power_two) i =
        if i.val = 0 then (B S : ℤ) else 0 := by
    by_cases hi : i.val = 0 <;> simp [Cyclic.one, Cyclotomic.monomial, Fin.ext_iff, hi]
  rw [Cyclic.generator, concat_apply]
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, hone]
  change gCoeff S r.val = if h : r.val < d S then
    S.reductionDataCubic.g ⟨r.val,h⟩ + (if r.val = 0 then (B S : ℤ) else 0)
    else -S.reductionDataCubic.g ⟨r.val-d S,by have := r.isLt; change r.val < 2*d S at this; omega⟩ +
      (if r.val-d S = 0 then (B S : ℤ) else 0)
  unfold gCoeff
  by_cases h : r.val < d S
  · rw [if_pos h, dif_pos h, Fast.gCoeff_eq S ⟨r.val,h⟩]
  · rw [if_neg h, dif_neg h]
    have hi : r.val-d S < d S := by have := r.isLt; change r.val < 2*d S at this; omega
    rw [Fast.gCoeff_eq S ⟨r.val-d S,hi⟩]

theorem TCoeff_eq (S : MaskedSys) (r : Fin (2*S.reductionDataCubic.d)) :
    TCoeff S r.val = Cyclic.lift S.reductionDataCubic.T r := by
  rw [Cyclic.lift, concat_apply]
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  change TCoeff S r.val = if h : r.val < d S then 2*S.reductionDataCubic.T ⟨r.val,h⟩
    else -(2*S.reductionDataCubic.T ⟨r.val-d S,
      by have := r.isLt; change r.val < 2*d S at this; omega⟩)
  unfold TCoeff
  by_cases h : r.val < d S
  · rw [if_pos h, dif_pos h, Fast.TCoeff_eq S ⟨r.val,h⟩]
  · rw [if_neg h, dif_neg h]
    have hi : r.val-d S < d S := by have := r.isLt; change r.val < 2*d S at this; omega
    rw [Fast.TCoeff_eq S ⟨r.val-d S,hi⟩]
    ring

theorem compile_eq (S : MaskedSys) : compile S =
    (S.reductionDataCubic.d,
      toList (Cyclic.generator (Cyclotomic.power_two_pos S.reductionDataCubic.d_power_two)
        S.reductionDataCubic.g (B S)),toList (Cyclic.lift S.reductionDataCubic.T),
        8*S.reductionDataCubic.Δ) := by
  unfold compile
  rw [H_eq]
  exact Prod.ext rfl (Prod.ext (Fast.map_range_eq_toList _ _ (gCoeff_eq S))
    (Prod.ext (Fast.map_range_eq_toList _ _ (TCoeff_eq S)) rfl))

theorem compile_correct (S : MaskedSys) (hw : S.WellFormed) :
    S.Feasible ↔ compile S ∈ PrincipalCyclicCVP := by
  rw [compile_eq, cyclic_list_mem_iff S.reductionDataCubic.d_power_two]
  have hp : 4*S.reductionDataCubic.Δ < (B S : ℤ)^2 := by
    rw [B_eq]
    have hH : 0 ≤ S.reductionDataCubic.Δ+4 := by unfold ReductionData.Δ; positivity
    have := Cyclic.penalty_sq_gt _ hH
    omega
  rw [Cyclic.cvp_iff _ _ _ _ _ hp]
  have h := compileFast_correct S
  rw [compileFast_eq S hw, toCVPInput_mem_iff] at h
  exact h

@[fun_prop] theorem poly_H : ComputableTidilyInPolyTime H encMasked encUnary := by
  unfold H
  fun_prop

@[fun_prop] theorem poly_B : ComputableTidilyInPolyTime B encMasked encUnary := by
  unfold B
  fun_prop

@[fun_prop] theorem poly_gCoeff : ComputableTidilyInPolyTime
    (fun p : MaskedSys × ℕ => gCoeff p.1 p.2) (encPair encMasked encUnary) encIntBin := by
  unfold gCoeff d
  fun_prop

@[fun_prop] theorem poly_TCoeff : ComputableTidilyInPolyTime
    (fun p : MaskedSys × ℕ => TCoeff p.1 p.2) (encPair encMasked encUnary) encIntBin := by
  unfold TCoeff d
  fun_prop

@[fun_prop] theorem poly_compile : ComputableTidilyInPolyTime compile encMasked encCVP := by
  unfold compile d encCVP
  fun_prop

end CyclicFast

def cyclicNoInput : CVPInput := (1,[0,0],[0,0],-1)

theorem cyclicNoInput_not_mem : cyclicNoInput ∉ PrincipalCyclicCVP := by
  rintro ⟨_,_,_,w,_,hw⟩
  have := sqNorm_nonneg (w-ofList cyclicNoInput.2.2.1)
  change _ ≤ (-1 : ℤ) at hw
  omega

def compileCyclicFast (S : MaskedSys) : CVPInput :=
  if Fast.wellFormed S then CyclicFast.compile S else cyclicNoInput

theorem compileCyclicFast_correct (S : MaskedSys) :
    S.Feasible ↔ compileCyclicFast S ∈ PrincipalCyclicCVP := by
  by_cases hw : S.WellFormed
  · rw [compileCyclicFast, if_pos ((Fast.wellFormed_eq S).mpr hw)]
    exact CyclicFast.compile_correct S hw
  · have hc : Fast.wellFormed S ≠ true := fun h => hw ((Fast.wellFormed_eq S).mp h)
    simp only [compileCyclicFast, hc, MaskedSys.Feasible, hw, false_and]
    exact (iff_false_intro cyclicNoInput_not_mem).symm

@[fun_prop] theorem poly_compileCyclicFast : ComputableTidilyInPolyTime
    compileCyclicFast encMasked encCVP := by
  unfold compileCyclicFast
  fun_prop

theorem polyTimeReducible_Masked_CyclicCVP :
    PolyTimeReducible encMasked encCVP {S | S.Feasible} PrincipalCyclicCVP :=
  ⟨compileCyclicFast,poly_compileCyclicFast,compileCyclicFast_correct⟩

theorem principalCyclicCVP_npHard : NPHard encCVP PrincipalCyclicCVP :=
  maskedSys_npHard.trans polyTimeReducible_Masked_CyclicCVP

end IdealCVP
