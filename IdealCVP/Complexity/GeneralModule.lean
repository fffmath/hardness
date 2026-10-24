import IdealCVP.GeneralModule
import IdealCVP.Complexity.SeparatedCyclic

/-! # General rank-two module-SIVP with signed binary data -/
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace IdealCVP
open Turing.MultiTapeTM Cslib.Complexity IdealCVP.Cyclotomic ModuleSIVP
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Padded coefficient addition and subtraction, using exactly `d` entries. -/
def listAdd (d : ℕ) (a b : List ℤ) : List ℤ :=
  (List.range d).map fun i => a.getD i 0 + b.getD i 0

def listSub (d : ℕ) (a b : List ℤ) : List ℤ :=
  (List.range d).map fun i => a.getD i 0 - b.getD i 0

@[simp] theorem ofList_listAdd (d : ℕ) (a b : List ℤ) :
    ofList (d := d) (listAdd d a b) = ofList a + ofList b := by
  ext i
  simp [ofList, listAdd, List.getD_eq_getElem?_getD, i.isLt]

@[simp] theorem ofList_listSub (d : ℕ) (a b : List ℤ) :
    ofList (d := d) (listSub d a b) = ofList a - ofList b := by
  ext i
  simp [ofList, listSub, List.getD_eq_getElem?_getD, i.isLt]

/-- An exact nonzero scan, including the dimension-zero case. -/
theorem list_any_ne_zero (d : ℕ) (l : List ℤ) (hl : l.length = d) :
    l.any (fun z => decide (z ≠ 0)) = true ↔ ofList (d := d) l ≠ 0 := by
  simp only [List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨z,hz,hne⟩ hzero
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hz
    have hi' : i < d := by omega
    have hh := congrFun hzero ⟨i,hi'⟩
    apply hne
    simpa only [ofList, List.getD_eq_getElem _ _ hi, he, Pi.zero_apply] using hh
  · contrapose!
    intro h
    ext i
    have hi : i.val < l.length := by omega
    exact (List.getD_eq_getElem _ _ hi).trans (h _ (List.getElem_mem hi))

/-- Ring representatives of a pair of stored lists. -/
noncomputable def listRingPair (d : ℕ) (p : List ℤ × List ℤ) : QuotRing d × QuotRing d :=
  (toQuot (ofList p.1), toQuot (ofList p.2))

/-- Computable integral determinant; the domain theorem identifies its meaning. -/
def listDet (d : ℕ) (u v : List ℤ × List ℤ) : List ℤ :=
  listSub d (negacyclicMul d u.1 v.2) (negacyclicMul d u.2 v.1)

def listIndependent (d : ℕ) (u v : List ℤ × List ℤ) : Bool :=
  (listDet d u v).any fun z => decide (z ≠ 0)

theorem listIndependent_iff {d : ℕ} [Fact (∃ k, d = 2^k)]
    (u v : List ℤ × List ℤ) :
    listIndependent d u v = true ↔ Independent (listRingPair d u) (listRingPair d v) := by
  rw [listIndependent, list_any_ne_zero d _ (by simp [listDet, listSub]), independent_iff]
  have hsub (a b : Coeff d) : toQuot (a-b) = toQuot a - toQuot b := by
    rw [← quotEquiv_apply dimension_pos, ← quotEquiv_apply dimension_pos,
      ← quotEquiv_apply dimension_pos]
    exact (quotEquiv dimension_pos).map_sub a b
  have he : toQuot (ofList (d := d) (listDet d u v)) =
      (listRingPair d u).1 * (listRingPair d v).2 -
        (listRingPair d u).2 * (listRingPair d v).1 := by
    simp only [listDet, listRingPair, ofList_listSub, ofList_negacyclicMul,
      hsub, toQuot_mul dimension_pos]
  rw [← he]
  simpa only [quotEquiv_apply] using not_congr
    (map_eq_zero_iff (quotEquiv dimension_pos) (quotEquiv dimension_pos).injective).symm

namespace ModuleSIVPInput

def generalCheck (x : ModuleSIVPInput) : Bool :=
  cvpWellFormedCheck (x.1,x.2.1.1,x.2.1.2,x.gamma) &&
    decide (x.2.2.1.1.length = x.1) && decide (x.2.2.1.2.length = x.1) &&
    decide (0 ≤ x.gamma) && listIndependent x.1 x.2.1 x.2.2.1

def GeneralWellFormed (x : ModuleSIVPInput) : Prop := x.generalCheck = true

theorem generalCheck_spec (x : ModuleSIVPInput) : x.GeneralWellFormed ↔
    (∃ k, x.1 = 2^k) ∧ x.2.1.1.length = x.1 ∧ x.2.1.2.length = x.1 ∧
      x.2.2.1.1.length = x.1 ∧ x.2.2.1.2.length = x.1 ∧ 0 ≤ x.gamma ∧
      listIndependent x.1 x.2.1 x.2.2.1 = true := by
  simp [GeneralWellFormed, generalCheck, cvpWellFormedCheck_eq, CVPInput.WellFormed, and_assoc]

theorem general_power_two {x : ModuleSIVPInput} (h : x.GeneralWellFormed) :
    ∃ k, x.1 = 2^k := ((generalCheck_spec x).mp h).1

noncomputable def generalInstance (x : ModuleSIVPInput) (h : x.GeneralWellFormed) :
    ModuleSIVPInstance := by
  letI : Fact (∃ k, x.1 = 2^k) := ⟨general_power_two h⟩
  exact { d := x.1
          power_two := general_power_two h
          module := basisSpan (listRingPair x.1 x.2.1) (listRingPair x.1 x.2.2.1)
          basis := generalBasis _ _ ((listIndependent_iff _ _).mp
            ((generalCheck_spec x).mp h).2.2.2.2.2.2)
          Γ := x.gamma
          Γ_nonneg := ((generalCheck_spec x).mp h).2.2.2.2.2.1 }

end ModuleSIVPInput

/-- The actual second field-linear minimum in the supplied integral module. -/
def ModuleSIVPGeneral : Set ModuleSIVPInput := {x | ∃ h : x.GeneralWellFormed,
  (x.generalInstance h).Yes}

theorem moduleSIVPGeneral_iff_instance (x : ModuleSIVPInput) (h : x.GeneralWellFormed) :
    x ∈ ModuleSIVPGeneral ↔ (x.generalInstance h).Yes := by
  constructor
  · rintro ⟨_,hy⟩; exact hy
  · exact fun hy => ⟨h,hy⟩

/-- Apply the stored basis to two ring multipliers in contiguous order. -/
def moduleProduct (x : ModuleSIVPInput) (q : List ℤ) : List ℤ × List ℤ :=
  (listAdd x.1 (negacyclicMul x.1 x.2.1.1 (q.take x.1))
      (negacyclicMul x.1 x.2.2.1.1 (q.drop x.1)),
   listAdd x.1 (negacyclicMul x.1 x.2.1.2 (q.take x.1))
      (negacyclicMul x.1 x.2.2.1.2 (q.drop x.1)))

abbrev PairRingArgs := ℕ × ((List ℤ × List ℤ) × (List ℤ × List ℤ))
def encPairRingArgs : PairRingArgs ↪ List Bool :=
  encPair encUnary (encPair (encPair (encList encIntBin) (encList encIntBin))
    (encPair (encList encIntBin) (encList encIntBin)))


/-- Check the two reconstructed short vectors. -/
def moduleVectorsCheck (p : PairRingArgs × ℤ) : Bool :=
  decide (listSqDistance p.1.1 p.1.2.1.1 [] + listSqDistance p.1.1 p.1.2.1.2 [] ≤ p.2) &&
  decide (listSqDistance p.1.1 p.1.2.2.1 [] + listSqDistance p.1.1 p.1.2.2.2 [] ≤ p.2) &&
  listIndependent p.1.1 p.1.2.1 p.1.2.2

/-- Certificate: two length-`2d` lists, hence four integral ring multipliers. -/
def moduleGeneralVerifier (p : ModuleSIVPInput × (List ℤ × List ℤ)) : Bool :=
  let x := p.1
  let u := moduleProduct x p.2.1
  let v := moduleProduct x p.2.2
  x.generalCheck && decide (p.2.1.length = 2*x.1) && decide (p.2.2.length = 2*x.1) &&
    moduleVectorsCheck ((x.1,u,v),x.gamma)

/-- Splitting the multiplier list agrees with the contiguous coefficient basis. -/
theorem ofList_split (d : ℕ) (q : List ℤ) :
    Cyclic.concat (ofList (q.take d)) (ofList (q.drop d)) = ofList (d := 2*d) q := by
  ext i
  rw [CyclicFast.concat_apply]
  split_ifs with hi
  · simp [ofList, List.getD_eq_getElem?_getD, List.getElem?_take, hi]
  · simp [ofList, List.getD_eq_getElem?_getD, List.getElem?_drop,
      Nat.add_sub_of_le (by omega : d ≤ i.val)]

theorem listRingPair_moduleProduct (x : ModuleSIVPInput)
    [Fact (∃ k, x.1 = 2^k)] (q : List ℤ) :
    listRingPair x.1 (moduleProduct x q) =
      basisMap (listRingPair x.1 x.2.1) (listRingPair x.1 x.2.2.1)
        (pairEquiv (ofList q)) := by
  rw [← ofList_split, pairEquiv_concat]
  simp [listRingPair, moduleProduct, basisMap, ofList_negacyclicMul,
    ← toQuot_mul dimension_pos, ← toQuot_add]

theorem moduleGeneralVerifier_spec (x : ModuleSIVPInput) (h : x.GeneralWellFormed)
    (q : List ℤ × List ℤ) :
    moduleGeneralVerifier (x,q) = true ↔
      letI : Fact (∃ k, x.1 = 2^k) := ⟨ModuleSIVPInput.general_power_two h⟩
      q.1.length = 2*x.1 ∧ q.2.length = 2*x.1 ∧
      vectorNormSq (listRingPair x.1 (moduleProduct x q.1)) ≤ x.gamma ∧
      vectorNormSq (listRingPair x.1 (moduleProduct x q.2)) ≤ x.gamma ∧
      Independent (listRingPair x.1 (moduleProduct x q.1))
        (listRingPair x.1 (moduleProduct x q.2)) := by
  letI : Fact (∃ k, x.1 = 2^k) := ⟨ModuleSIVPInput.general_power_two h⟩
  have hz : ofList (d := x.1) ([] : List ℤ) = 0 := by ext; simp [ofList]
  simp [moduleGeneralVerifier, moduleVectorsCheck, show x.generalCheck = true from h, listIndependent_iff,
    vectorNormSq, listRingPair, listSqDistance_eq, hz, and_assoc]

theorem moduleGeneral_iff_exists_check (x : ModuleSIVPInput) :
    x ∈ ModuleSIVPGeneral ↔ ∃ q, moduleGeneralVerifier (x,q) = true := by
  constructor
  · rintro ⟨hw,u,⟨a,rfl⟩,v,⟨b,rfl⟩,hind,hu,hv⟩
    letI : Fact (∃ k, x.1 = 2^k) := ⟨ModuleSIVPInput.general_power_two hw⟩
    refine ⟨(toList (pairEquiv.symm a), toList (pairEquiv.symm b)),
      (moduleGeneralVerifier_spec x hw _).mpr ?_⟩
    simp only [length_toList, ofList_toList, listRingPair_moduleProduct,
      LinearEquiv.apply_symm_apply]
    exact ⟨True.intro,True.intro,hu,hv,hind⟩
  · rintro ⟨q,hq⟩
    have hw : x.GeneralWellFormed := by
      have hh := hq
      simp only [moduleGeneralVerifier, Bool.and_eq_true] at hh
      exact hh.1.1.1
    letI : Fact (∃ k, x.1 = 2^k) := ⟨ModuleSIVPInput.general_power_two hw⟩
    obtain ⟨_,_,hu,hv,hind⟩ := (moduleGeneralVerifier_spec x hw q).mp hq
    refine ⟨hw, listRingPair x.1 (moduleProduct x q.1), ?_,
      listRingPair x.1 (moduleProduct x q.2), ?_, hind, hu, hv⟩
    · exact ⟨pairEquiv (ofList q.1), (listRingPair_moduleProduct x q.1).symm⟩
    · exact ⟨pairEquiv (ofList q.2), (listRingPair_moduleProduct x q.2).symm⟩

attribute [local irreducible] List.getD

@[fun_prop] theorem poly_listAdd : ComputableTidilyInPolyTime
    (fun p : RingArgs => listAdd p.1 p.2.1 p.2.2) encRingArgs (encList encIntBin) := by
  unfold listAdd encRingArgs
  fun_prop

@[fun_prop] theorem poly_listSub : ComputableTidilyInPolyTime
    (fun p : RingArgs => listSub p.1 p.2.1 p.2.2) encRingArgs (encList encIntBin) := by
  unfold listSub encRingArgs
  fun_prop


@[fun_prop] theorem poly_listDet : ComputableTidilyInPolyTime
    (fun p : PairRingArgs => listDet p.1 p.2.1 p.2.2) encPairRingArgs (encList encIntBin) := by
  unfold listDet encPairRingArgs
  fun_prop

@[fun_prop] theorem poly_listIndependent : ComputableTidilyInPolyTime
    (fun p : PairRingArgs => listIndependent p.1 p.2.1 p.2.2) encPairRingArgs encBool := by
  unfold listIndependent encPairRingArgs
  fun_prop

@[fun_prop] theorem poly_moduleGeneralCheck : ComputableTidilyInPolyTime
    ModuleSIVPInput.generalCheck encModuleSIVP encBool := by
  unfold ModuleSIVPInput.generalCheck encModuleSIVP
  fun_prop

@[fun_prop] theorem poly_moduleProduct : ComputableTidilyInPolyTime
    (fun p : ModuleSIVPInput × List ℤ => moduleProduct p.1 p.2)
      (encPair encModuleSIVP (encList encIntBin))
      (encPair (encList encIntBin) (encList encIntBin)) := by
  unfold moduleProduct encModuleSIVP
  fun_prop

@[fun_prop] theorem poly_moduleVectorsCheck : ComputableTidilyInPolyTime
    moduleVectorsCheck (encPair encPairRingArgs encIntBin) encBool := by
  unfold moduleVectorsCheck encPairRingArgs
  fun_prop

@[fun_prop] theorem poly_moduleGeneralVerifier : ComputableTidilyInPolyTime
    moduleGeneralVerifier
      (encPair encModuleSIVP (encPair (encList encIntBin) (encList encIntBin))) encBool := by
  let encQ := encPair (encList encIntBin) (encList encIntBin)
  have hx : ComputableTidilyInPolyTime
      (fun p : ModuleSIVPInput × (List ℤ × List ℤ) => p.1)
      (encPair encModuleSIVP encQ) encModuleSIVP := fst _ _
  have hu := poly_moduleProduct.comp (hx.prod ((snd encModuleSIVP encQ).fst'))
  have hv := poly_moduleProduct.comp (hx.prod ((snd encModuleSIVP encQ).snd'))
  have hdim : ComputableTidilyInPolyTime (fun x : ModuleSIVPInput => x.1)
      encModuleSIVP encUnary := by unfold encModuleSIVP; fun_prop
  have hgam : ComputableTidilyInPolyTime (fun x : ModuleSIVPInput => x.gamma)
      encModuleSIVP encIntBin := by unfold encModuleSIVP; fun_prop
  have ho := ((hdim.comp hx).prod (hu.prod hv)).prod (hgam.comp hx)
  have hc := poly_moduleVectorsCheck.comp ho
  have htwod := unary_mul.comp ((const (encIn := encPair encModuleSIVP encQ) (encMid := encUnary) 2).prod (hdim.comp hx))
  have hl := (length_list encIntBin).comp ((snd encModuleSIVP encQ).fst')
  have hr := (length_list encIntBin).comp ((snd encModuleSIVP encQ).snd')
  have hcl := (decide_eq encUnary).comp (hl.prod htwod)
  have hcr := (decide_eq encUnary).comp (hr.prod htwod)
  exact bool_and.comp
    ((bool_and.comp ((bool_and.comp ((poly_moduleGeneralCheck.comp hx).prod hcl)).prod hcr)).prod hc)

/-- A polynomial-time auxiliary diagonal basis used only for the bit estimate. -/
def moduleMagnitude (x : ModuleSIVPInput) : ℤ :=
  1 + listSqDistance x.1 x.2.1.1 [] + listSqDistance x.1 x.2.1.2 [] +
    listSqDistance x.1 x.2.2.1.1 [] + listSqDistance x.1 x.2.2.1.2 []

def moduleBoundInput (x : ModuleSIVPInput) : CVPInput :=
  (2*x.1, constantList (2*x.1) ((2*x.1 : ℕ)*(x.1 : ℤ)*moduleMagnitude x), [], x.gamma)

@[fun_prop] theorem poly_moduleMagnitude : ComputableTidilyInPolyTime
    moduleMagnitude encModuleSIVP encIntBin := by
  unfold moduleMagnitude encModuleSIVP
  fun_prop

@[fun_prop] theorem poly_moduleBoundInput : ComputableTidilyInPolyTime
    moduleBoundInput encModuleSIVP encCVP := by
  unfold moduleBoundInput encModuleSIVP encCVP
  fun_prop

theorem moduleMagnitude_bounds (x : ModuleSIVPInput) :
    0 ≤ moduleMagnitude x ∧
    (∀ i : Fin x.1, |ofList x.2.1.1 i| ≤ moduleMagnitude x) ∧
    (∀ i : Fin x.1, |ofList x.2.1.2 i| ≤ moduleMagnitude x) ∧
    (∀ i : Fin x.1, |ofList x.2.2.1.1 i| ≤ moduleMagnitude x) ∧
    (∀ i : Fin x.1, |ofList x.2.2.1.2 i| ≤ moduleMagnitude x) := by
  have hz : ofList (d := x.1) ([] : List ℤ) = 0 := by ext; simp [ofList]
  have h₁ := sqNorm_nonneg (ofList (d := x.1) x.2.1.1)
  have h₂ := sqNorm_nonneg (ofList (d := x.1) x.2.1.2)
  have h₃ := sqNorm_nonneg (ofList (d := x.1) x.2.2.1.1)
  have h₄ := sqNorm_nonneg (ofList (d := x.1) x.2.2.1.2)
  simp only [moduleMagnitude, listSqDistance_eq, hz, sub_zero]
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩ <;> intro i <;>
    exact (residual_coordinate_le _ i).trans (by omega)

theorem moduleMatrix_entry_bound (x : ModuleSIVPInput) [Fact (∃ k, x.1 = 2^k)]
    (i j : Fin (2*x.1)) :
    |generalMatrix (listRingPair x.1 x.2.1) (listRingPair x.1 x.2.2.1) i j| ≤
      (x.1 : ℤ)*moduleMagnitude x := by
  obtain ⟨hA,h₁,h₂,h₃,h₄⟩ := moduleMagnitude_bounds x
  obtain ⟨i,rfl⟩ := (Cyclic.blockEquiv x.1).surjective i
  obtain ⟨j,rfl⟩ := (Cyclic.blockEquiv x.1).surjective j
  have hc := generalMatrix_column_eq (ofList x.2.1.1) (ofList x.2.1.2)
    (ofList x.2.2.1.1) (ofList (d := x.1) x.2.2.1.2)
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hh := congrFun (hc j).1 (Cyclic.blockEquiv x.1 (.inl i))
      simp only [Cyclic.concat_left] at hh
      rw [show generalMatrix (listRingPair x.1 x.2.1) (listRingPair x.1 x.2.2.1)
        (Cyclic.blockEquiv x.1 (.inl i)) (Cyclic.blockEquiv x.1 (.inl j)) = _ from hh]
      exact multiplicationMatrix_entry_bound _ _ hA h₁ i j
    | inr j =>
      have hh := congrFun (hc j).2 (Cyclic.blockEquiv x.1 (.inl i))
      simp only [Cyclic.concat_left] at hh
      rw [show generalMatrix (listRingPair x.1 x.2.1) (listRingPair x.1 x.2.2.1)
        (Cyclic.blockEquiv x.1 (.inl i)) (Cyclic.blockEquiv x.1 (.inr j)) = _ from hh]
      exact multiplicationMatrix_entry_bound _ _ hA h₃ i j
  | inr i =>
    cases j with
    | inl j =>
      have hh := congrFun (hc j).1 (Cyclic.blockEquiv x.1 (.inr i))
      simp only [Cyclic.concat_right] at hh
      rw [show generalMatrix (listRingPair x.1 x.2.1) (listRingPair x.1 x.2.2.1)
        (Cyclic.blockEquiv x.1 (.inr i)) (Cyclic.blockEquiv x.1 (.inl j)) = _ from hh]
      exact multiplicationMatrix_entry_bound _ _ hA h₂ i j
    | inr j =>
      have hh := congrFun (hc j).2 (Cyclic.blockEquiv x.1 (.inr i))
      simp only [Cyclic.concat_right] at hh
      rw [show generalMatrix (listRingPair x.1 x.2.1) (listRingPair x.1 x.2.2.1)
        (Cyclic.blockEquiv x.1 (.inr i)) (Cyclic.blockEquiv x.1 (.inr j)) = _ from hh]
      exact multiplicationMatrix_entry_bound _ _ hA h₄ i j

theorem moduleBoundInput_dominates (x : ModuleSIVPInput) [Fact (∃ k, x.1 = 2^k)] :
    certificateBound (generalMatrix (listRingPair x.1 x.2.1) (listRingPair x.1 x.2.2.1))
      0 x.gamma ≤ cvpCertificateBound (moduleBoundInput x) := by
  have hd : 0 < 2*x.1 := by have := dimension_pos (d := x.1); omega
  have hA := (moduleMagnitude_bounds x).1
  have hM : 0 ≤ ((2*x.1 : ℕ) : ℤ)*(x.1 : ℤ)*moduleMagnitude x := by positivity
  have hb : basisMagnitude (generalMatrix (listRingPair x.1 x.2.1) (listRingPair x.1 x.2.2.1)) ≤
      basisMagnitude (multiplicationMatrix (ofList (d := 2*x.1) (moduleBoundInput x).2.1)) := by
    calc
      _ ≤ ∑ _i : Fin (2*x.1), ∑ _j : Fin (2*x.1), (x.1 : ℤ)*moduleMagnitude x := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum fun j _ => moduleMatrix_entry_bound x i j
      _ = _ := by
        unfold basisMagnitude moduleBoundInput
        simp only [multiplicationMatrix_constantList hd, apply_ite abs, abs_zero,
          abs_of_nonneg hM]
        simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
        ring
  unfold certificateBound cvpCertificateBound moduleBoundInput
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀
  · have := basisMagnitude_nonneg (generalMatrix (listRingPair x.1 x.2.1) (listRingPair x.1 x.2.2.1))
    have := targetMagnitude_nonneg (0 : Coeff (2*x.1))
    have := abs_nonneg x.gamma
    omega
  · have hz : ofList (d := 2*x.1) ([] : List ℤ) = 0 := by ext; simp [ofList]
    dsimp only [moduleBoundInput] at hb
    rw [hz]
    linarith only [hb]

/-- The recognition determinant, field independence, and integer nonsingularity coincide. -/
theorem moduleGeneral_basis_criteria (x : ModuleSIVPInput) [Fact (∃ k, x.1 = 2^k)] :
    (listIndependent x.1 x.2.1 x.2.2.1 = true ↔
      Independent (listRingPair x.1 x.2.1) (listRingPair x.1 x.2.2.1)) ∧
    (listIndependent x.1 x.2.1 x.2.2.1 = true ↔
      (generalMatrix (listRingPair x.1 x.2.1) (listRingPair x.1 x.2.2.1)).det ≠ 0) :=
  ⟨listIndependent_iff _ _, (listIndependent_iff _ _).trans (generalMatrix_det_iff _ _).symm⟩

/-- Both stored columns are the basis of the proof-carrying general instance. -/
theorem ModuleSIVPInput.generalInstance_columns (x : ModuleSIVPInput) (h : x.GeneralWellFormed) :
    ((x.generalInstance h).basis 0).val = listRingPair x.1 x.2.1 ∧
      ((x.generalInstance h).basis 1).val = listRingPair x.1 x.2.2.1 := by
  letI : Fact (∃ k, x.1 = 2^k) := ⟨ModuleSIVPInput.general_power_two h⟩
  exact generalBasis_columns _ _ ((listIndependent_iff _ _).mp
    ((ModuleSIVPInput.generalCheck_spec x).mp h).2.2.2.2.2.2)

noncomputable def moduleWitnessPolynomial : Polynomial ℕ := 3*witnessPolynomial + 1

/-- Every accepted pair has bounded coefficients: Cramer applies to each short vector. -/
theorem moduleSIVPGeneral_bounded_certificate (x : ModuleSIVPInput) (hx : x ∈ ModuleSIVPGeneral) :
    ∃ q : List ℤ × List ℤ, moduleGeneralVerifier (x,q) = true ∧
      (∀ z ∈ q.1 ++ q.2, |z| ≤ cvpCertificateBound (moduleBoundInput x)) ∧
      (encPair (encList encIntBin) (encList encIntBin) q).length ≤
        moduleWitnessPolynomial.eval (encCVP (moduleBoundInput x)).length := by
  obtain ⟨q,hq⟩ := (moduleGeneral_iff_exists_check x).mp hx
  have hw := hx.1
  letI : Fact (∃ k, x.1 = 2^k) := ⟨ModuleSIVPInput.general_power_two hw⟩
  obtain ⟨hql,hqr,hu,hv,hind⟩ := (moduleGeneralVerifier_spec x hw q).mp hq
  let M := generalMatrix (listRingPair x.1 x.2.1) (listRingPair x.1 x.2.2.1)
  have hdet : M.det ≠ 0 := (moduleGeneral_basis_criteria x).2.mp
    ((ModuleSIVPInput.generalCheck_spec x).mp hw).2.2.2.2.2.2
  have hb (l : List ℤ) (hl : l.length = 2*x.1)
      (hn : vectorNormSq (listRingPair x.1 (moduleProduct x l)) ≤ x.gamma) :
      ∀ z ∈ l, |z| ≤ cvpCertificateBound (moduleBoundInput x) := by
    intro z hz
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hz
    have hi' : i < 2*x.1 := by omega
    have hnorm : sqNorm (M.mulVec (ofList l) - 0) ≤ x.gamma := by
      rw [sub_zero, ← sqNorm_pairEquiv, generalMatrix_mulVec,
        LinearEquiv.apply_symm_apply, ← listRingPair_moduleProduct]
      exact hn
    have hh := (certificate_coeff_le M hdet 0 x.gamma (ofList l) hnorm ⟨i,hi'⟩).trans
      (moduleBoundInput_dominates x)
    simpa only [ofList, List.getD_eq_getElem _ _ hi, he] using hh
  have hbl := hb q.1 hql hu
  have hbr := hb q.2 hqr hv
  have hlen (l : List ℤ) (hl : l.length = 2*x.1)
      (hb : ∀ z ∈ l, |z| ≤ cvpCertificateBound (moduleBoundInput x)) :
      (encList encIntBin l).length ≤ witnessPolynomial.eval (encCVP (moduleBoundInput x)).length := by
    have hh := intList_encoding_length_le l _ (cvpCertificateBound_nonneg _) hb
    have hbits := cvpCertificateBound_bits (moduleBoundInput x)
    have hn := (cvp_input_length_bounds (moduleBoundInput x)).1
    rw [hl] at hh
    simp only [witnessPolynomial, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one]
    exact hh.trans (Nat.mul_le_mul hn (by unfold certificateBitBound at hbits; omega))
  refine ⟨q,hq,?_,?_⟩
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hbl z hz
    · exact hbr z hz
  · have hl := hlen q.1 hql hbl
    have hr := hlen q.2 hqr hbr
    simp only [length_encPair, moduleWitnessPolynomial, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]
    omega

theorem moduleSIVPGeneral_mem_NP : ModuleSIVPGeneral ∈ NP encModuleSIVP := by
  obtain ⟨p,hp⟩ := poly_moduleBoundInput.polyBounded_length.exists_polynomial
  have he : ModuleSIVPGeneral = {x | ∃ q, moduleGeneralVerifier (x,q) = true} := by
    ext x; exact moduleGeneral_iff_exists_check x
  rw [he]
  apply mem_NP_of_witness (p := moduleWitnessPolynomial.comp p)
    (intBinDecoder.list.pair intBinDecoder.list) poly_moduleGeneralVerifier (fun _ _ => Iff.rfl)
  intro x q hq
  obtain ⟨q',hq',_,hlen⟩ := moduleSIVPGeneral_bounded_certificate x
    ((moduleGeneral_iff_exists_check x).mpr ⟨q,hq⟩)
  refine ⟨q',hq',hlen.trans ?_⟩
  rw [Polynomial.eval_comp]
  exact moduleWitnessPolynomial.eval_mono (hp x)

/-- Identify the triangular subclass's stored columns with its old completion. -/
theorem ModuleSIVPInput.triangular_columns (x : ModuleSIVPInput) (h : x.WellFormed) :
    listRingPair x.1 x.2.1 = ((x.scale : QuotRing x.1), toQuot (ofList x.target)) ∧
      listRingPair x.1 x.2.2.1 = (0,toQuot (ofList x.g)) := by
  have hs := (x.wellFormed_spec).mp h
  have hz : ofList (d := x.1) (List.replicate x.1 (0 : ℤ)) = 0 := by
    ext i
    simp [ofList, List.getD_eq_getElem?_getD, List.getElem?_replicate, i.isLt]
  simp only [listRingPair, hs.2.2.1, hs.2.2.2.1,
    toQuot_constantList (power_two_pos (ModuleSIVPInput.power_two h)), hz, toQuot_zero,
    ModuleSIVPInput.target, ModuleSIVPInput.g, and_self]

theorem ModuleSIVPInput.triangular_generalWellFormed (x : ModuleSIVPInput) (h : x.WellFormed) :
    x.GeneralWellFormed := by
  letI : Fact (∃ k, x.1 = 2^k) := ⟨ModuleSIVPInput.power_two h⟩
  obtain ⟨hc,hg,hQ,hzero,hΓ⟩ := (x.wellFormed_spec).mp h
  apply (x.generalCheck_spec).mpr
  refine ⟨hc.1, ?_, hc.2.2, ?_, hc.2.1, hΓ, ?_⟩
  · rw [hQ]; simp [constantList]
  · rw [hzero]; simp
  · rw [listIndependent_iff, (x.triangular_columns h).1, (x.triangular_columns h).2,
      independent_iff]
    simp only [MulZeroClass.mul_zero, sub_zero, ne_eq, mul_eq_zero, not_or]
    refine ⟨intCast_ne_zero (ne_of_gt (moduleScale_bounds _ _ _).1), ?_⟩
    intro hh
    exact ModuleSIVPInput.generator_ne_zero h
      ((toQuot_bijective dimension_pos).injective (hh.trans (toQuot_zero _).symm))

theorem triangular_basisSpan {d : ℕ} [Fact (∃ k, d = 2^k)]
    (Q : ℤ) (g T : QuotRing d) :
    basisSpan ((Q : QuotRing d),T) (0,g) = completion Q g T := by
  unfold basisSpan completion
  congr 1
  ext a <;> simp [basisMap, completionMap]

theorem moduleSIVPGeneral_triangular (x : ModuleSIVPInput) (h : x.WellFormed) :
    x ∈ ModuleSIVPLang ↔ x ∈ ModuleSIVPGeneral := by
  letI : Fact (∃ k, x.1 = 2^k) := ⟨ModuleSIVPInput.power_two h⟩
  rw [moduleSIVPLang_iff_instance x h,
    moduleSIVPGeneral_iff_instance x (x.triangular_generalWellFormed h)]
  change SecondMinimumSq (d := x.1)
      (completion x.scale (toQuot (ofList x.g)) (toQuot (ofList x.target))) x.gamma ↔
    SecondMinimumSq (d := x.1)
      (basisSpan (listRingPair x.1 x.2.1) (listRingPair x.1 x.2.2.1)) x.gamma
  rw [(x.triangular_columns h).1, (x.triangular_columns h).2, triangular_basisSpan]

theorem moduleNoInput_not_general : moduleNoInput ∉ ModuleSIVPGeneral := by
  rintro ⟨hw,_⟩
  obtain ⟨k,hk⟩ := ModuleSIVPInput.general_power_two hw
  have := Nat.two_pow_pos k
  change 0 = 2^k at hk
  omega

/-- Identity on the recognized triangular subclass, with an explicit malformed fallback. -/
def moduleToGeneral (x : ModuleSIVPInput) : ModuleSIVPInput :=
  if x.wellFormedCheck then x else moduleNoInput

theorem moduleToGeneral_correct (x : ModuleSIVPInput) :
    x ∈ ModuleSIVPLang ↔ moduleToGeneral x ∈ ModuleSIVPGeneral := by
  by_cases hw : x.WellFormed
  · simpa [moduleToGeneral, show x.wellFormedCheck = true from hw] using
      moduleSIVPGeneral_triangular x hw
  · have hc : x.wellFormedCheck ≠ true := hw
    have hn : x ∉ ModuleSIVPLang := fun h => hw h.1
    simp [moduleToGeneral,hc,hn,moduleNoInput_not_general]

@[fun_prop] theorem poly_moduleToGeneral : ComputableTidilyInPolyTime
    moduleToGeneral encModuleSIVP encModuleSIVP := by
  unfold moduleToGeneral
  fun_prop

theorem polyTimeReducible_ModuleSIVP_General :
    PolyTimeReducible encModuleSIVP encModuleSIVP ModuleSIVPLang ModuleSIVPGeneral :=
  ⟨moduleToGeneral,poly_moduleToGeneral,moduleToGeneral_correct⟩

theorem moduleSIVPGeneral_npHard : NPHard encModuleSIVP ModuleSIVPGeneral :=
  moduleSIVP_npHard.trans polyTimeReducible_ModuleSIVP_General

/-- NP-completeness for every independent rank-two integral cyclotomic basis. -/
theorem moduleSIVPGeneral_npComplete : NPComplete encModuleSIVP ModuleSIVPGeneral :=
  ⟨moduleSIVPGeneral_mem_NP,moduleSIVPGeneral_npHard⟩

end IdealCVP
