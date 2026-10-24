import Hardness.ModuleSIVP
import Hardness.Complexity.NPComplete

/-! # Module-SIVP on separated triangular bases

The input explicitly lists both coordinates of both basis vectors. We restrict
well-formed inputs to `(Q,T),(0,g)`, where `g ≠ 0` and
`Q = 1 + ‖T‖² + ‖g‖²`. This subclass is recognized in polynomial time.
Its language is the actual second field-linear successive minimum predicate.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Hardness
open Turing.MultiTapeTM Cslib.Complexity Hardness.Cyclotomic ModuleSIVP
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

abbrev ModuleSIVPInput := ℕ × ((List ℤ × List ℤ) × ((List ℤ × List ℤ) × ℤ))

def encModuleSIVP : ModuleSIVPInput ↪ List Bool :=
  encPair encUnary (encPair (encPair (encList encIntBin) (encList encIntBin))
    (encPair (encPair (encList encIntBin) (encList encIntBin)) encIntBin))

/-- Binary arithmetic avoids a unary search up to the squared norms. -/
def moduleScale (d : ℕ) (g T : List ℤ) : ℤ :=
  1 + listSqDistance d T [] + listSqDistance d g []

def constantList (d : ℕ) (Q : ℤ) : List ℤ :=
  (List.range d).map fun i => if i = 0 then Q else 0

namespace ModuleSIVPInput
abbrev g (x : ModuleSIVPInput) := x.2.2.1.2
abbrev target (x : ModuleSIVPInput) := x.2.1.2
abbrev gamma (x : ModuleSIVPInput) := x.2.2.2
abbrev scale (x : ModuleSIVPInput) := moduleScale x.1 x.g x.target

def cvp (x : ModuleSIVPInput) : CVPInput :=
  (x.1, x.g, x.target, x.gamma - x.scale^2)

/-- All four coefficient lists are checked, including the two constant columns. -/
def wellFormedCheck (x : ModuleSIVPInput) : Bool :=
  cvpWellFormedCheck x.cvp && x.g.any (fun z => decide (z ≠ 0)) &&
    decide (x.2.1.1 = constantList x.1 x.scale) &&
    decide (x.2.2.1.1 = List.replicate x.1 0) && decide (0 ≤ x.gamma)

def WellFormed (x : ModuleSIVPInput) : Prop := x.wellFormedCheck = true

theorem wellFormed_spec (x : ModuleSIVPInput) : x.WellFormed ↔
    x.cvp.WellFormed ∧ (∃ z ∈ x.g, z ≠ 0) ∧
      x.2.1.1 = constantList x.1 x.scale ∧
      x.2.2.1.1 = List.replicate x.1 0 ∧ 0 ≤ x.gamma := by
  simp [WellFormed, wellFormedCheck, List.any_eq_true, cvpWellFormedCheck_eq, and_assoc]

theorem power_two {x : ModuleSIVPInput} (h : x.WellFormed) : ∃ k, x.1 = 2 ^ k :=
  ((wellFormed_spec x).mp h).1.1

theorem generator_ne_zero {x : ModuleSIVPInput} (h : x.WellFormed) :
    ofList (d := x.1) x.g ≠ 0 := by
  obtain ⟨hw, ⟨z,hz,hne⟩, _⟩ := (wellFormed_spec x).mp h
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hz
  intro hh
  have hi' : i < x.1 := by have := hw.2.1; change x.g.length = x.1 at this; omega
  have hc := congrFun hh ⟨i,hi'⟩
  apply hne
  simpa only [ofList, List.getD_eq_getElem _ _ hi, he, Pi.zero_apply] using hc

end ModuleSIVPInput

theorem moduleScale_bounds (d : ℕ) (g T : List ℤ) :
    0 < moduleScale d g T ∧
    sqNorm (ofList (d := d) T) < moduleScale d g T ^ 2 ∧
    sqNorm (ofList (d := d) g) < moduleScale d g T ^ 2 := by
  have ht := sqNorm_nonneg (ofList (d := d) T)
  have hg := sqNorm_nonneg (ofList (d := d) g)
  have hzero : ofList (d := d) ([] : List ℤ) = 0 := by ext; simp [ofList]
  simp only [moduleScale, listSqDistance_eq, hzero, sub_zero]
  constructor
  · omega
  constructor <;> nlinarith

/-- The semantic problem, with independence over the actual quotient field. -/
def ModuleSIVPLang : Set ModuleSIVPInput := {x | ∃ h : x.WellFormed,
  letI : Fact (∃ k, x.1 = 2 ^ k) := ⟨(ModuleSIVPInput.power_two h)⟩
  SecondMinimumSq (completion (d := x.1) x.scale (toQuot (ofList x.g))
    (toQuot (ofList x.target))) x.gamma}

/-- The central completion equivalence works for arbitrary signed thresholds. -/
theorem separated_secondMinimum_iff {d : ℕ} (hd : ∃ k, d = 2 ^ k)
    (g T : Coeff d) (hg : g ≠ 0) (Q Γ : ℤ)
    (hQ : 0 < Q) (hQT : sqNorm T < Q ^ 2) (hQg : sqNorm g < Q ^ 2) :
    (letI : Fact (∃ k, d = 2 ^ k) := ⟨hd⟩;
      SecondMinimumSq (completion Q (toQuot g) (toQuot T)) Γ) ↔
      CVPYes (principalIdealLattice g) T (Γ - Q ^ 2) := by
  letI : Fact (∃ k, d = 2 ^ k) := ⟨hd⟩
  obtain ⟨δ,hmin⟩ := exists_minimumDistance (toQuot g) (toQuot T)
  have hg' : toQuot g ≠ 0 := by
    intro hh
    exact hg ((toQuot_bijective dimension_pos).injective (hh.trans (toQuot_zero _).symm))
  have hex := module_completion Q hQ (toQuot g) (toQuot T) hg'
    (by simpa using hQT) (by simpa using hQg) hmin
  rw [secondMinimumSq_iff hex]
  constructor
  · intro hh
    obtain ⟨b,hb⟩ := hmin.1
    obtain ⟨b,rfl⟩ := (toQuot_bijective dimension_pos).surjective b
    rw [normSq_residual] at hb
    exact ⟨mul g b, ⟨b,rfl⟩, by omega⟩
  · rintro ⟨v, ⟨b,rfl⟩, hb⟩
    change sqNorm (mul g b - T) ≤ Γ - Q ^ 2 at hb
    have hh := hmin.2 (toQuot b)
    rw [normSq_residual] at hh
    omega

theorem moduleSIVPLang_iff (x : ModuleSIVPInput) :
    x ∈ ModuleSIVPLang ↔ x.WellFormed ∧ x.cvp ∈ PrincipalCVP := by
  constructor
  · rintro ⟨hw,hyes⟩
    refine ⟨hw, (principalCVP_iff x.cvp).mpr ⟨((x.wellFormed_spec).mp hw).1, ?_⟩⟩
    have hb := moduleScale_bounds x.1 x.g x.target
    exact (separated_secondMinimum_iff (ModuleSIVPInput.power_two hw) _ _ (ModuleSIVPInput.generator_ne_zero hw) _ _
      hb.1 hb.2.1 hb.2.2).mp hyes
  · rintro ⟨hw,hyes⟩
    refine ⟨hw, ?_⟩
    have hb := moduleScale_bounds x.1 x.g x.target
    exact (separated_secondMinimum_iff (ModuleSIVPInput.power_two hw) _ _ (ModuleSIVPInput.generator_ne_zero hw) _ _
      hb.1 hb.2.1 hb.2.2).mpr ((principalCVP_iff x.cvp).mp hyes).2

/-- Bridge to the proof-carrying rank-two module problem. -/
noncomputable def ModuleSIVPInput.toInstance (x : ModuleSIVPInput) (h : x.WellFormed) :
    ModuleSIVPInstance := by
  letI : Fact (∃ k, x.1 = 2 ^ k) := ⟨(ModuleSIVPInput.power_two h)⟩
  have hg : toQuot (ofList (d := x.1) x.g) ≠ 0 := by
    intro hh
    exact (ModuleSIVPInput.generator_ne_zero h) ((toQuot_bijective dimension_pos).injective
      (hh.trans (toQuot_zero _).symm))
  exact {
    d := x.1
    power_two := ModuleSIVPInput.power_two h
    module := completion x.scale (toQuot (ofList x.g)) (toQuot (ofList x.target))
    basis := completionBasis x.scale (ne_of_gt (moduleScale_bounds _ _ _).1) _ _ hg
    Γ := x.gamma
    Γ_nonneg := ((x.wellFormed_spec).mp h).2.2.2.2 }

theorem moduleSIVPLang_iff_instance (x : ModuleSIVPInput) (h : x.WellFormed) :
    x ∈ ModuleSIVPLang ↔ (x.toInstance h).Yes := by
  constructor
  · rintro ⟨_,hy⟩; exact hy
  · intro hy; exact ⟨h,hy⟩

@[simp] theorem ofList_constantList {d : ℕ} (Q : ℤ) (i : Fin d) :
    ofList (constantList d Q) i = if i.val = 0 then Q else 0 := by
  simp [ofList, constantList, List.getD_eq_getElem?_getD, i.isLt]

@[simp] theorem toQuot_constantList {d : ℕ} (hd : 0 < d) (Q : ℤ) :
    toQuot (ofList (d := d) (constantList d Q)) = (Q : QuotRing d) := by
  classical
  simp only [toQuot, ofList_constantList]
  rw [Finset.sum_eq_single (⟨0,hd⟩ : Fin d)]
  · simp
  · intro i _ hi
    have hv : i.val ≠ 0 := fun h => hi (Fin.ext h)
    simp [hv]
  · simp

/-- Both stored vectors are exactly the displayed free module basis. -/
theorem ModuleSIVPInput.basis_columns (x : ModuleSIVPInput) (h : x.WellFormed) :
    ((x.toInstance h).basis 0).val =
      (toQuot (ofList (d := x.1) x.2.1.1), toQuot (ofList x.2.1.2)) ∧
    ((x.toInstance h).basis 1).val =
      (toQuot (ofList (d := x.1) x.2.2.1.1), toQuot (ofList x.2.2.1.2)) := by
  letI : Fact (∃ k, x.1 = 2 ^ k) := ⟨ModuleSIVPInput.power_two h⟩
  have hs := (x.wellFormed_spec).mp h
  have hz : ofList (d := x.1) (List.replicate x.1 (0 : ℤ)) = 0 := by
    ext i
    simp [ofList, List.getD_eq_getElem?_getD, List.getElem?_replicate, i.isLt]
  rw [hs.2.2.1, hs.2.2.2.1, toQuot_constantList (d := x.1) (power_two_pos (ModuleSIVPInput.power_two h)), hz, toQuot_zero]
  have hg : toQuot (ofList (d := x.1) x.g) ≠ 0 := by
    intro hh
    exact ModuleSIVPInput.generator_ne_zero h
      ((toQuot_bijective dimension_pos).injective (hh.trans (toQuot_zero _).symm))
  exact completionBasis_columns x.scale (ne_of_gt (moduleScale_bounds _ _ _).1)
    (toQuot (ofList x.g)) (toQuot (ofList x.target)) hg

attribute [local irreducible] List.getD

@[fun_prop] theorem poly_moduleScale : ComputableTidilyInPolyTime
    (fun p : RingArgs => moduleScale p.1 p.2.1 p.2.2) encRingArgs encIntBin := by
  unfold moduleScale encRingArgs
  fun_prop

@[fun_prop] theorem poly_constantList : ComputableTidilyInPolyTime
    (fun p : ℕ × ℤ => constantList p.1 p.2) (encPair encUnary encIntBin)
      (encList encIntBin) := by
  unfold constantList
  fun_prop

@[fun_prop] theorem poly_moduleCVP : ComputableTidilyInPolyTime
    ModuleSIVPInput.cvp encModuleSIVP encCVP := by
  unfold ModuleSIVPInput.cvp ModuleSIVPInput.scale encModuleSIVP encCVP
  fun_prop

@[fun_prop] theorem poly_moduleWellFormedCheck : ComputableTidilyInPolyTime
    ModuleSIVPInput.wellFormedCheck encModuleSIVP encBool := by
  unfold ModuleSIVPInput.wellFormedCheck ModuleSIVPInput.scale encModuleSIVP
  fun_prop

/-- A single CVP multiplier certifies the independent pair `(Q,T-gb),(0,g)`.
Cramer's coefficient and bit bounds are inherited through this total reduction. -/
def moduleToCVP (x : ModuleSIVPInput) : CVPInput :=
  if x.wellFormedCheck then x.cvp else cvpNoInput

theorem moduleToCVP_correct (x : ModuleSIVPInput) :
    x ∈ ModuleSIVPLang ↔ moduleToCVP x ∈ PrincipalCVP := by
  rw [moduleSIVPLang_iff]
  by_cases hw : x.WellFormed
  · simp [moduleToCVP, ModuleSIVPInput.WellFormed] at hw ⊢
    simp [hw]
  · have hc : x.wellFormedCheck ≠ true := hw
    simp [moduleToCVP, hc, hw, cvpNoInput_not_mem]

@[fun_prop] theorem poly_moduleToCVP : ComputableTidilyInPolyTime
    moduleToCVP encModuleSIVP encCVP := by
  unfold moduleToCVP
  fun_prop

theorem moduleSIVP_mem_NP : ModuleSIVPLang ∈ NP encModuleSIVP :=
  (show PolyTimeReducible encModuleSIVP encCVP ModuleSIVPLang PrincipalCVP from
    ⟨moduleToCVP, poly_moduleToCVP, moduleToCVP_correct⟩).mem_NP principalCVP_mem_NP

/-- A bounded certificate consists of the multiplier for the short horizontal
vector; the vertical vector is the second stored basis column. -/
theorem moduleSIVP_bounded_certificate (x : ModuleSIVPInput) (hx : x ∈ ModuleSIVPLang) :
    ∃ q : List ℤ, cvpCheck (moduleToCVP x, q) = true ∧
      (∀ z ∈ q, |z| ≤ cvpCertificateBound (moduleToCVP x)) ∧
      (encList encIntBin q).length ≤ witnessPolynomial.eval (encCVP (moduleToCVP x)).length := by
  have hy := (moduleToCVP_correct x).mp hx
  obtain ⟨q,hq,hbound⟩ := principalCVP_bounded_list _ hy
  refine ⟨q,hq,hbound,?_⟩
  have hlen := intList_encoding_length_le q _ (cvpCertificateBound_nonneg _) hbound
  have hbits := cvpCertificateBound_bits (moduleToCVP x)
  have hd := (cvp_input_length_bounds (moduleToCVP x)).1
  have hqlen := ((cvpCheck_eq _ _).mp hq).2.1
  rw [hqlen] at hlen
  simp only [witnessPolynomial, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one]
  exact hlen.trans (Nat.mul_le_mul hd (by unfold certificateBitBound at hbits; omega))

/-- List-level completion, retaining all four basis-coordinate lists. -/
def completeCVP (x : CVPInput) : ModuleSIVPInput :=
  let Q := moduleScale x.1 x.2.1 x.2.2.1
  (x.1, (constantList x.1 Q, x.2.2.1),
    (List.replicate x.1 0, x.2.1), Q ^ 2 + x.2.2.2)

@[simp] theorem completeCVP_cvp (x : CVPInput) : (completeCVP x).cvp = x := by
  rcases x with ⟨d,g,T,Δ⟩
  simp [completeCVP, ModuleSIVPInput.cvp, ModuleSIVPInput.gamma,
    ModuleSIVPInput.scale, ModuleSIVPInput.g, ModuleSIVPInput.target]

theorem completeCVP_wellFormed (x : CVPInput) (hw : x.WellFormed)
    (hg : ofList (d := x.1) x.2.1 ≠ 0) (hΔ : 0 ≤ x.2.2.2) :
    (completeCVP x).WellFormed := by
  apply ((completeCVP x).wellFormed_spec).mpr
  refine ⟨by simpa using hw, ?_, rfl, rfl, ?_⟩
  · change ∃ z ∈ x.2.1, z ≠ 0
    by_contra! hh
    apply hg
    funext i
    have hi : i.val < x.2.1.length := by rw [hw.2.1]; exact i.isLt
    change x.2.1.getD i.val 0 = 0
    rw [List.getD_eq_getElem _ _ hi]
    exact hh _ (List.getElem_mem hi)
  · exact add_nonneg (sq_nonneg _) hΔ

theorem completeCVP_correct (x : CVPInput) (hw : x.WellFormed)
    (hg : ofList (d := x.1) x.2.1 ≠ 0) (hΔ : 0 ≤ x.2.2.2) :
    x ∈ PrincipalCVP ↔ completeCVP x ∈ ModuleSIVPLang := by
  rw [moduleSIVPLang_iff, completeCVP_cvp, and_iff_right (completeCVP_wellFormed x hw hg hΔ)]

@[fun_prop] theorem poly_completeCVP : ComputableTidilyInPolyTime
    completeCVP encCVP encModuleSIVP := by
  unfold completeCVP encCVP encModuleSIVP
  fun_prop

def moduleNoInput : ModuleSIVPInput := (0, ([],[]), ([],[]), -1)

theorem moduleNoInput_not_mem : moduleNoInput ∉ ModuleSIVPLang := by
  rintro ⟨hw,_⟩
  obtain ⟨k,hk⟩ := ModuleSIVPInput.power_two hw
  have := Nat.two_pow_pos k
  change 0 = 2 ^ k at hk
  omega

def compileModuleFast (S : MaskedSys) : ModuleSIVPInput :=
  if Fast.wellFormed S then completeCVP (Fast.compile S) else moduleNoInput

theorem compileModuleFast_correct (S : MaskedSys) :
    S.Feasible ↔ compileModuleFast S ∈ ModuleSIVPLang := by
  by_cases hw : S.WellFormed
  · rw [compileModuleFast, ite_eq_left ((Fast.wellFormed_eq S).mpr hw), Fast.compile_eq]
    have hC := completeCVP_correct
      (toCVPInput S.reductionDataCubic.toPrincipalCVPInstance)
      (by simp [toCVPInput, CVPInput.WellFormed,
        ReductionData.toPrincipalCVPInstance, S.reductionDataCubic.d_power_two])
      (by
        change ofList (d := S.reductionDataCubic.d) (toList S.reductionDataCubic.g) ≠ 0
        exact fun h => S.reductionDataCubic.g_ne_zero
          ((ofList_toList S.reductionDataCubic.g).symm.trans h))
      (by change 0 ≤ S.reductionDataCubic.Δ; unfold ReductionData.Δ; positivity)
    exact (compileFast_correct S).trans (by rw [compileFast_eq S hw]; exact hC)
  · have hc : Fast.wellFormed S ≠ true := fun h => hw ((Fast.wellFormed_eq S).mp h)
    simp [compileModuleFast, hc, MaskedSys.Feasible, hw, moduleNoInput_not_mem]

@[fun_prop] theorem poly_compileModuleFast : ComputableTidilyInPolyTime
    compileModuleFast encMasked encModuleSIVP := by
  unfold compileModuleFast
  fun_prop

theorem polyTimeReducible_Masked_ModuleSIVP :
    PolyTimeReducible encMasked encModuleSIVP {S | S.Feasible} ModuleSIVPLang :=
  ⟨compileModuleFast, poly_compileModuleFast, compileModuleFast_correct⟩

theorem moduleSIVP_npHard : NPHard encModuleSIVP ModuleSIVPLang :=
  maskedSys_npHard.trans polyTimeReducible_Masked_ModuleSIVP

/-- NP-completeness for the explicitly separated triangular subclass. -/
theorem moduleSIVP_npComplete : NPComplete encModuleSIVP ModuleSIVPLang :=
  ⟨moduleSIVP_mem_NP, moduleSIVP_npHard⟩

end Hardness
