import Hardness.Complexity.X3CVerifier
import Hardness.Complexity.SatToMasked

/-! # The paper's incidence-system route from list X3C to principal CVP -/
namespace Hardness
open Turing.MultiTapeTM Cslib.Complexity
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

namespace X3CList

/-- The X3C incidence matrix, with all-one rhs and mask. -/
def incidenceSystem (x : X3CList) : MaskedSys :=
  (x.2.length, (List.range (3*x.1)).map (fun u => x.2.map (incident u)),
    List.replicate (3*x.1) true, List.replicate x.2.length true)

theorem incidenceSystem_wellFormed (x : X3CList) : (incidenceSystem x).WellFormed := by
  simp [incidenceSystem, MaskedSys.WellFormed, MaskedSys.cols, MaskedSys.rows,
    MaskedSys.rhs, MaskedSys.mask]

theorem incidenceSystem_correct (x : X3CList) :
    (incidenceSystem x).Feasible ↔ x.HasExactCover := by
  have hA (i : Fin (3*x.1)) (j : Fin x.2.length) :
      ((((List.range (3*x.1)).map (fun u => x.2.map (incident u))).getD i.val []).getD
        j.val false) = incident i.val x.2[j.val] := by
    simp [List.getD_eq_getElem?_getD, i.isLt, j.isLt]
  have hb (i : Fin (3*x.1)) : (List.replicate (3*x.1) true).getD i.val false = true := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, i.isLt]
  constructor
  · rintro ⟨_, ξ, _, hr⟩
    refine ⟨ξ, fun u => ?_⟩
    have he := congrFun hr ⟨u.val, by simp [MaskedSys.rows, incidenceSystem]⟩
    change (∑ j : Fin x.2.length,
      bit ((((List.range (3*x.1)).map (fun u => x.2.map (incident u))).getD u.val []).getD
        j.val false) * bit (ξ j)) -
        bit ((List.replicate (3*x.1) true).getD u.val false) = 0 at he
    simpa only [hA u, hb u, bit_true, sub_eq_zero] using he
  · rintro ⟨ξ, hξ⟩
    refine ⟨incidenceSystem_wellFormed x, ξ, ?_, ?_⟩
    · intro j _
      change (List.replicate x.2.length true).getD j.val false = true
      have hj : j.val < x.2.length := j.isLt
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hj]
    · funext i
      have hi : i.val < 3*x.1 := by simpa [MaskedSys.rows, incidenceSystem] using i.isLt
      change (∑ j : Fin x.2.length,
        bit ((((List.range (3*x.1)).map (fun u => x.2.map (incident u))).getD i.val []).getD
          j.val false) * bit (ξ j)) -
          bit ((List.replicate (3*x.1) true).getD i.val false) = 0
      simp only [hA ⟨i.val,hi⟩, hb ⟨i.val,hi⟩, bit_true, hξ ⟨i.val,hi⟩, sub_self]

attribute [local irreducible] List.getD

@[fun_prop] theorem poly_incidenceSystem : ComputableTidilyInPolyTime
    incidenceSystem encX3C encMasked := by
  have hrow : ComputableTidilyInPolyTime
      (fun p : X3CList × ℕ => p.1.2.map (incident p.2))
      (encPair encX3C encUnary) (encList encBool) := by
    apply mapWithInput (encA := encX3CTriple)
    · unfold encX3C
      fun_prop
    · have hp : ComputableTidilyInPolyTime
          (fun p : (X3CList × ℕ) × X3CTriple => (p.1.2, p.2))
          (encPair (encPair encX3C encUnary) encX3CTriple)
          (encPair encNat encX3CTriple) :=
        (unary_to_binary.comp (fst _ _).snd').prod (snd _ _)
      exact poly_incident.comp hp
  unfold incidenceSystem encMasked encX3C
  fun_prop

end X3CList

/-- Invalid list inputs map to the fixed inconsistent system. -/
def x3cToMasked (x : X3CList) : MaskedSys :=
  if X3CList.wellFormedCheck x then x.incidenceSystem else SatToMasked.noSystem

theorem x3cToMasked_correct (x : X3CList) :
    x ∈ X3CLang ↔ (x3cToMasked x).Feasible := by
  by_cases hw : x.WellFormed
  · rw [x3cToMasked, if_pos ((X3CList.wellFormedCheck_eq x).mpr hw),
      X3CList.incidenceSystem_correct]
    exact and_iff_right hw
  · have hc : X3CList.wellFormedCheck x ≠ true :=
      fun h => hw ((X3CList.wellFormedCheck_eq x).mp h)
    simp only [X3CLang, Set.mem_setOf_eq, hw, false_and, x3cToMasked, hc, ↓reduceIte]
    exact (iff_false_intro SatToMasked.noSystem_not_feasible).symm

@[fun_prop] theorem poly_x3cToMasked : ComputableTidilyInPolyTime
    x3cToMasked encX3C encMasked := by
  unfold x3cToMasked
  fun_prop

def compileX3CList (x : X3CList) : CVPInput := compileFast (x3cToMasked x)

theorem compileX3CList_correct (x : X3CList) :
    x ∈ X3CLang ↔ compileX3CList x ∈ PrincipalCVP :=
  (x3cToMasked_correct x).trans (compileFast_correct _)

@[fun_prop] theorem poly_compileX3CList : ComputableTidilyInPolyTime
    compileX3CList encX3C encCVP := poly_compileFast.comp poly_x3cToMasked

theorem polyTimeReducible_X3C_CVP :
    PolyTimeReducible encX3C encCVP X3CLang PrincipalCVP :=
  ⟨compileX3CList, poly_compileX3CList, compileX3CList_correct⟩

/-- List-level paper route; only the combinatorial hardness premise remains. -/
theorem principalCVP_npHard_of_X3CList (hX3C : NPHard encX3C X3CLang) :
    NPHard encCVP PrincipalCVP := hX3C.trans polyTimeReducible_X3C_CVP

end Hardness
