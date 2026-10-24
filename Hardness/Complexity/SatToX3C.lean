import Hardness.Complexity.X3CEnumerate
import Hardness.Complexity.SatToX3CSemantic
import Hardness.Complexity.X3CToCVP

/-! # An explicit list implementation of the exact-cover gadget -/
namespace Hardness
open Turing.MultiTapeTM Cslib.Complexity Cslib.Logic.PL
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open scoped List

namespace X3CFast

abbrev Label := ℕ × ℕ × ℕ × ℕ
abbrev Pair := ℕ × ℕ
def encLabel : Label ↪ List Bool := encPair encUnary
  (encPair encUnary (encPair encUnary encUnary))
def encEdge : Pair ↪ List Bool := encPair encUnary encUnary
def encPort : (Pair × ℕ) ↪ List Bool := encPair encEdge encUnary

def positions (S : MaskedSys) (j : ℕ) : List ℕ :=
  (List.range S.rows.length).filter fun i => (S.rows.getD i []).getD j false

def edges (S : MaskedSys) : List Pair :=
  (List.range S.cols).flatMap fun j =>
    (List.range (positions S j).length).map fun k => (j,k)

def ports (S : MaskedSys) : List (Pair × ℕ) := (edges S) ×ˢ (List.range 3)

def nodes (S : MaskedSys) : List Label :=
  (((List.range S.rows.length) ×ˢ (List.range 3)).map fun p => (0,p.1,p.2,0)) ++
  (((ports S) ×ˢ (List.range 3)).map fun p => (p.2+1,p.1.1.1,p.1.1.2,p.1.2))

def columns (S : MaskedSys) : List Label :=
  ((ports S).map fun p => (0,p.1.1,p.1.2,p.2)) ++
  ((ports S).map fun p => (1,p.1.1,p.1.2,p.2)) ++
  ((edges S).map fun p => (2,p.1,p.2,0))

def previous (S : MaskedSys) (j k : ℕ) : ℕ :=
  if k = 0 then (positions S j).length - 1 else k-1

def row (S : MaskedSys) (j k : ℕ) : ℕ := (positions S j).getD k 0

def triple (S : MaskedSys) (c : Label) : Label × Label × Label :=
  let j := c.2.1
  let k := c.2.2.1
  let r := c.2.2.2
  if c.1 = 0 then ((0,row S j k,r,0),(1,j,k,r),(2,j,previous S j k,r))
  else if c.1 = 1 then ((1,j,k,r),(2,j,k,r),(3,j,k,r))
  else ((3,j,k,0),(3,j,k,1),(3,j,k,2))

def encodeTriple (S : MaskedSys) (c : Label) : X3CTriple :=
  let t := triple S c
  ((nodes S).idxOf t.1, (nodes S).idxOf t.2.1, (nodes S).idxOf t.2.2)

def reduce (S : MaskedSys) : X3CList :=
  (S.rows.length + 3*(edges S).length, (columns S).map (encodeTriple S))

open ExactCoverGadget

def edgeLabel {n : ℕ} {K : Fin n → ℕ} (e : Edge K) : Pair := (e.1.val,e.2.val)
def portLabel {n : ℕ} {K : Fin n → ℕ} (p : Port K) : Pair × ℕ := (edgeLabel p.1,p.2.val)
def nodeLabel {M n : ℕ} {K : Fin n → ℕ} : Node (M := M) K → Label
  | .inl (i,r) => (0,i.val,r.val,0)
  | .inr ((e,r),t) => (t.val+1,e.1.val,e.2.val,r.val)
def columnLabel {n : ℕ} {K : Fin n → ℕ} : Column K → Label
  | .inl (e,r) => (0,e.1.val,e.2.val,r.val)
  | .inr (.inl (e,r)) => (1,e.1.val,e.2.val,r.val)
  | .inr (.inr e) => (2,e.1.val,e.2.val,0)

theorem edgeLabel_injective {n : ℕ} {K : Fin n → ℕ} :
    Function.Injective (edgeLabel (K := K)) := by
  rintro ⟨j,k⟩ ⟨j',k'⟩ h
  have hj : j = j' := Fin.ext (congrArg Prod.fst h)
  cases hj
  have hk : k = k' := Fin.ext (congrArg Prod.snd h)
  cases hk
  rfl

theorem nodeLabel_injective {M n : ℕ} {K : Fin n → ℕ} :
    Function.Injective (nodeLabel (M := M) (K := K)) := by
  intro a b h
  rcases a with ⟨i,r⟩ | ⟨⟨e,r⟩,t⟩ <;> rcases b with ⟨i',r'⟩ | ⟨⟨e',r'⟩,t'⟩
  · have hi : i = i' := Fin.ext (congrArg (fun a : Label => a.2.1) h)
    have hr : r = r' := Fin.ext (congrArg (fun a : Label => a.2.2.1) h)
    cases hi; cases hr; rfl
  · have he := congrArg Prod.fst h
    change 0 = t'.val+1 at he
    omega
  · have he := congrArg Prod.fst h
    change t.val+1 = 0 at he
    omega
  · have ht : t = t' := Fin.ext (by have he := congrArg Prod.fst h; dsimp [nodeLabel] at he; omega)
    have he : e = e' := edgeLabel_injective
      (Prod.ext (congrArg (fun a : Label => a.2.1) h)
        (congrArg (fun a : Label => a.2.2.1) h))
    have hr : r = r' := Fin.ext (congrArg (fun a : Label => a.2.2.2) h)
    cases ht; cases he; cases hr; rfl

theorem finRange_val_map (d : ℕ) : (List.finRange d).map Fin.val = List.range d := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp

theorem map_product {A B C D : Type*} (f : A → C) (g : B → D) (l : List A) (k : List B) :
    (l ×ˢ k).map (fun p => (f p.1,g p.2)) = (l.map f) ×ˢ (k.map g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simpa [List.product, List.map_map, Function.comp_def] using
      (congrArg (fun xs => ((k.map fun b => (f a,g b)) ++ xs)) ih)

theorem edges_eq (S : MaskedSys) :
    (edgeEnum (X3COccurrences.sizes S)).map edgeLabel = edges S := by
  unfold edgeEnum edges
  rw [← finRange_val_map S.cols]
  simp only [List.map_flatMap, List.flatMap_map]
  congr 1
  funext j
  rw [← finRange_val_map (positions S j.val).length]
  simp only [List.map_map]
  rfl

theorem ports_eq (S : MaskedSys) :
    (portEnum (X3COccurrences.sizes S)).map portLabel = ports S := by
  change ((edgeEnum (X3COccurrences.sizes S)) ×ˢ List.finRange 3).map
    (fun p => (edgeLabel p.1,p.2.val)) = _
  rw [map_product, edges_eq, finRange_val_map]
  rfl

theorem nodes_eq (S : MaskedSys) :
    (nodeEnum (M := S.rows.length) (X3COccurrences.sizes S)).map nodeLabel = nodes S := by
  unfold nodeEnum nodes
  rw [← ports_eq S, ← finRange_val_map S.rows.length, ← finRange_val_map 3]
  simp only [List.map_append, List.map_map, ← map_product]
  rfl

theorem columns_eq (S : MaskedSys) :
    (columnEnum (X3COccurrences.sizes S)).map columnLabel = columns S := by
  unfold columnEnum columns
  rw [← ports_eq S, ← edges_eq S]
  simp only [List.map_append, List.map_map]
  rfl

theorem previous_eq {k : ℕ} (i : Fin k) :
    ((finRotate k).symm i).val = if i.val = 0 then k-1 else i.val-1 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero i.pos.ne'
  letI : NeZero (m+1) := ⟨by omega⟩
  by_cases hi : i = 0
  · subst i
    have he : (finRotate (m+1)).symm 0 = Fin.last m :=
      (finRotate (m+1)).symm_apply_eq.mpr (finRotate_last (n := m)).symm
    simp [he]
  · have hv : i.val ≠ 0 := fun h => hi (Fin.ext h)
    simp only [hv, ↓reduceIte]
    exact coe_finRotate_symm_of_ne_zero hi

theorem triple_eq (S : MaskedSys) (c : Column (X3COccurrences.sizes S)) :
    triple S (columnLabel c) =
      let t := tripleTuple (X3COccurrences.sizes S) (X3COccurrences.row S) c
      (nodeLabel t.1,nodeLabel t.2.1,nodeLabel t.2.2) := by
  rcases c with ⟨⟨j,k⟩,r⟩ | ⟨⟨j,k⟩,r⟩ | ⟨j,k⟩
  · simp only [triple, columnLabel, tripleTuple, original, internal, nodeLabel,
      ↓reduceIte, row, previous]
    change ((0,(positions S j.val).getD k.val 0,r.val,0),(1,j.val,k.val,r.val),
      (2,j.val,(if k.val = 0 then (positions S j.val).length-1 else k.val-1),r.val)) =
      ((0,(positions S j.val)[k.val],r.val,0),(1,j.val,k.val,r.val),
        (2,j.val,((finRotate (X3COccurrences.sizes S j)).symm k).val,r.val))
    have hk : k.val < (positions S j.val).length := k.isLt
    rw [previous_eq, List.getD_eq_getElem (positions S j.val) 0 hk]
    rfl
  · rfl
  · rfl

theorem reduce_correct (S : MaskedSys) (hw : S.WellFormed)
    (hb : ∀ i, S.toSystem.b i = true) (hμ : ∀ j, S.toSystem.μ j = true) :
    reduce S ∈ X3CLang ↔ S.Feasible := by
  let K := X3COccurrences.sizes S
  letI : BEq (Node (M := S.rows.length) K) := instBEqOfDecidableEq
  let t := tripleTuple K (X3COccurrences.row S)
  let us := nodeEnum (M := S.rows.length) K
  let cs := columnEnum K
  have he : reduce S = (S.rows.length + 3*(edgeEnum K).length,
      cs.map fun c => (us.idxOf (t c).1,us.idxOf (t c).2.1,us.idxOf (t c).2.2)) := by
    unfold reduce
    rw [← edges_eq S, List.length_map, ← columns_eq S, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c _
    simp only [Function.comp_apply]
    unfold encodeTriple
    rw [triple_eq, ← nodes_eq S]
    simp only [idxOf_map_injective _ nodeLabel_injective]
    rfl
  rw [he]
  apply (enumeratedTripleList_correct us cs (nodup_nodeEnum K) (nodup_columnEnum K)
    (mem_nodeEnum K) (mem_columnEnum K) _ (length_nodeEnum K) t (tripleTuple_distinct K _)).trans
  simp only [t, tripleTuple_set]
  change (∃ ξ, Covers K (X3COccurrences.row S) ξ) ↔ _
  rw [ExactCoverGadget.correct, X3COccurrences.solvable_iff S hb hμ]
  exact (and_iff_right hw).symm

attribute [local irreducible] List.getD

@[fun_prop] theorem poly_positions : ComputableTidilyInPolyTime
    (fun p : MaskedSys × ℕ => positions p.1 p.2)
    (encPair encMasked encUnary) (encList encUnary) := by
  unfold positions
  apply filterWithInput (encA := encUnary)
  · fun_prop
  · have hr : ComputableTidilyInPolyTime
        (fun p : (MaskedSys × ℕ) × ℕ => p.1.1.rows.getD p.2 [])
        (encPair (encPair encMasked encUnary) encUnary) (encList encBool) :=
      (listGetD (encA := encList encBool) (encL := encList (encList encBool)) []).comp
        ((Fast.poly_rows.comp (fst _ _).fst').prod (snd _ _))
    exact (listGetD (encA := encBool) (encL := encList encBool) false).comp
      (hr.prod (fst _ _).snd')

@[fun_prop] theorem poly_edges : ComputableTidilyInPolyTime edges encMasked (encList encEdge) := by
  unfold edges encEdge
  apply flatMapWithInput (encA := encUnary) (by fun_prop)
  apply mapWithInput (encA := encUnary) (by fun_prop)
  fun_prop

@[fun_prop] theorem poly_ports : ComputableTidilyInPolyTime ports encMasked (encList encPort) := by
  unfold ports encPort SProd.sprod List.instSProd List.product
  fun_prop

@[fun_prop] theorem poly_nodes : ComputableTidilyInPolyTime nodes encMasked (encList encLabel) := by
  have hg : ComputableTidilyInPolyTime
      (fun S : MaskedSys => (List.range S.rows.length).product (List.range 3))
      encMasked (encList encEdge) := by
    unfold List.product encEdge
    fun_prop
  have hi : ComputableTidilyInPolyTime
      (fun S : MaskedSys => (ports S).product (List.range 3))
      encMasked (encList (encPair encPort encUnary)) := by
    unfold List.product
    fun_prop
  have hf : ComputableTidilyInPolyTime (fun p : Pair => (0,p.1,p.2,0)) encEdge encLabel := by
    unfold encEdge encLabel
    fun_prop
  have hh : ComputableTidilyInPolyTime
      (fun p : (Pair × ℕ) × ℕ => (p.2+1,p.1.1.1,p.1.1.2,p.1.2))
      (encPair encPort encUnary) encLabel := by
    unfold encPort encEdge encLabel
    fun_prop
  exact listAppend' ((ComputableTidilyInPolyTime.map hf).comp hg)
    ((ComputableTidilyInPolyTime.map hh).comp hi)

@[fun_prop] theorem poly_columns : ComputableTidilyInPolyTime columns encMasked (encList encLabel) := by
  unfold columns encLabel
  fun_prop

@[fun_prop] theorem poly_previous : ComputableTidilyInPolyTime
    (fun p : MaskedSys × Pair => previous p.1 p.2.1 p.2.2)
    (encPair encMasked encEdge) encUnary := by
  unfold previous encEdge
  fun_prop

@[fun_prop] theorem poly_row : ComputableTidilyInPolyTime
    (fun p : MaskedSys × Pair => row p.1 p.2.1 p.2.2)
    (encPair encMasked encEdge) encUnary := by
  unfold row encEdge
  fun_prop

set_option maxHeartbeats 2000000 in
@[fun_prop] theorem poly_triple : ComputableTidilyInPolyTime
    (fun p : MaskedSys × Label => triple p.1 p.2)
    (encPair encMasked encLabel) (encPair encLabel (encPair encLabel encLabel)) := by
  let ein := encPair encMasked encLabel
  have hj : ComputableTidilyInPolyTime (fun p : MaskedSys × Label => p.2.2.1) ein encUnary :=
    (snd _ _).snd'.fst'
  have hk : ComputableTidilyInPolyTime (fun p : MaskedSys × Label => p.2.2.2.1) ein encUnary :=
    (snd _ _).snd'.snd'.fst'
  have hi : ComputableTidilyInPolyTime (fun p : MaskedSys × Label => p.2.2.2.2) ein encUnary :=
    (snd _ _).snd'.snd'.snd'
  have hp : ComputableTidilyInPolyTime
      (fun p : MaskedSys × Label => (p.1,(p.2.2.1,p.2.2.2.1))) ein (encPair encMasked encEdge) :=
    (fst _ _).prod (hj.prod hk)
  have hr : ComputableTidilyInPolyTime
      (fun p : MaskedSys × Label => row p.1 p.2.2.1 p.2.2.2.1) ein encUnary := poly_row.comp hp
  have hv : ComputableTidilyInPolyTime
      (fun p : MaskedSys × Label => previous p.1 p.2.2.1 p.2.2.2.1) ein encUnary := poly_previous.comp hp
  have hl (t : ℕ) : ComputableTidilyInPolyTime
      (fun p : MaskedSys × Label => (t,p.2.2.1,p.2.2.2.1,p.2.2.2.2)) ein encLabel :=
    (const t).prod (hj.prod (hk.prod hi))
  have hs (r : ℕ) : ComputableTidilyInPolyTime
      (fun p : MaskedSys × Label => (3,p.2.2.1,p.2.2.2.1,r)) ein encLabel :=
    (const 3).prod (hj.prod (hk.prod (const r)))
  have ho : ComputableTidilyInPolyTime
      (fun p : MaskedSys × Label => (0,row p.1 p.2.2.1 p.2.2.2.1,p.2.2.2.2,0)) ein encLabel :=
    (const 0).prod (hr.prod (hi.prod (const 0)))
  have hv' : ComputableTidilyInPolyTime
      (fun p : MaskedSys × Label => (2,p.2.2.1,previous p.1 p.2.2.1 p.2.2.2.1,p.2.2.2.2))
      ein encLabel := (const 2).prod (hj.prod (hv.prod hi))
  have htag (t : ℕ) : ComputableTidilyInPolyTime
      (fun p : MaskedSys × Label => decide (p.2.1 = t)) ein encBool :=
    decide_eq' (snd _ _).fst' (const t)
  exact ite_decide (htag 0) (ho.prod ((hl 1).prod hv'))
    (ite_decide (htag 1) ((hl 1).prod ((hl 2).prod (hl 3))) ((hs 0).prod ((hs 1).prod (hs 2))))

@[fun_prop] theorem poly_encodeTriple : ComputableTidilyInPolyTime
    (fun p : MaskedSys × Label => encodeTriple p.1 p.2)
    (encPair encMasked encLabel) encX3CTriple := by
  let et := encPair encUnary (encPair encUnary encUnary)
  have hn : ComputableTidilyInPolyTime (fun p : MaskedSys × Label => nodes p.1)
      (encPair encMasked encLabel) (encList encLabel) := poly_nodes.comp (fst _ _)
  have ht : ComputableTidilyInPolyTime
      (fun p : MaskedSys × Label => encodeTriple p.1 p.2)
      (encPair encMasked encLabel) et :=
    (idxOfWithInput hn poly_triple.fst').prod
      ((idxOfWithInput hn poly_triple.snd'.fst').prod
        (idxOfWithInput hn poly_triple.snd'.snd'))
  have hc : ComputableTidilyInPolyTime (fun t : X3CTriple => t) et encX3CTriple :=
    (unary_to_binary.comp (fst _ _)).prod
      ((unary_to_binary.comp (snd _ _).fst').prod (unary_to_binary.comp (snd _ _).snd'))
  exact hc.comp ht

@[fun_prop] theorem poly_reduce : ComputableTidilyInPolyTime reduce encMasked encX3C := by
  unfold reduce encX3C
  fun_prop

end X3CFast

def satToX3C (φ : CNF ℕ) : X3CList := X3CFast.reduce (satToMasked φ)

theorem satToX3C_correct (φ : CNF ℕ) : φ ∈ ExactThreeSAT ↔ satToX3C φ ∈ X3CLang :=
  (satToMasked_correct φ).trans
    (X3CFast.reduce_correct _ (SatToMasked.reduce_wellFormed φ)
      (SatToMasked.reduce_rhs_true φ) (SatToMasked.reduce_mask_true φ)).symm

@[fun_prop] theorem poly_satToX3C : ComputableTidilyInPolyTime satToX3C encCNF encX3C :=
  X3CFast.poly_reduce.comp SatToMasked.poly_reduce

theorem polyTimeReducible_ExactThreeSAT_X3C :
    PolyTimeReducible encCNF encX3C ExactThreeSAT X3CLang :=
  ⟨satToX3C, poly_satToX3C, satToX3C_correct⟩

theorem x3c_npHard : NPHard encX3C X3CLang :=
  ExactThreeSAT_npHard.trans polyTimeReducible_ExactThreeSAT_X3C

theorem x3c_npComplete : NPComplete encX3C X3CLang := ⟨x3c_mem_NP,x3c_npHard⟩

theorem principalCVP_npHard_via_X3C : NPHard encCVP PrincipalCVP :=
  principalCVP_npHard_of_X3CList x3c_npComplete.2

end Hardness
