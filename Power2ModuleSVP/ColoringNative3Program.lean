import Power2ModuleSVP.ColoringNative2

/-! List preparation for the concrete partial-coloring program. The bounds
and certificates here apply to raw, possibly malformed, arrays as well. -/
namespace Power2ModuleSVP.ColoringRuntime

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open PartialColoringAlg
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] List.getD dotPrefix normalizeList initialWeight

abbrev PreparationInput := ℕ × (List (List ℚ) × List ℚ)
def encPreparation : PreparationInput ↪ List Bool :=
  encPair encUnary (encPair (encList (encList encColoringRational))
    (encList encColoringRational))

/-- Stored rows pair their threshold with their coefficient array. -/
def prepareRowList (p : PreparationInput) (i : ℕ) : QuadraticRows :=
  let v := p.2.1.getD i []
  let c := p.2.2.getD i 0
  if dotPrefix (p.1, (v, v)) = 0 ∨ 4 * (p.1 : ℚ) < c ^ 2 then []
  else
    let v' := normalizeList (p.1, v)
    [(c, v'), (c, v'.map fun q => -q)]

def prepareList (p : PreparationInput) : QuadraticRows :=
  (List.range p.2.1.length).flatMap (prepareRowList p)

theorem prepareRowList_polytime :
    ComputableTidilyInPolyTime (fun p : PreparationInput × ℕ => prepareRowList p.1 p.2)
      (encPair encPreparation encUnary) encQuadraticRows := by
  let eV := encList (encList encColoringRational)
  let eC := encList encColoringRational
  let hP := fst encPreparation encUnary
  let hi := snd encPreparation encUnary
  let hr := (fst encUnary (encPair eV eC)).comp hP
  let hData := (snd encUnary (encPair eV eC)).comp hP
  let hv := (listGetD (encA := eC) []).comp (((fst eV eC).comp hData).prod hi)
  let hc := (listGetD (encA := encColoringRational) 0).comp (((snd eV eC).comp hData).prod hi)
  have hd := dotPrefix_polytime.comp (hr.prod (hv.prod hv))
  have hz := normalizeList_polytime.comp (hr.prod hv)
  have hrq := natCast_polytime.comp (unary_to_binary.comp hr)
  have hc2 := pow_polytime.comp (hc.prod (const (2 : ℕ)))
  have h4 := mul_polytime.comp ((const (4 : ℚ)).prod hrq)
  have ht := decide_or (decide_eq' hd (const (0 : ℚ))) (lt_polytime.comp (h4.prod hc2))
  have hn := (ComputableTidilyInPolyTime.map neg_polytime).comp hz
  have hfalse := cons' (hc.prod hz) (cons' (hc.prod hn) (const []))
  have hcert := ht.ite_decide
    (condition := fun p : PreparationInput × ℕ =>
      dotPrefix (p.1.1, (p.1.2.1.getD p.2 [], p.1.2.1.getD p.2 [])) = 0 ∨
        4 * (p.1.1 : ℚ) < (p.1.2.2.getD p.2 0) ^ 2)
    (const []) hfalse
  exact hcert.of_enc_eq fun p => congrArg encQuadraticRows (by rfl)

@[fun_prop] theorem prepareList_polytime :
    ComputableTidilyInPolyTime prepareList encPreparation encQuadraticRows := by
  unfold prepareList
  apply flatMapWithInput (encA := encUnary)
  · unfold encPreparation
    fun_prop
  · exact prepareRowList_polytime

private theorem range_map_ofFn {α : Type} (r : ℕ) (f : ℕ → α) :
    (List.range r).map f = List.ofFn (fun j : Fin r => f j) := by
  apply List.ext_getElem <;> simp

/-- Preparation preserves the precise order and both signs of each row. -/
theorem prepareList_spec {r m : ℕ} (V : Fin m → Vec r) (c : Fin m → ℚ) :
    prepareList (r, (List.ofFn fun i => List.ofFn (V i), List.ofFn c)) =
      (prepareRows V c).map (fun row => (row.threshold, List.ofFn row.a)) := by
  simp only [prepareList, List.length_ofFn]
  have hrange : (List.finRange m).map (fun i : Fin m => (i : ℕ)) = List.range m := by
    simp
  rw [← hrange]
  rw [List.flatMap_map]
  simp only [prepareRows, List.map_flatMap]
  congr 1
  funext i
  simp only [prepareRowList, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    Fin.isLt, ↓reduceDIte, Option.getD_some, normalizeList_spec, dotPrefix_ofFn]
  split_ifs <;> simp [List.map_ofFn, Function.comp_def, Pi.neg_def]

/-- Raw arrays are read with the same padding convention as the typed core. -/
theorem prepareList_read (r : ℕ) (V : List (List ℚ)) (c : List ℚ) :
    prepareList (r, (V, c)) =
      (prepareRows (fun i : Fin V.length => fun j : Fin r => (V.getD i []).getD j 0)
        (fun i => c.getD i 0)).map (fun row => (row.threshold, List.ofFn row.a)) := by
  unfold prepareList prepareRows
  have h : (List.finRange V.length).map Fin.val = List.range V.length := by simp
  rw [← h, List.flatMap_map, List.map_flatMap]
  congr 1
  funext i
  simp only [prepareRowList, dotPrefix_read, normalizeList_spec]
  split_ifs <;> simp [List.map_ofFn, Function.comp_def, Pi.neg_def]

/-- Typed initialization has an exact native list implementation. -/
def initializeList (p : ℕ × QuadraticRows) : List ℚ :=
  p.2.map fun row => initialWeight p.1 p.2.length row.1

theorem initializeList_polytime :
    ComputableTidilyInPolyTime initializeList (encPair encUnary encQuadraticRows)
      (encList encColoringRational) := by
  let eRow := encPair encColoringRational (encList encColoringRational)
  let eIn := encPair encUnary encQuadraticRows
  let hP := fst eIn eRow
  have hr : ComputableTidilyInPolyTime (fun p : (ℕ × QuadraticRows) × (ℚ × List ℚ) => p.1.1)
      (encPair eIn eRow) encUnary := (fst encUnary encQuadraticRows).comp hP
  have hm : ComputableTidilyInPolyTime (fun p : (ℕ × QuadraticRows) × (ℚ × List ℚ) => p.1.2.length)
      (encPair eIn eRow) encUnary :=
    (length_list eRow).comp ((snd encUnary encQuadraticRows).comp hP)
  have hc : ComputableTidilyInPolyTime (fun p : (ℕ × QuadraticRows) × (ℚ × List ℚ) => p.2.1)
      (encPair eIn eRow) encColoringRational :=
    (fst encColoringRational (encList encColoringRational)).comp (snd eIn eRow)
  have hbody := initialWeight_polytime.comp ((hr.prod hm).prod hc)
  have hmap := mapWithInput (f := fun p : ℕ × QuadraticRows => fun row : ℚ × List ℚ =>
    initialWeight p.1 p.2.length row.1) (snd encUnary encQuadraticRows) hbody
  exact hmap.of_enc_eq fun p => congrArg (encList encColoringRational) (by rfl)

theorem initializeList_spec {r m : ℕ} (a : Fin m → Row r) :
    initializeList (r, List.ofFn fun i => ((a i).threshold, List.ofFn (a i).a)) =
      List.ofFn (fun i => initialWeight r m (a i).threshold) := by
  simp [initializeList, List.map_ofFn, Function.comp_def]

end Power2ModuleSVP.ColoringRuntime
