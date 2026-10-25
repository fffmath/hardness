import Power2ModuleSVP.Runtime.Coloring.Constraints

/-!
# Step

Exact list arithmetic for the stopped partial-coloring walk.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open PartialColoringAlg
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] List.getD

/-- Choose the sign of the normalized direction using its dot product with the point. -/
def orientedList (p : WalkInput) : List ℚ :=
  let z := unorientedDirection (directionDataList p)
  if 0 ≤ dotPrefix (p.1.1, (p.2.1, z)) then z else z.map fun q => -q

/-- Compute the step fraction allowed by one coordinate of a list state. -/
def capacityList (p : (ℕ × ListState) × ℕ) : ℚ :=
  let x := p.1.2.1.getD p.2 0
  let z := p.1.2.2.getD p.2 0
  if 0 < z then (1 - x) / (stepSize p.1.1 * z)
  else if z < 0 then (-1 - x) / (stepSize p.1.1 * z) else 1

/-- Take the minimum coordinate capacity, capped at one. -/
def fractionList (p : ℕ × ListState) : ℚ :=
  ((List.range p.1).map fun j => capacityList (p, j)).foldr min 1

/-- Update the point and rounded row weights using the supplied direction. -/
def nextListWithDirection (p : WalkInput × List ℚ) : ListState :=
  let α := fractionList (p.1.1.1, (p.1.2.1, p.2))
  let y := p.2.map fun q => α * q
  ((List.range p.1.1.1).map (fun j => p.1.2.1.getD j 0 + stepSize p.1.1.1 * y.getD j 0),
   (List.range p.1.1.2.length).map (fun i =>
     let t := stepSize p.1.1.1 * (p.1.1.2.getD i (0, [])).1 *
       dotPrefix (p.1.1.1, ((p.1.1.2.getD i (0, [])).2, y))
     roundUp (mesh p.1.1.1 p.1.1.2.length)
       (p.1.2.2.getD i 0 * dampingList p.1.1 i * (1 + t + t ^ 2))))

/-- Update a list state with its canonically chosen and oriented direction. -/
def nextList (p : WalkInput) : ListState := nextListWithDirection (p, orientedList p)

/-- Test whether at least half of the ambient coordinates have been fixed. -/
def stopList (p : WalkInput) : Bool :=
  decide (p.1.1 ≤ 2 * ((List.range p.1.1).filter fun j =>
    p.2.1.getD j 0 = -1 ∨ p.2.1.getD j 0 = 1).length)

/-- Keep a stopped list state unchanged, or perform its next walk step. -/
def stoppedStep (p : WalkInput) : ListState :=
  if stopList p then p.2 else nextList p

/-- Native polynomial-time certificate for `stepSizeUnary`. -/
@[fun_prop] theorem stepSizeUnary_polytime :
    ComputableTidilyInPolyTime stepSize encUnary encColoringRational := by
  have hr := natCast_polytime.comp unary_to_binary
  have hc := div_polytime.comp ((const (1 : ℚ)).prod (mul_polytime.comp ((const (16 : ℚ)).prod hr)))
  exact hc.of_enc_eq fun r => congrArg encColoringRational (by rfl)

/-- Native polynomial-time certificate for `orientedList`. -/
@[fun_prop] theorem orientedList_polytime
    (hD : CanonicalProjectorDenominatorHypothesis) (hH : HeavyIndicesNativeHypothesis) :
    ComputableTidilyInPolyTime orientedList encWalkInput (encList encColoringRational) := by
  have hz := (unorientedDirection_polytime hD).comp (directionDataList_polytime hH)
  let eL := encList encColoringRational
  let hR := (fst encUnary encQuadraticRows).comp (fst encWalkParameter encListState)
  let hX := (fst eL eL).comp (snd encWalkParameter encListState)
  have hd := dotPrefix_polytime.comp (hR.prod (hX.prod hz))
  have ht := le_polytime.comp ((const (0 : ℚ)).prod hd)
  have hn := (ComputableTidilyInPolyTime.map neg_polytime).comp hz
  have hc := ht.ite_decide (condition := fun p : WalkInput =>
    0 ≤ dotPrefix (p.1.1, (p.2.1, unorientedDirection (directionDataList p)))) hz hn
  exact hc.of_enc_eq fun p => congrArg (encList encColoringRational) (by rfl)

/-- Native polynomial-time certificate for `capacityList`. -/
@[fun_prop] theorem capacityList_polytime :
    ComputableTidilyInPolyTime capacityList
      (encPair (encPair encUnary encListState) encUnary) encColoringRational := by
  let eL := encList encColoringRational
  let eP := encPair encUnary encListState
  let hP := fst eP encUnary
  let hI := snd eP encUnary
  let hR := (fst encUnary encListState).comp hP
  let hS := (snd encUnary encListState).comp hP
  let hX := (listGetD (encA := encColoringRational) 0).comp
    (((fst eL eL).comp hS).prod hI)
  let hZ := (listGetD (encA := encColoringRational) 0).comp
    (((snd eL eL).comp hS).prod hI)
  let hDen := mul_polytime.comp ((stepSizeUnary_polytime.comp hR).prod hZ)
  let hPos := lt_polytime.comp ((const (0 : ℚ)).prod hZ)
  let hNeg := lt_polytime.comp (hZ.prod (const (0 : ℚ)))
  let hUp := div_polytime.comp ((sub_polytime.comp ((const (1 : ℚ)).prod hX)).prod hDen)
  let hDown := div_polytime.comp ((sub_polytime.comp ((const (-1 : ℚ)).prod hX)).prod hDen)
  have hc := hPos.ite_decide
    (condition := fun p : (ℕ × ListState) × ℕ => 0 < p.1.2.2.getD p.2 0)
    hUp (hNeg.ite_decide
      (condition := fun p : (ℕ × ListState) × ℕ => p.1.2.2.getD p.2 0 < 0)
      hDown (const (1 : ℚ)))
  exact hc.of_enc_eq fun p => congrArg encColoringRational (by rfl)

/-- Native polynomial-time certificate for `minRational`. -/
@[fun_prop] theorem minRational_polytime :
    ComputableTidilyInPolyTime (fun p : ℚ × ℚ => min p.1 p.2)
      (encPair encColoringRational encColoringRational) encColoringRational := by
  have ht : ComputableTidilyInPolyTime (fun p : ℚ × ℚ => decide (p.1 ≤ p.2))
      (encPair encColoringRational encColoringRational) encBool := by fun_prop
  exact (ht.ite_decide (condition := fun p : ℚ × ℚ => p.1 ≤ p.2)
    (fst encColoringRational encColoringRational)
    (snd encColoringRational encColoringRational)).of_enc_eq fun p => by
    apply congrArg encColoringRational
    simp only [min_def]

/-- Native polynomial-time certificate for `minimumList`. -/
@[fun_prop] theorem minimumList_polytime :
    ComputableTidilyInPolyTime (fun xs : List ℚ => xs.foldr min 1)
      (encList encColoringRational) encColoringRational := by
  have hf : ComputableTidilyInPolyTime (fun xs : List ℚ => xs.reverse.foldl min 1)
      (encList encColoringRational) encColoringRational := by
    apply (foldl_spec (encA := encColoringRational)
      (encL := encList encColoringRational) (encB := encColoringRational)
      (by fun_prop) (const 1) minRational_polytime
      (fun (_ : List ℚ) consumed b => b = 1 ∨ b ∈ consumed)
      (by simp) ?_ (size := fun xs => (encList encColoringRational xs).length +
        (encColoringRational 1).length)
      ((PolyBounded.of_forall_le 1 1 (by intro xs; simp)).add (.const _)) ?_).1
    · intro xs consumed b q hp hb
      rcases le_total b q with h | h
      · rw [min_eq_left h]
        exact hb.imp_right fun hb => List.mem_append_left _ hb
      · rw [min_eq_right h]
        exact Or.inr (by simp)
    · intro xs consumed b hp hb
      rcases hb with rfl | hb
      · omega
      · have hm : b ∈ xs := List.mem_reverse.mp (hp.subset hb)
        exact (length_le_encList_of_mem encColoringRational hm).trans (by omega)
  exact hf.of_enc_eq fun xs => by
    apply congrArg encColoringRational
    rw [List.foldl_reverse]
    congr 1
    funext a b
    exact min_comm a b

/-- Native polynomial-time certificate for `fractionList`. -/
@[fun_prop] theorem fractionList_polytime :
    ComputableTidilyInPolyTime fractionList (encPair encUnary encListState)
      encColoringRational := by
  have hm := mapWithInput (f := fun p : ℕ × ListState => fun j => capacityList (p, j))
    (range.comp (fst encUnary encListState)) capacityList_polytime
  have hc := minimumList_polytime.comp hm
  exact hc.of_enc_eq fun p => congrArg encColoringRational (by rfl)

/-- Native polynomial-time certificate for `nextListWithDirection`. -/
@[fun_prop] theorem nextListWithDirection_polytime :
    ComputableTidilyInPolyTime nextListWithDirection
      (encPair encWalkInput (encList encColoringRational)) encListState := by
  have hα := fractionList_polytime.comp
    (show ComputableTidilyInPolyTime
      (fun p : WalkInput × List ℚ => (p.1.1.1, (p.1.2.1, p.2)))
      (encPair encWalkInput (encList encColoringRational))
      (encPair encUnary encListState) from by
        unfold encWalkInput encWalkParameter encListState; fun_prop)
  have hy := mapWithInput (f := fun p : WalkInput × List ℚ => fun q : ℚ =>
      fractionList (p.1.1.1, (p.1.2.1, p.2)) * q)
    (snd encWalkInput (encList encColoringRational))
    (mul_polytime.comp ((hα.comp (fst _ encColoringRational)).prod
      (snd _ encColoringRational)))
  let eL := encList encColoringRational
  let eP := encPair encWalkInput eL
  let hBase := fst eP encUnary
  let hWalk := (fst encWalkInput eL).comp hBase
  let hPar := (fst encWalkParameter encListState).comp hWalk
  let hR := (fst encUnary encQuadraticRows).comp hPar
  let hS := (snd encWalkParameter encListState).comp hWalk
  let hX := (fst eL eL).comp hS
  let hW := (snd eL eL).comp hS
  let hI := snd eP encUnary
  let hY := hy.comp hBase
  let hΔ := stepSizeUnary_polytime.comp hR
  let hXi := (listGetD (encA := encColoringRational) 0).comp (hX.prod hI)
  let hYi := (listGetD (encA := encColoringRational) 0).comp (hY.prod hI)
  let hcoord := add_polytime.comp (hXi.prod (mul_polytime.comp (hΔ.prod hYi)))
  let hRow := walkRowAt_polytime.comp (hPar.prod hI)
  let hDot := dotPrefix_polytime.comp (hR.prod (hRow.snd'.prod hY))
  let hT := mul_polytime.comp ((mul_polytime.comp (hΔ.prod hRow.fst')).prod hDot)
  let hT2 := pow_polytime.comp (hT.prod (const (2 : ℕ)))
  let hQuad := add_polytime.comp ((add_polytime.comp ((const (1 : ℚ)).prod hT)).prod hT2)
  let hDamp := dampingList_polytime.comp (hPar.prod hI)
  let hWi := (listGetD (encA := encColoringRational) 0).comp (hW.prod hI)
  let hM := (length_list (encPair encColoringRational eL)).comp
    ((snd encUnary encQuadraticRows).comp hPar)
  let hMesh := mesh_polytime.comp (hR.prod hM)
  let hWeight := roundUp_polytime.comp (hMesh.prod
    (mul_polytime.comp ((mul_polytime.comp (hWi.prod hDamp)).prod hQuad)))
  let hOrigWalk := fst encWalkInput eL
  let hOrigPar := (fst encWalkParameter encListState).comp hOrigWalk
  let hOrigR := (fst encUnary encQuadraticRows).comp hOrigPar
  let hOrigM := (length_list (encPair encColoringRational eL)).comp
    ((snd encUnary encQuadraticRows).comp hOrigPar)
  have hout := (mapWithInput (f := fun p : WalkInput × List ℚ => fun j : ℕ =>
      let α := fractionList (p.1.1.1, (p.1.2.1, p.2))
      let y := p.2.map fun q => α * q
      p.1.2.1.getD j 0 + stepSize p.1.1.1 * y.getD j 0)
    (range.comp hOrigR) hcoord).prod
    (mapWithInput (f := fun p : WalkInput × List ℚ => fun i : ℕ =>
      let α := fractionList (p.1.1.1, (p.1.2.1, p.2))
      let y := p.2.map fun q => α * q
      let t := stepSize p.1.1.1 * (p.1.1.2.getD i (0, [])).1 *
        dotPrefix (p.1.1.1, ((p.1.1.2.getD i (0, [])).2, y))
      roundUp (mesh p.1.1.1 p.1.1.2.length)
        (p.1.2.2.getD i 0 * dampingList p.1.1 i * (1 + t + t ^ 2)))
      (range.comp hOrigM) hWeight)
  exact hout.of_enc_eq fun p => congrArg encListState (by rfl)

/-- Native polynomial-time certificate for `nextList`. -/
@[fun_prop] theorem nextList_polytime
    (hD : CanonicalProjectorDenominatorHypothesis) (hH : HeavyIndicesNativeHypothesis) :
    ComputableTidilyInPolyTime nextList encWalkInput encListState := by
  have hc := nextListWithDirection_polytime.comp
    ((id' (encIn := encWalkInput)).prod (orientedList_polytime hD hH))
  exact hc.of_enc_eq fun p => congrArg encListState (by rfl)

/-- Native polynomial-time certificate for `stopList`. -/
@[fun_prop] theorem stopList_polytime :
    ComputableTidilyInPolyTime stopList encWalkInput encBool := by
  unfold stopList
  have hf : ComputableTidilyInPolyTime
      (fun p : WalkInput => (List.range p.1.1).filter fun j =>
        p.2.1.getD j 0 = -1 ∨ p.2.1.getD j 0 = 1)
      encWalkInput (encList encUnary) := by
    apply filterWithInput (range.comp (by unfold encWalkInput encWalkParameter; fun_prop))
    let eL := encList encColoringRational
    let hP := fst encWalkInput encUnary
    let hS := (snd encWalkParameter encListState).comp hP
    let hX := (fst eL eL).comp hS
    let hI := snd encWalkInput encUnary
    have hq := (listGetD (encA := encColoringRational) 0).comp (hX.prod hI)
    have ht := signTest_polytime.comp hq
    exact ht.of_enc_eq fun p => congrArg encBool (by rfl)
  have hl := (length_list encUnary).comp hf
  unfold encWalkInput encWalkParameter at *
  fun_prop

/-- Native polynomial-time certificate for `stoppedStep`. -/
@[fun_prop] theorem stoppedStep_polytime
    (hD : CanonicalProjectorDenominatorHypothesis) (hH : HeavyIndicesNativeHypothesis) :
    ComputableTidilyInPolyTime stoppedStep encWalkInput encListState := by
  unfold stoppedStep
  exact stopList_polytime.cond (by unfold encWalkInput; fun_prop) (nextList_polytime hD hH)

private theorem range_map_ofFn {α : Type} (r : ℕ) (f : ℕ → α) :
    (List.range r).map f = List.ofFn (fun j : Fin r => f j) := by
  apply List.ext_getElem <;> simp

/-- Encode mathematical walk rows as fixed list parameters. -/
def reifyRows {r m : ℕ} (a : Fin m → Row r) : WalkParameter :=
  (r, List.ofFn fun i => ((a i).threshold, List.ofFn (a i).a))

/-- Encode a mathematical walk state as point and weight lists. -/
def reifyState {r m : ℕ} (s : State r m) : ListState := (List.ofFn s.x, List.ofFn s.w)

/-- List coordinate capacities agree with the mathematical walk capacities. -/
theorem capacityList_spec {r : ℕ} (x z : Vec r) (j : Fin r) :
    capacityList ((r, (List.ofFn x, List.ofFn z)), j) = capacity x z j := by
  simp [capacityList, capacity, List.getD_eq_getElem?_getD]

/-- The list step fraction agrees with the mathematical walk fraction. -/
theorem fractionList_spec {r : ℕ} (x z : Vec r) :
    fractionList (r, (List.ofFn x, List.ofFn z)) = stepFraction x z := by
  simp [fractionList, stepFraction, range_map_ofFn, List.finRange,
    List.map_ofFn, Function.comp_def, capacityList_spec]

/-- The oriented list is the exact reified mathematical walk direction. -/
theorem orientedList_spec {r m : ℕ} (a : Fin m → Row r) (s : State r m) :
    orientedList (reifyRows a, reifyState s) = List.ofFn (direction a s) := by
  have hd := directionDataList_spec a s
  have hC : readConstraints r ((constraints a s).map List.ofFn) = constraints a s := by
    simp [readConstraints, List.map_map, Function.comp_def, List.getD_eq_getElem?_getD]
  have hQ : readQuadraticRows r ((quadraticRows a s).map
      (fun row => (row.1, List.ofFn row.2))) = quadraticRows a s := by
    simp [readQuadraticRows, List.map_map, Function.comp_def, List.getD_eq_getElem?_getD]
  unfold orientedList reifyRows reifyState
  rw [hd, unorientedDirection_spec]
  simp only [walkDirectionInput]
  rw [hC, hQ, dotPrefix_ofFn]
  unfold direction orient
  split_ifs <;> simp [List.map_ofFn, Function.comp_def, Pi.neg_def]

/-- The list update agrees with the mathematical update for the supplied direction. -/
theorem nextListWithDirection_spec {r m : ℕ} (a : Fin m → Row r)
    (s : State r m) (z : Vec r) :
    nextListWithDirection ((reifyRows a, reifyState s), List.ofFn z) =
      reifyState
        { x := s.x + stepSize r • (stepFraction s.x z • z)
          w := fun i =>
            let t := stepSize r * (a i).threshold * dot (a i).a (stepFraction s.x z • z)
            roundUp (mesh r m) (s.w i * damping a i * (1 + t + t ^ 2)) } := by
  simp only [nextListWithDirection, reifyState, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, reifyRows, fractionList_spec, List.map_ofFn, Function.comp_def,
    range_map_ofFn, Fin.is_lt, ↓reduceDIte, Fin.eta, Option.getD_some, List.length_ofFn,
    dampingList, dotPrefix_ofFn, damping, Prod.mk.injEq, List.ofFn_inj]
  constructor <;> funext j <;> rfl

/-- The canonical list update agrees with the mathematical walk step. -/
theorem nextList_spec {r m : ℕ} (a : Fin m → Row r) (s : State r m) :
    nextList (reifyRows a, reifyState s) = reifyState (nextState a s) := by
  unfold nextList
  rw [orientedList_spec, nextListWithDirection_spec]
  rfl

/-- The list stopping test agrees with the mathematical stopping condition. -/
theorem stopList_spec {r m : ℕ} (a : Fin m → Row r) (s : State r m) :
    stopList (reifyRows a, reifyState s) = decide (r ≤ 2 * signCoordinateCount s.x) := by
  have hrange : (List.finRange r).map Fin.val = List.range r := by simp
  have hf : ((List.finRange r).filter (fun j => s.x j = -1 ∨ s.x j = 1)).length =
      signCoordinateCount s.x := by
    rw [← List.toFinset_card_of_nodup (List.nodup_finRange r |>.filter _)]
    simp [signCoordinateCount]
  unfold stopList reifyRows reifyState
  simp only [← hrange, List.filter_map, List.length_map]
  simp only [Function.comp_def, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    Fin.isLt, ↓reduceDIte, Option.getD_some]
  rw [hf]

/-- One stopped list step agrees with the stopped mathematical walk step. -/
theorem stoppedStep_spec {r m : ℕ} (a : Fin m → Row r) (s : State r m) :
    stoppedStep (reifyRows a, reifyState s) = reifyState
      (if r ≤ 2 * signCoordinateCount s.x then s else nextState a s) := by
  unfold stoppedStep
  rw [stopList_spec]
  split_ifs <;> simp_all [nextList_spec]

/-- Iterating the stopped list step agrees with iterating the mathematical walk. -/
theorem stopped_iterate_spec {r m : ℕ} (a : Fin m → Row r) (s : State r m) (k : ℕ) :
    (fun t => stoppedStep (reifyRows a, t))^[k] (reifyState s) =
      reifyState (walk a k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, stoppedStep_spec]
    split_ifs with hs
    · have hstop : ∀ n, walk a n s = s := by
        intro n
        cases n <;> simp [walk, hs]
      rw [ih, hstop, hstop]
    · rw [ih]
      simp [walk, hs]

end Power2ModuleSVP.ColoringRuntime
