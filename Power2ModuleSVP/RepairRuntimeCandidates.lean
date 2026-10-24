import Power2ModuleSVP.RepairRuntime

/-! List implementations preserving the order and multiplicities of candidates. -/
namespace Power2ModuleSVP.AnchorRepairRuntime
open Turing.MultiTapeTM IdealCVP.Cyclotomic
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] List.getD

abbrev encVectors := encList (encList encIntBin)
abbrev encSupportInput := encPair encUnary (encList encIntBin)

def unitList (d j : ℕ) (z : ℤ) : List ℤ :=
  (List.range d).map fun i => if i = j then z else 0

def atomsList (d : ℕ) : List (List ℤ) :=
  List.replicate d 0 :: (List.range d).flatMap (fun j => [unitList d j 1, unitList d j (-1)])

def atomSumsList (n : ℕ) (d : ℕ) : List (List ℤ) :=
  match n with
  | 0 => [List.replicate d 0]
  | n+1 => (atomSumsList n d).flatMap fun v =>
      (atomsList d).map fun a => IdealCVP.listAdd d v a

def supportList (d : ℕ) (v : List ℤ) : List ℕ :=
  (List.range d).filter fun j => decide (v.getD j 0 ≠ 0)

def squareSum (d : ℕ) (v : List ℤ) : ℤ :=
  ((List.range d).map fun i => (v.getD i 0)^2).sum

def candidateList (n d : ℕ) : List (List ℤ) :=
  (atomSumsList n d).filter fun v =>
    decide (2 ≤ (supportList d v).length ∧ squareSum d v ≤ (n : ℤ))

@[fun_prop] theorem unitList_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × (ℕ × ℤ) => unitList a.1 a.2.1 a.2.2)
    (encPair encUnary (encPair encUnary encIntBin)) (encList encIntBin) := by
  unfold unitList
  fun_prop

@[fun_prop] theorem atomsList_polytime :
    ComputableTidilyInPolyTime atomsList encUnary encVectors := by
  unfold atomsList
  apply cons'
  · fun_prop
  · apply flatMapWithInput (encA := encUnary)
    · fun_prop
    · unfold unitList
      fun_prop

/-- The exponent is fixed before choosing the machine. No recursion in the
unary input degree is hidden in this certificate. -/
@[fun_prop] theorem atomSumsList_polytime (n : ℕ) :
    ComputableTidilyInPolyTime (atomSumsList n) encUnary encVectors := by
  induction n with
  | zero =>
    change ComputableTidilyInPolyTime (fun d => [List.replicate d (0 : ℤ)])
      encUnary encVectors
    fun_prop
  | succ n ih =>
    change ComputableTidilyInPolyTime
      (fun d => (atomSumsList n d).flatMap fun v =>
        (atomsList d).map fun a => IdealCVP.listAdd d v a) encUnary encVectors
    apply flatMapWithInput (encA := encList encIntBin) ih
    apply mapWithInput (encA := encList encIntBin)
    · exact atomsList_polytime.comp (fst _ _)
    · unfold IdealCVP.listAdd
      fun_prop

@[fun_prop] theorem supportList_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × List ℤ => supportList a.1 a.2) encSupportInput (encList encUnary) := by
  unfold supportList encSupportInput
  apply filterWithInput (encA := encUnary)
  · fun_prop
  · simp only [ne_eq, decide_not]
    apply bool_not.comp
    apply intBin_isZero.comp
    fun_prop

@[fun_prop] theorem squareSum_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × List ℤ => squareSum a.1 a.2) encSupportInput encIntBin := by
  unfold squareSum encSupportInput
  fun_prop

@[fun_prop] theorem candidateList_polytime (n : ℕ) :
    ComputableTidilyInPolyTime (candidateList n) encUnary encVectors := by
  unfold candidateList
  apply filterWithInput (encA := encList encIntBin) (atomSumsList_polytime n)
  have hs := supportList_polytime
  have hq := squareSum_polytime
  unfold encSupportInput at hs hq
  fun_prop

theorem unitList_eq (d : ℕ) (j : Fin d) (z : ℤ) :
    unitList d j.val z = IdealCVP.toList (monomial j z) := by
  apply List.ext_getElem
  · simp [unitList]
  · intro i hi hj
    simp [unitList, IdealCVP.toList, monomial, Fin.ext_iff, eq_comm]

theorem zeroList_eq (d : ℕ) :
    List.replicate d (0 : ℤ) = IdealCVP.toList (0 : Coeff d) := by
  change List.replicate d (0 : ℤ) = List.ofFn (fun _ : Fin d => (0 : ℤ))
  simp

theorem listAdd_toList {d : ℕ} (a b : Coeff d) :
    IdealCVP.listAdd d (IdealCVP.toList a) (IdealCVP.toList b) =
      IdealCVP.toList (a+b) := by
  apply List.ext_getElem
  · simp [IdealCVP.listAdd]
  · intro i hi hj
    have hlt : i < d := by simpa using hj
    simp [IdealCVP.listAdd, IdealCVP.toList, List.getD_eq_getElem?_getD,
      hlt]

theorem atomsList_eq (d : ℕ) :
    atomsList d = (AnchorRepair.atoms d).map IdealCVP.toList := by
  unfold atomsList AnchorRepair.atoms
  rw [List.map_cons, ← zeroList_eq, List.map_flatMap]
  have hr : List.range d = (List.finRange d).map Fin.val := by simp
  rw [hr, List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro j hj
  simp only [List.map_cons, List.map_nil, unitList_eq]
  congr 2
  congr 1
  ext i
  by_cases hi : i = j <;> simp [monomial, hi]

theorem atomSumsList_eq (n d : ℕ) :
    atomSumsList n d = (AnchorRepair.atomSums d n).map IdealCVP.toList := by
  induction n with
  | zero => simp [atomSumsList, AnchorRepair.atomSums, zeroList_eq]
  | succ n ih =>
    simp only [atomSumsList, AnchorRepair.atomSums, ih, atomsList_eq,
      List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
    congr 1
    funext v
    apply List.map_congr_left
    intro a ha
    exact listAdd_toList v a

theorem supportList_eq (d : ℕ) (v : List ℤ) :
    (supportList d v).toFinset = AnchorTests.multiplierSupport d v := by
  ext j
  simp [supportList, AnchorTests.multiplierSupport]

theorem supportList_length (d : ℕ) (v : List ℤ) :
    (supportList d v).length = (AnchorTests.multiplierSupport d v).card := by
  rw [← supportList_eq, List.toFinset_card_of_nodup]
  exact List.nodup_range.filter _

theorem squareSum_toList {d : ℕ} (v : Coeff d) :
    squareSum d (IdealCVP.toList v) = IdealCVP.sqNorm v := by
  simp only [squareSum, IdealCVP.list_sum_range, Finset.sum_range,
    IdealCVP.toList, IdealCVP.sqNorm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [List.getD_eq_getElem?_getD, i.isLt]

theorem candidateList_eq (n d : ℕ) :
    candidateList n d = (AnchorRepair.candidates d n).map IdealCVP.toList := by
  unfold candidateList AnchorRepair.candidates
  rw [atomSumsList_eq, List.filter_map]
  congr 1
  apply List.filter_congr
  intro v hv
  dsimp only [Function.comp_def]
  rw [supportList_length, AnchorRepair.testSupport_card, squareSum_toList]
  rfl

/-- A total list bound, including dimensions below three. -/
theorem candidateList_length_le (n d : ℕ) :
    (candidateList n d).length ≤ (1+2*d)^n := by
  rw [candidateList_eq, List.length_map]
  exact AnchorRepair.candidates_length_le d n

theorem candidateList_length_le_pow (n : ℕ) {d : ℕ} (hd : 3 ≤ d) :
    (candidateList n d).length ≤ d^(2*n) := by
  rw [candidateList_eq, List.length_map]
  exact AnchorRepair.candidates_length_le_pow hd

end Power2ModuleSVP.AnchorRepairRuntime
