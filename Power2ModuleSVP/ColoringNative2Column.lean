import Power2ModuleSVP.ColoringNative2Height

/-! Native exact Rayleigh-score selection. The accumulator is always an
input candidate or the empty zero vector; no iterative arithmetic growth
assumption is needed for this scan. -/
namespace Power2ModuleSVP.ColoringRuntime

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open PartialColoringAlg
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev QuadraticRows := List (ℚ × List ℚ)
def encQuadraticRows : QuadraticRows ↪ List Bool :=
  encList (encPair encColoringRational (encList encColoringRational))
abbrev ScoreInput := ℕ × (QuadraticRows × List ℚ)
def encScoreInput : ScoreInput ↪ List Bool :=
  encPair encUnary (encPair encQuadraticRows (encList encColoringRational))

def energyPrefix (p : ScoreInput) : ℚ :=
  (p.2.1.map fun row => row.1 * dotPrefix (p.1, (row.2, p.2.2)) ^ 2).sum

def scorePrefix (p : ScoreInput) : ℚ :=
  energyPrefix p / dotPrefix (p.1, (p.2.2, p.2.2))

abbrev ColumnParameter := ℕ × QuadraticRows
def encColumnParameter : ColumnParameter ↪ List Bool := encPair encUnary encQuadraticRows
abbrev ColumnInput := ColumnParameter × List (List ℚ)
def encColumnInput : ColumnInput ↪ List Bool :=
  encPair encColumnParameter (encList (encList encColoringRational))

/-- Same tie rule and zero-candidate rule as the original `bestColumn`. -/
def chooseColumn (p : ColumnParameter) (b q : List ℚ) : List ℚ :=
  if dotPrefix (p.1, (q, q)) = 0 then b
  else if dotPrefix (p.1, (b, b)) = 0 ∨
    scorePrefix (p.1, (p.2, q)) ≤ scorePrefix (p.1, (p.2, b)) then q else b

def bestColumnList (p : ColumnInput) : List ℚ :=
  p.2.reverse.foldl (chooseColumn p.1) []

@[fun_prop] theorem energyPrefix_polytime :
    ComputableTidilyInPolyTime energyPrefix encScoreInput encColoringRational := by
  unfold energyPrefix
  apply sum_polytime.comp
  apply mapWithInput (by unfold encScoreInput encQuadraticRows; fun_prop)
  simp only [encScoreInput, encQuadraticRows]
  fun_prop

@[fun_prop] theorem scorePrefix_polytime :
    ComputableTidilyInPolyTime scorePrefix encScoreInput encColoringRational := by
  unfold scorePrefix
  have hd : ComputableTidilyInPolyTime (fun p : ScoreInput => dotPrefix (p.1, (p.2.2, p.2.2)))
      encScoreInput encColoringRational := by
    apply dotPrefix_polytime.comp
    unfold encDotInput encScoreInput
    fun_prop
  fun_prop

@[fun_prop] theorem chooseColumn_polytime :
    ComputableTidilyInPolyTime
      (fun p : (ColumnParameter × List ℚ) × List ℚ => chooseColumn p.1.1 p.1.2 p.2)
      (encPair (encPair encColumnParameter (encList encColoringRational))
        (encList encColoringRational)) (encList encColoringRational) := by
  unfold chooseColumn
  have htest₁ : ComputableTidilyInPolyTime
      (fun p : (ColumnParameter × List ℚ) × List ℚ =>
        decide (dotPrefix (p.1.1.1, (p.2, p.2)) = 0))
      (encPair (encPair encColumnParameter (encList encColoringRational))
        (encList encColoringRational)) encBool := by
    simp only [encColumnParameter]
    fun_prop
  have htest₂ : ComputableTidilyInPolyTime
      (fun p : (ColumnParameter × List ℚ) × List ℚ =>
        decide (dotPrefix (p.1.1.1, (p.1.2, p.1.2)) = 0 ∨
          scorePrefix (p.1.1.1, (p.1.1.2, p.2)) ≤
            scorePrefix (p.1.1.1, (p.1.1.2, p.1.2))))
      (encPair (encPair encColumnParameter (encList encColoringRational))
        (encList encColoringRational)) encBool := by
    simp only [encColumnParameter]
    fun_prop
  exact htest₁.ite_decide (by fun_prop)
    (htest₂.ite_decide (by fun_prop) (by fun_prop))

theorem chooseColumn_mem (p : ColumnParameter) (b q : List ℚ) :
    chooseColumn p b q = b ∨ chooseColumn p b q = q := by
  unfold chooseColumn
  split_ifs <;> simp

/-- Unlike a repeated arithmetic update, selection stores an existing list.
This proves the complete accumulator-size invariant on raw inputs. -/
@[fun_prop] theorem bestColumnList_polytime :
    ComputableTidilyInPolyTime bestColumnList encColumnInput (encList encColoringRational) := by
  unfold bestColumnList
  apply (foldlWith_spec (encP := encColumnParameter) (encA := encList encColoringRational)
    (encL := encList (encList encColoringRational)) (encB := encList encColoringRational)
    (by unfold encColumnInput; fun_prop) (by unfold encColumnInput; fun_prop)
    (const []) chooseColumn_polytime
    (fun (_ : ColumnInput) consumed b => b = [] ∨ b ∈ consumed)
    (by simp) ?_ (size := fun p => (encColumnInput p).length)
    (PolyBounded.of_forall_le 1 1 (by intro p; simp)) ?_).1
  · intro p consumed b q hp hb
    rcases chooseColumn_mem p.1 b q with he | he
    · rw [he]
      rcases hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr (List.mem_append_left _ hb)
    · exact Or.inr (by simp [he])
  · intro p consumed b hp hb
    rcases hb with rfl | hb
    · simp
    · have hmem : b ∈ p.2 := List.mem_reverse.mp (hp.subset hb)
      exact (length_le_encList_of_mem (encList encColoringRational) hmem).trans
        (length_le_encPair_right encColumnParameter (encList (encList encColoringRational)) p)

private theorem range_map_ofFn {α : Type} (r : ℕ) (f : ℕ → α) :
    (List.range r).map f = List.ofFn (fun j : Fin r => f j) := by
  apply List.ext_getElem <;> simp

theorem dotPrefix_read (r : ℕ) (x y : List ℚ) :
    dotPrefix (r, (x, y)) = dot (fun j : Fin r => x.getD j 0) (fun j => y.getD j 0) := by
  simp [dotPrefix, range_map_ofFn, List.sum_ofFn, dot]

def readQuadraticRows (r : ℕ) (a : QuadraticRows) : List (ℚ × Vec r) :=
  a.map fun row => (row.1, fun j => row.2.getD j 0)

theorem energyPrefix_spec (p : ScoreInput) :
    energyPrefix p = energy (readQuadraticRows p.1 p.2.1) (fun j => p.2.2.getD j 0) := by
  simp [energyPrefix, energy, readQuadraticRows, List.map_map, dotPrefix_read, Function.comp_def]

theorem scorePrefix_spec (p : ScoreInput) :
    scorePrefix p = score (readQuadraticRows p.1 p.2.1) (fun j => p.2.2.getD j 0) := by
  simp [scorePrefix, score, energyPrefix_spec, dotPrefix_read]

private theorem bestColumnList_cons (p : ColumnParameter) (q : List ℚ) (qs : List (List ℚ)) :
    bestColumnList (p, q :: qs) = chooseColumn p (bestColumnList (p, qs)) q := by
  simp [bestColumnList, List.reverse_cons, List.foldl_append]

/-- Exact semantic agreement for arbitrary candidate lists, including
wrong lengths and ties. -/
theorem bestColumnList_spec (p : ColumnInput) :
    (fun j : Fin p.1.1 => (bestColumnList p).getD j 0) =
      bestColumn (readQuadraticRows p.1.1 p.1.2) (readConstraints p.1.1 p.2) := by
  obtain ⟨p, qs⟩ := p
  induction qs with
  | nil => funext j; simp [bestColumnList, readConstraints, bestColumn]
  | cons q qs ih =>
    simp only [readConstraints] at ih
    rw [bestColumnList_cons]
    simp only [readConstraints, List.map_cons, bestColumn]
    simp only [chooseColumn, dotPrefix_read, scorePrefix_spec]
    rw [← ih]
    split_ifs <;> rfl

end Power2ModuleSVP.ColoringRuntime
