import Hardness.StrongBounds
import Hardness.SearchToDecision

/-! Executable regression examples; intentionally not imported by `Hardness`. -/
namespace Hardness.Smoke
open Hardness

def oneTriple : X3CInstance where
  q := 1
  n := 1
  q_pos := by omega
  n_pos := by omega
  triples := fun _ => Finset.univ
  triple_card := by intro j; rfl

def repeatedTriple : X3CInstance where
  q := 1
  n := 2
  q_pos := by omega
  n_pos := by omega
  triples := fun _ => Finset.univ
  triple_card := by intro j; rfl

/-- The last three universe elements are uncovered. -/
def noInstance : X3CInstance where
  q := 2
  n := 1
  q_pos := by omega
  n_pos := by omega
  triples := fun _ => {0, 1, 2}
  triple_card := by intro j; decide

def report (I : X3CInstance) : ℕ × ℤ × ℕ × ℕ × Bool := Id.run do
  let D := compileX3C I
  let maxCoeff := (List.ofFn fun i => max (D.generator i).natAbs (D.target i).natAbs).foldl max 0
  return (D.d, D.threshold, maxCoeff, outputLength D,
    decide (maxCoeff ≤ valueBound I.q I.n ∧
      D.threshold.natAbs ≤ valueBound I.q I.n ∧ D.d ≤ valueBound I.q I.n ∧
      outputLength D ≤ encodingBound (inputLength I) ∧
      unaryLength D ≤ encodingBound (inputLength I)))

#eval report oneTriple
#eval report repeatedTriple
#eval report noInstance
#eval verify (multiplicationMatrix (compileX3C oneTriple).generator)
  (compileX3C oneTriple).target (compileX3C oneTriple).threshold
  (oneTriple.reductionData.encode fun _ => true)

#eval let I := oneTriple
  let v := Cyclotomic.mul (x3cToCVP I).g (I.reductionData.encode fun _ => true)
  (I.decode v, I.checkDecoded v)

#eval let I := repeatedTriple
  let v := Cyclotomic.mul (x3cToCVP I).g
    (I.reductionData.encode fun j => decide (j.val = 1))
  (I.decode v, I.checkDecoded v)

#eval noInstance.checkDecoded (fun _ => 0)

end Hardness.Smoke
