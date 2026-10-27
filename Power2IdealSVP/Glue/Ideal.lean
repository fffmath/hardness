import Power2IdealSVP.Runtime.Structure
import Power2IdealSVP.Glue.Source
import Power2IdealSVP.Ideal.Construction

/-!
# Executable reduction and the ideal construction

The list program agrees, intermediate by intermediate, with the coefficient construction.
The sparse polynomial is interpreted directly from the runtime array, leaving equation (1)
to the separate Spin development. All identities here hold even outside the main case.

Paper: `paper/power2-ideal-svp.pdf`, Section 1.5, equations (2) and (3).
-/

namespace Power2IdealSVP.Glue

open Cslib.Complexity Power2ModuleSVP IdealCVP.Cyclotomic
open Power2IdealSVP.Algebra

attribute [local irreducible] Runtime.spinCoeffs Runtime.wallCoeffs Runtime.clockCoeffs
  Runtime.dominantCoeffs Runtime.generatorCoeffs Runtime.parityCoeffs

/-- The runtime dimension is larger than one, so its literal `X` has no wraparound. -/
theorem degree_one_lt (x : Graph × ℕ) : 1 < Runtime.degree x := by
  have := Runtime.degree_gt x
  omega

/-- Positive dimension used by all ideal-layer constructions. -/
theorem degree_pos (x : Graph × ℕ) : 0 < Runtime.degree x :=
  lt_trans (by decide) (degree_one_lt x)

/-- The runtime sparse-spin polynomial, interpreted in the coefficient model. -/
def runtimeG (x : Graph × ℕ) : Coeff (Runtime.degree x) :=
  IdealCVP.ofList (Runtime.spinCoeffs x)

/-- The computed sparse-spin threshold as an integer. -/
def runtimeTau (x : Graph × ℕ) : ℤ := Runtime.spinThreshold x

/-- The runtime threshold satisfies the clock's sole sign requirement. -/
theorem runtimeTau_nonneg (x : Graph × ℕ) : 0 ≤ runtimeTau x :=
  Int.natCast_nonneg _

private theorem ofList_range {n : ℕ} (f : ℕ → ℤ) (i : Fin n) :
    IdealCVP.ofList ((List.range n).map f) i = f i := by
  simp [IdealCVP.ofList, List.getD_eq_getElem?_getD, i.isLt]

/-- Natural list one-norm and integer coefficient one-norm agree on exact arrays. -/
theorem listNorm_toList {n : ℕ} (a : Coeff n) :
    (Runtime.listNorm (IdealCVP.toList a) : ℤ) = coeffL1 a := by
  simp [Runtime.listNorm, IdealCVP.toList, coeffL1,
    List.map_ofFn, List.sum_ofFn]

/-- Every exact-length list has the same one-norm as its coefficient interpretation. -/
theorem listNorm_eq_coeffL1 {n : ℕ} (a : List ℤ) (ha : a.length = n) :
    (Runtime.listNorm a : ℤ) = coeffL1 (IdealCVP.ofList (d := n) a) := by
  subst n
  rw [← listNorm_toList, IdealCVP.toList_ofList]

/-- The literal list `[1,-1]` is `1-X` in the runtime dimension. -/
theorem difference_eq (x : Graph × ℕ) :
    IdealCVP.ofList (d := Runtime.degree x) ([1, -1] : List ℤ) =
      Ideal.difference (degree_pos x) := by
  have hn := degree_one_lt x
  funext i
  by_cases h0 : i.val = 0
  · simp [IdealCVP.ofList, Ideal.difference, Ideal.xPoly, hn, coeffOne, monomial,
      List.getD_eq_getElem?_getD, Fin.ext_iff, h0]
  · by_cases h1 : i.val = 1
    · simp [IdealCVP.ofList, Ideal.difference, Ideal.xPoly, hn, coeffOne, monomial,
        List.getD_eq_getElem?_getD, Fin.ext_iff, h1]
    · have hout : ([1, -1] : List ℤ).length ≤ i.val := by simp; omega
      simp [IdealCVP.ofList, Ideal.difference, Ideal.xPoly, hn, coeffOne, monomial,
        List.getD_eq_getElem?_getD, Fin.ext_iff, h0, h1, List.getElem?_eq_none hout]

/-- Runtime `H` is exactly the ideal layer's perturbation `G(1-X)`. -/
theorem wallCoeffs_eq_perturbation (x : Graph × ℕ) :
    IdealCVP.ofList (Runtime.wallCoeffs x) =
      Ideal.perturbation (degree_pos x) (runtimeG x) := by
  rw [Runtime.wallCoeffs_eq, difference_eq]
  rfl

/-- Runtime `R_H` is the exact coefficient one-norm, including cancellations. -/
theorem wallNorm_eq (x : Graph × ℕ) :
    (Runtime.wallNorm x : ℤ) = Ideal.perturbationNorm (degree_pos x) (runtimeG x) := by
  unfold Runtime.wallNorm
  rw [listNorm_eq_coeffL1 (n := Runtime.degree x) _
    (by simp [Runtime.wallCoeffs]), wallCoeffs_eq_perturbation]
  rfl

/-- Runtime `B` is the clock amplitude. -/
theorem clockAmplitude_eq (x : Graph × ℕ) :
    (Runtime.clockAmplitude x : ℤ) =
      Ideal.clockAmplitude (degree_pos x) (runtimeG x) (runtimeTau x) := by
  simp only [Runtime.clockAmplitude, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    wallNorm_eq, Ideal.clockAmplitude, runtimeTau]

/-- Runtime `K` is the full-sign clock multiplier `BX+H`. -/
theorem clockCoeffs_eq_constructedK (x : Graph × ℕ) :
    IdealCVP.ofList (Runtime.clockCoeffs x) =
      Ideal.constructedK (degree_pos x) (runtimeG x) (runtimeTau x) := by
  have hn := degree_one_lt x
  have hH := wallCoeffs_eq_perturbation x
  funext i
  rw [Runtime.clockCoeffs, ofList_range]
  have hi := congrFun hH i
  simp only [IdealCVP.ofList] at hi
  rw [hi]
  simp [Ideal.constructedK, Ideal.clockMultiplier, Ideal.perturbation,
    Ideal.xPoly, hn, monomial, clockAmplitude_eq, Fin.ext_iff]

/-- Runtime `R_K` is the exact coefficient one-norm of the clock multiplier. -/
theorem clockNorm_eq (x : Graph × ℕ) :
    (Runtime.clockNorm x : ℤ) =
      Ideal.clockNorm (degree_pos x) (runtimeG x) (runtimeTau x) := by
  unfold Runtime.clockNorm
  rw [listNorm_eq_coeffL1 (n := Runtime.degree x) _ (by simp [Runtime.clockCoeffs]),
    clockCoeffs_eq_constructedK]
  rfl

/-- Runtime `M` is the dominating amplitude `3 R_K+1`. -/
theorem dominantAmplitude_eq (x : Graph × ℕ) :
    (Runtime.dominantAmplitude x : ℤ) =
      Ideal.constructedM (degree_pos x) (runtimeG x) (runtimeTau x) := by
  simp only [Runtime.dominantAmplitude, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    clockNorm_eq, Ideal.constructedM, Ideal.amplitude, Ideal.clockNorm]

/-- The replicated all-one list is the parity generator `S`. -/
theorem parityCoeffs_eq_sumPoly (x : Graph × ℕ) :
    IdealCVP.ofList (Runtime.parityCoeffs x) = Ideal.sumPoly (Runtime.degree x) := by
  funext i
  simp [Runtime.parityCoeffs, IdealCVP.ofList, Ideal.sumPoly,
    List.getD_eq_getElem?_getD, i.isLt]

/-- The runtime factor `M-K` agrees with the ideal-layer factor. -/
theorem dominantCoeffs_eq (x : Graph × ℕ) :
    IdealCVP.ofList (Runtime.dominantCoeffs x) =
      Ideal.constructedM (degree_pos x) (runtimeG x) (runtimeTau x) •
        coeffOne (degree_pos x) -
      Ideal.constructedK (degree_pos x) (runtimeG x) (runtimeTau x) := by
  have hK := clockCoeffs_eq_constructedK x
  funext i
  rw [Runtime.dominantCoeffs, ofList_range]
  have hi := congrFun hK i
  simp only [IdealCVP.ofList] at hi
  rw [hi]
  simp [dominantAmplitude_eq, coeffOne, monomial, Fin.ext_iff]

/-- The output generator is exactly `(M-K)S` from the ideal construction. -/
theorem generatorCoeffs_eq_constructedF (x : Graph × ℕ) :
    IdealCVP.ofList (Runtime.generatorCoeffs x) =
      Ideal.constructedF (degree_pos x) (runtimeG x) (runtimeTau x) := by
  rw [Runtime.generatorCoeffs_eq, dominantCoeffs_eq, parityCoeffs_eq_sumPoly]
  rfl

/-- The executable generator list is the canonical list of the ideal generator. -/
theorem generatorCoeffs_eq_toList (x : Graph × ℕ) :
    Runtime.generatorCoeffs x =
      IdealCVP.toList (Ideal.constructedF (degree_pos x) (runtimeG x) (runtimeTau x)) := by
  have roundtrip {n : ℕ} (a : List ℤ) (ha : a.length = n) :
      IdealCVP.toList (IdealCVP.ofList (d := n) a) = a := by
    subst n
    exact IdealCVP.toList_ofList a
  have hround := roundtrip (Runtime.generatorCoeffs x) (Runtime.length_generatorCoeffs x)
  rw [generatorCoeffs_eq_constructedF] at hround
  exact hround.symm

/-- Integer and natural radius formulas agree; natural subtraction loses no mass. -/
theorem outputRadius_eq (x : Graph × ℕ) :
    Runtime.outputRadius x =
      (Ideal.radius (degree_pos x) (runtimeG x) (runtimeTau x)).toNat := by
  have hr : (Runtime.outputRadius x : ℤ) =
      Ideal.radius (degree_pos x) (runtimeG x) (runtimeTau x) := by
    rw [Runtime.outputRadius_eq, Nat.cast_add, Nat.cast_add,
      dominantAmplitude_eq, wallNorm_eq, Ideal.radius_eq]
    rfl
  rw [← hr, Int.toNat_natCast]

/-- The unrestricted list construction agrees exactly with the mathematical output. -/
theorem construction_eq_outputInput (x : Graph × ℕ) :
    Runtime.construction x = Ideal.outputInput (degree_pos x) (runtimeG x) (runtimeTau x) := by
  unfold Runtime.construction Ideal.outputInput
  rw [generatorCoeffs_eq_toList, outputRadius_eq]

/-- In the main case the total list reduction is exactly the mathematical output. -/
theorem reduceList_eq_outputInput {x : Graph × ℕ} (hx : Runtime.mainCase x = true) :
    Runtime.reduceList x = Ideal.outputInput (degree_pos x) (runtimeG x) (runtimeTau x) := by
  rw [Runtime.reduceList_of_mainCase hx, construction_eq_outputInput]

/-- The literal stored tuple agrees with the coefficient construction in the main case. -/
theorem reduceList_eq_constructed {x : Graph × ℕ} (hx : Runtime.mainCase x = true) :
    Runtime.reduceList x =
      (Runtime.degree x,
        IdealCVP.toList (Ideal.constructedF (degree_pos x) (runtimeG x) (runtimeTau x)),
        (Ideal.radius (degree_pos x) (runtimeG x) (runtimeTau x)).toNat) :=
  reduceList_eq_outputInput hx

/-- The main construction is well formed, including its nonzero generator condition. -/
theorem construction_wellFormed (x : Graph × ℕ) :
    (Runtime.construction x).WellFormed := by
  rw [construction_eq_outputInput]
  exact Ideal.outputInput_wellFormed _ (Runtime.degree_dyadic x) _ _

/-- The total reduction is well formed on every input, including the constant branches. -/
theorem reduceList_wellFormed (x : Graph × ℕ) : (Runtime.reduceList x).WellFormed := by
  unfold Runtime.reduceList
  split
  · exact construction_wellFormed x
  · split
    · exact Runtime.yesInput_mem.1
    · exact Runtime.noInput_wellFormed

/-- Main-case membership is exactly the sparse-spin threshold, without using equation (1). -/
theorem reduceList_mem_iff {x : Graph × ℕ} (hx : Runtime.mainCase x = true) :
    Runtime.reduceList x ∈ IdealSVPLang ↔
      runtimeTau x ≤ Ideal.thetaOf (degree_pos x) (runtimeG x) := by
  rw [reduceList_eq_outputInput hx]
  exact Ideal.outputInput_mem_iff _ (Runtime.degree_dyadic x) _ _ (runtimeTau_nonneg x)

/-- Intermediate composition helper only: `hEq1` is the pending Spin equation (1).
It must be discharged by the separate Spin development before claiming an unconditional
reduction. The other two bridges and all non-main branches are proved in this worktree. -/
theorem reduceList_correct_of_eq1
    (hEq1 : ∀ x : Graph × ℕ, Runtime.mainCase x = true →
      (runtimeTau x ≤ Ideal.thetaOf (degree_pos x) (runtimeG x) ↔
        ∃ P : Finset ℤ, x.2 ≤ P.card ∧
          Source.PositiveDifferences P (differenceSet x) ∧ 0 ∈ P))
    (x : Graph × ℕ) : x ∈ Clique ↔ Runtime.reduceList x ∈ IdealSVPLang := by
  cases hx : Runtime.mainCase x with
  | false => exact Runtime.reduceList_correct_of_not_mainCase x hx
  | true =>
    have hh := (Runtime.mainCase_eq_true x).mp hx
    exact (clique_iff_positions x (by omega)).trans
      ((hEq1 x hx).symm.trans (reduceList_mem_iff hx).symm)

end Power2IdealSVP.Glue
