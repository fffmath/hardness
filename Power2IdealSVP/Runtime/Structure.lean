import Power2IdealSVP.Runtime.Construction

/-!
# Structural guarantees for the executable reduction

The total output has a dyadic degree and an exact-length coefficient array. The main gadget
uses the least sufficiently large power of two and has positive radius. The constant branches
have the advertised decision values.

Paper: `paper/power2-ideal-svp.pdf`, Sections 1.1 and 1.5.
-/

namespace Power2IdealSVP.Runtime

open Cslib.Complexity Power2ModuleSVP

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] guardCoeff guardCoeffs interactionCoeff interactionCoeffs listNorm
  interactionNorm neighborAmplitude spinThreshold guardAmplitude spinCoeffs wallCoeffs wallNorm
  clockAmplitude clockCoeffs clockNorm dominantAmplitude parityCoeffs dominantCoeffs generatorCoeffs
  outputRadius construction reduceList


/-- The gadget dimension is dyadic on every input. -/
theorem degree_dyadic (x : Graph × ℕ) : Dyadic (degree x) :=
  ⟨Nat.clog 2 (8 * windowBound x + 17), rfl⟩

/-- The dimension strictly exceeds the geometric separation bound. -/
theorem degree_gt (x : Graph × ℕ) : 8 * windowBound x + 16 < degree x := by
  have := Nat.le_pow_clog (by decide : 1 < 2) (8 * windowBound x + 17)
  unfold degree
  omega

/-- Every other power of two above the separation bound is at least the chosen degree. -/
theorem degree_le_pow {x : Graph × ℕ} {k : ℕ}
    (hk : 8 * windowBound x + 16 < 2 ^ k) : degree x ≤ 2 ^ k := by
  unfold degree
  exact Nat.pow_le_pow_right (by decide)
    ((Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr (by omega))

/-- Rounding up to a power of two increases the bound by at most a factor two. -/
theorem degree_le (x : Graph × ℕ) : degree x ≤ 16 * windowBound x + 34 := by
  have hpos : 0 < Nat.clog 2 (8 * windowBound x + 17) :=
    Nat.clog_pos (by decide) (by omega)
  have h := Nat.pow_pred_clog_lt_self (by decide : 1 < 2)
    (show 1 < 8 * windowBound x + 17 by omega)
  have hp : Nat.clog 2 (8 * windowBound x + 17) =
      (Nat.clog 2 (8 * windowBound x + 17)).pred + 1 := by
    exact (Nat.succ_pred_eq_of_pos hpos).symm
  unfold degree
  rw [hp, pow_succ]
  omega

/-- The label magnitude is bounded by a fixed degree-nine polynomial in the vertex count. -/
theorem maxLabel_le (x : Graph × ℕ) : maxLabel x ≤ 21 * vertexCount x.1 ^ 9 := by
  let v := vertexCount x.1
  change v + (3 * v ^ 3 + 1) * v ^ 2 + (3 * v ^ 3 + 1) ^ 2 * v ^ 3 ≤ 21 * v ^ 9
  by_cases hv : v = 0
  · simp [hv]
  · have hv1 : 1 ≤ v := by omega
    have hv3 : 1 ≤ v ^ 3 := Nat.one_le_pow _ _ hv1
    have hb : 3 * v ^ 3 + 1 ≤ 4 * v ^ 3 := by omega
    have hv9 : v ≤ v ^ 9 := by
      simpa using Nat.pow_le_pow_right hv1 (show 1 ≤ 9 by decide)
    have hv59 : v ^ 5 ≤ v ^ 9 := Nat.pow_le_pow_right hv1 (by decide)
    calc
      _ ≤ v + (4 * v ^ 3) * v ^ 2 + (4 * v ^ 3) ^ 2 * v ^ 3 := by gcongr
      _ = v + 4 * v ^ 5 + 16 * v ^ 9 := by ring
      _ ≤ 21 * v ^ 9 := by omega

/-- Explicit polynomial bound for the unary dimension, valid even on degenerate inputs. -/
theorem degree_le_vertexCount (x : Graph × ℕ) :
    degree x ≤ 5376 * vertexCount x.1 ^ 9 + 66 := by
  have hn := degree_le x
  have ha := maxLabel_le x
  unfold windowBound windowSpacing at hn
  omega

/-- The apparent subtraction in the radius is exact and leaves a positive integer. -/
theorem outputRadius_eq (x : Graph × ℕ) :
    outputRadius x = dominantAmplitude x + wallNorm x + 1 := by
  unfold outputRadius clockAmplitude
  omega

/-- The main gadget radius is positive for every input. -/
theorem outputRadius_pos (x : Graph × ℕ) : 0 < outputRadius x := by
  rw [outputRadius_eq]
  omega

/-- The generator array has exactly the declared dimension. -/
@[simp] theorem length_generatorCoeffs (x : Graph × ℕ) :
    (generatorCoeffs x).length = degree x := by
  simp [generatorCoeffs]

/-- The total reduction always returns an exact-length array. -/
theorem reduceList_length (x : Graph × ℕ) :
    (reduceList x).2.1.length = (reduceList x).1 := by
  unfold reduceList construction yesInput noInput
  split
  · exact length_generatorCoeffs x
  · split <;> rfl

/-- The total reduction always returns a dyadic degree, including the constant branches. -/
theorem reduceList_dyadic (x : Graph × ℕ) : Dyadic (reduceList x).1 := by
  unfold reduceList construction yesInput noInput
  split
  · exact degree_dyadic x
  · split <;> exact ⟨0, rfl⟩

/-- Radius zero excludes every nonzero ring vector, in every dimension. -/
theorem not_idealYes_zero {d : ℕ} (f : Coeff d) : ¬IdealYes f 0 := by
  rintro ⟨u, hne, hsup⟩
  apply hne
  funext i
  have hi := (Finset.sup_le_iff.mp hsup) i (Finset.mem_univ i)
  exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hi)

/-- The constant YES branch is a well-formed accepted input. -/
theorem yesInput_mem : yesInput ∈ IdealSVPLang := by
  unfold yesInput IdealSVPLang IdealInput.WellFormed
  change (Dyadic 1 ∧ ([1] : List ℤ).length = 1 ∧
    IdealCVP.ofList (d := 1) [1] ≠ 0) ∧ IdealYes (IdealCVP.ofList (d := 1) [1]) 1
  have hgen : IdealCVP.ofList (d := 1) ([1] : List ℤ) ≠ 0 := by
    intro h
    have := congrFun h 0
    norm_num [IdealCVP.ofList] at this
  refine ⟨⟨⟨0, rfl⟩, rfl, hgen⟩, ?_⟩
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    norm_num [IdealCVP.Cyclotomic.mul, IdealCVP.ofList, Fin.sum_univ_one] at this
  · norm_num [coeffSup, IdealCVP.Cyclotomic.mul, IdealCVP.ofList, Fin.sum_univ_one]

/-- The constant NO branch still has a valid dyadic shape and a nonzero generator. -/
theorem noInput_wellFormed : noInput.WellFormed := by
  change yesInput.WellFormed
  exact yesInput_mem.1

/-- The constant NO branch is rejected because its radius is zero. -/
theorem noInput_not_mem : noInput ∉ IdealSVPLang := by
  intro h
  unfold noInput at h
  exact not_idealYes_zero _ h.2

/-- Every degenerate source case is mapped to a target instance with the same answer. -/
theorem reduceList_correct_of_not_mainCase (x : Graph × ℕ) (hx : mainCase x = false) :
    x ∈ Clique ↔ reduceList x ∈ IdealSVPLang := by
  rw [← smallAnswer_correct_of_not_mainCase hx]
  cases ha : smallAnswer x <;>
    simp [reduceList, hx, ha, yesInput_mem, noInput_not_mem]

end Power2IdealSVP.Runtime
