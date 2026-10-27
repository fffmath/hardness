import Power2ModuleSVPSubsetSum.Reduction.Construction

/-!
# Coefficient-model gadget and storage bridge

The two columns of the gadget, its determinant, and the exact multiplier formula.
The storage lemma uses the existing determinant/field-independence equivalence.

Paper: `paper/power2svp-subsetsum.pdf`, equations (4.3), (4.5), Proposition 4.2.
-/

namespace Power2ModuleSVPSubsetSum.Reduction
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- First column of the rank-two gadget. -/
def leftColumn {n : ℕ} (hn : 0 < n) (H : Coeff n) (M : ℕ) : Coeff n × Coeff n :=
  ((2 : ℤ) • H, (2 * (M : ℤ)) • coeffOne hn)

/-- Second column, with `P = Q + V`. -/
def rightColumn {n : ℕ} (H u P : Coeff n) (M : ℕ) : Coeff n × Coeff n :=
  (-mul H u - P, (-(M : ℤ)) • u)

/-- The coefficient-ring determinant of two columns. -/
def determinant {n : ℕ} (a b : Coeff n × Coeff n) : Coeff n :=
  mul a.1 b.2 - mul a.2 b.1

/-- The centered multiplier exposes the same ring expression in both coordinates. -/
theorem model_vector {n : ℕ} (hn : 0 < n) (H u P a b : Coeff n) (M : ℕ) :
    moduleVector (leftColumn hn H M) (rightColumn H u P M) a b =
      (mul H ((2 : ℤ) • a - mul u b) - mul P b,
        (M : ℤ) • ((2 : ℤ) • a - mul u b)) := by
  simp only [moduleVector, leftColumn, rightColumn, mul_smul_left,
    coeff_mul_neg_left, mul_coeffOne, coeff_mul_assoc hn,
    sub_eq_add_neg, mul_add, mul_add_left, mul_smul_right, mul_neg]
  apply Prod.ext <;> ext i <;>
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] <;> ring

/-- The determinant simplifies to the scalar multiple `2M(Q+V)`. -/
theorem model_determinant {n : ℕ} (hn : 0 < n) (H u P : Coeff n) (M : ℕ) :
    determinant (leftColumn hn H M) (rightColumn H u P M) =
      (2 * (M : ℤ)) • P := by
  simp only [determinant, leftColumn, rightColumn, mul_smul_left,
    mul_coeffOne, mul_smul_right]
  ext i
  simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A positive main scale and a nonzero `Q+V` suffice for a nonzero determinant. -/
theorem model_determinant_ne_zero {n : ℕ} (hn : 0 < n) (H u P : Coeff n)
    (M : ℕ) (hM : 0 < M) (hP : P ≠ 0) :
    determinant (leftColumn hn H M) (rightColumn H u P M) ≠ 0 := by
  rw [model_determinant]
  intro h
  apply hP
  ext i
  have hi := congrFun h i
  change (2 * (M : ℤ)) * P i = 0 at hi
  have hM' : (2 * (M : ℤ)) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hi).resolve_left hM'

/-- Store arbitrary coefficient-model columns using exact-length arrays. -/
def store {n : ℕ} (a b : Coeff n × Coeff n) (r : ℕ) : SVPInput :=
  ((n, (IdealCVP.toList a.1, IdealCVP.toList a.2),
    (IdealCVP.toList b.1, IdealCVP.toList b.2)), r)

/-- Exact array storage preserves the full decision predicate. -/
theorem store_mem_iff {n : ℕ} (hn : Dyadic n) (a b : Coeff n × Coeff n) (r : ℕ) :
    store a b r ∈ ModuleSVPLang ↔ determinant a b ≠ 0 ∧ ModuleYes a b r := by
  let : Fact (∃ k, n = 2 ^ k) := ⟨hn⟩
  have hp := hn.pos
  have hdet : IdealCVP.listIndependent n
      (IdealCVP.toList a.1, IdealCVP.toList a.2)
      (IdealCVP.toList b.1, IdealCVP.toList b.2) = true ↔ determinant a b ≠ 0 := by
    rw [IdealCVP.listIndependent_iff, IdealCVP.ModuleSIVP.independent_iff]
    simp only [IdealCVP.listRingPair, IdealCVP.ofList_toList]
    have he : toQuot (determinant a b) =
        toQuot a.1 * toQuot b.2 - toQuot a.2 * toQuot b.1 := by
      rw [determinant, ← quotEquiv_apply hp, map_sub]
      simp only [quotEquiv_apply, toQuot_mul hp]
    rw [← he, ← quotEquiv_apply hp]
    exact not_congr (map_eq_zero_iff (quotEquiv hp) (quotEquiv hp).injective)
  simp only [ModuleSVPLang, Set.mem_ofPred_eq, SVPInput.WellFormed,
    Power2ModuleSVP.SVPInput.WellFormed, store, IdealCVP.length_toList,
    IdealCVP.ofList_toList, hn, true_and]
  exact and_congr_left (fun _ => hdet)

end Power2ModuleSVPSubsetSum.Reduction
