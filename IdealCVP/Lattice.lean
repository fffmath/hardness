import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Module.Equiv.Basic

/-! # Integral coefficient lattices and exact decision CVP

The coefficient embedding is integral throughout this reduction. Distances and
thresholds are squared Euclidean distances in ℤ, avoiding square roots in the
statements of the decision and gap theorems.
-/
namespace IdealCVP

/-- Integral coefficient vectors of dimension `d`. -/
abbrev Coeff (d : ℕ) := Fin d → ℤ

/-- The squared Euclidean norm of an integral vector. -/
def sqNorm {ι : Type*} [Fintype ι] (v : ι → ℤ) : ℤ := ∑ i, v i ^ 2

theorem sqNorm_nonneg {ι : Type*} [Fintype ι] (v : ι → ℤ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

@[simp] theorem sqNorm_zero {ι : Type*} [Fintype ι] : sqNorm (0 : ι → ℤ) = 0 := by
  simp [sqNorm]

theorem sqNorm_eq_zero_iff {ι : Type*} [Fintype ι] (v : ι → ℤ) :
    sqNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have hi : v i ^ 2 ≤ sqNorm v :=
      Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
    have := sq_nonneg (v i)
    simp only [Pi.zero_apply]
    nlinarith
  · rintro rfl; simp

/-- A nonzero integral vector has squared norm at least one. -/
theorem sqNorm_pos {ι : Type*} [Fintype ι] {v : ι → ℤ} (h : v ≠ 0) :
    1 ≤ sqNorm v := by
  have := sqNorm_nonneg v
  have := (sqNorm_eq_zero_iff v).not.mpr h
  omega

theorem sqNorm_smul {ι : Type*} [Fintype ι] (k : ℤ) (v : ι → ℤ) :
    sqNorm (k • v) = k ^ 2 * sqNorm v := by
  simp only [sqNorm, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

/-- Exact decision CVP, as in `pre.tex`, specialized to integral inputs. -/
def CVPYes {d : ℕ} (L : AddSubgroup (Coeff d)) (t : Coeff d) (Δ : ℤ) : Prop :=
  ∃ v ∈ L, sqNorm (v - t) ≤ Δ

/-- A witness at the threshold together with the universal lower bound states
that the minimum squared distance is exactly Δ, without choosing a minimizer. -/
def MinimumSquaredDistance {d : ℕ} (L : AddSubgroup (Coeff d))
    (t : Coeff d) (Δ : ℤ) : Prop :=
  (∃ v ∈ L, sqNorm (v - t) = Δ) ∧ ∀ v ∈ L, Δ ≤ sqNorm (v - t)

end IdealCVP
