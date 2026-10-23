import Hardness.Certificates

/-! # Explicit coefficient bounds for the executable reduction

All bounds are ordinary polynomial expressions in the input parameters. They
bound numerical magnitudes, and make no claim about a machine runtime model.
-/
namespace Hardness
open Hardness.Cyclotomic

namespace Cyclotomic

/-- At an arbitrary coordinate an injectively supported sparse vector is zero
or one of its supplied coefficients. -/
theorem sparse_coeff_cases {ι : Type*} [Fintype ι] {d : ℕ} {e : ι → Fin d}
    (he : Function.Injective e) (v : ι → ℤ) (r : Fin d) :
    sparse e v r = 0 ∨ ∃ j, sparse e v r = v j := by
  classical
  by_cases hr : ∃ j, e j = r
  · obtain ⟨j, rfl⟩ := hr
    exact Or.inr ⟨j, sparse_at he v j⟩
  · left
    have hh : ∀ j, r ≠ e j := by simpa [eq_comm] using hr
    simp only [sparse_apply, hh, ite_false, Finset.sum_const_zero]

theorem interleave_coeff_bound {N : ℕ} (a b : R N) (B : ℤ)
    (ha : ∀ i, |a i| ≤ B) (hb : ∀ i, |b i| ≤ B) (i : Fin (2*N)) :
    |interleave a b i| ≤ B := by
  unfold interleave
  split_ifs
  · exact ha _
  · exact hb _

end Cyclotomic

/-- An explicit polynomial upper bound for the scalar penalty. -/
def penaltyBound (M n : ℕ) : ℕ :=
  1 + (n+4) * ((n+4)*(M*n) + (4*M + M*n^2 + 1) + (M*n^2 + 5))

namespace ReductionData
variable {M n : ℕ} (D : ReductionData M n)

theorem cross_size_le : D.ν ≤ M * n^2 := by
  calc
    (n-1)*D.W ≤ n*(M*n) := Nat.mul_le_mul (Nat.sub_le n 1) D.W_le
    _ = _ := by ring

theorem t_sqNorm_le : sqNorm D.t ≤ (4*M + M*n^2 : ℕ) := by
  have hc : (Finset.univ.filter fun i => D.system.b i = true).card ≤ M := by
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin M)) (fun i => D.system.b i = true)
  have hn : (D.ν : ℤ) ≤ (M*n^2 : ℕ) := by exact_mod_cast D.cross_size_le
  push_cast at hn
  rw [D.t_norm]
  push_cast
  omega

theorem penalty_le : D.P ≤ penaltyBound M n := by
  have hs : D.s ≤ n+4 := by
    rw [s, ceilSqrt_le_iff]
    nlinarith
  have hsqrt (r : ℕ) : ceilSqrt r ≤ r+1 := by
    rw [ceilSqrt_le_iff]
    nlinarith
  have ht : ceilSqrt (sqNorm D.t).toNat ≤ 4*M + M*n^2 + 1 := by
    have hh : (sqNorm D.t).toNat ≤ 4*M + M*n^2 := Int.toNat_le.mpr D.t_sqNorm_le
    exact (hsqrt _).trans (by omega)
  have hν : ceilSqrt (D.ν+4) ≤ M*n^2+5 := (hsqrt _).trans (by have := D.cross_size_le; omega)
  unfold P penaltyBound
  gcongr
  exact D.W_le

/-- Target coefficients in the half-size ring have magnitude at most two. -/
theorem t_coeff_bound (i : Fin D.N) : |D.t i| ≤ 2 := by
  rcases sparse_coeff_cases D.coordinate_injective
      (Sum.elim (fun i => 2 * bit (D.system.b i)) (fun _ => 1)) i with h | ⟨j, h⟩
  · change |sparse _ _ i| ≤ 2
    rw [h]
    norm_num
  · change |sparse _ _ i| ≤ 2
    rw [h]
    cases j with
    | inl j =>
      simp only [Sum.elim_inl]
      cases hbit : D.system.b j <;> norm_num [bit, hbit]
    | inr j => norm_num

theorem h_coeff_bound (i : Fin D.N) : |D.h i| ≤ 1 := by
  rcases sparse_coeff_cases D.hPosition_injective (fun _ => (1 : ℤ)) i with h | ⟨j, h⟩
  · change |sparse _ _ i| ≤ 1
    rw [h]
    norm_num
  · change |sparse _ _ i| ≤ 1
    rw [h]
    norm_num

/-- Generator magnitudes are bounded by twice the explicit penalty bound. -/
theorem generator_coeff_bound (i : Fin D.d) : |D.g i| ≤ 2 * (penaltyBound M n : ℤ) := by
  have hp : (1 : ℤ) ≤ D.P := by have := D.P_pos; omega
  have hb : (D.P : ℤ) ≤ penaltyBound M n := by exact_mod_cast D.penalty_le
  apply interleave_coeff_bound
  · intro j
    change |(2 : ℤ) * D.h j| ≤ _
    rw [abs_mul]
    have := D.h_coeff_bound j
    norm_num
    omega
  · intro j
    simp only [monomial]
    split_ifs
    · rw [abs_of_nonneg (by omega)]
      omega
    · rw [abs_zero]
      omega

/-- Target magnitudes obey the same numerical bound. -/
theorem target_coeff_bound (i : Fin D.d) : |D.T i| ≤ 2 * (penaltyBound M n : ℤ) := by
  have hp : (1 : ℤ) ≤ D.P := by have := D.P_pos; omega
  have hb : (D.P : ℤ) ≤ penaltyBound M n := by exact_mod_cast D.penalty_le
  apply interleave_coeff_bound
  · intro j
    exact (D.t_coeff_bound j).trans (by omega)
  · intro j
    change |(D.P : ℤ) * D.a D.system.μ j| ≤ _
    rw [abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ D.P),
      abs_of_nonneg (D.a_coeff_bounds _ j).1]
    have hh := mul_le_mul_of_nonneg_left (D.a_coeff_bounds D.system.μ j).2 (by omega : (0 : ℤ) ≤ D.P)
    simp only [mul_one] at hh
    omega

theorem threshold_le : D.Δ ≤ ((penaltyBound M n)^2 * n + M*n^2 : ℕ) := by
  have hP : (D.P : ℤ) ≤ penaltyBound M n := by exact_mod_cast D.penalty_le
  have hw : (D.weight : ℤ) ≤ n := by exact_mod_cast D.weight_le
  have hν : (D.ν : ℤ) ≤ (M*n^2 : ℕ) := by exact_mod_cast D.cross_size_le
  have hsq : (D.P : ℤ)^2 ≤ (penaltyBound M n : ℤ)^2 := by
    have h0 : (0 : ℤ) ≤ D.P := by positivity
    nlinarith
  unfold Δ
  push_cast
  exact add_le_add (mul_le_mul hsq hw (by positivity) (by positivity)) hν

end ReductionData

/-- Raw executable output data; the reduction already uses finite integer functions. -/
structure CompiledCVPData where
  d : ℕ
  generator : Coeff d
  target : Coeff d
  threshold : ℤ

def compileX3C (I : X3CInstance) : CompiledCVPData where
  d := (x3cToCVP I).d
  generator := (x3cToCVP I).g
  target := (x3cToCVP I).T
  threshold := (x3cToCVP I).Δ

/-- The data-only constructor has exactly the already-proved answer. -/
theorem compileX3C_correct (I : X3CInstance) :
    I.HasExactCover ↔ CVPYes (principalIdealLattice (compileX3C I).generator)
      (compileX3C I).target (compileX3C I).threshold := x3c_correct I

/-- Explicit output dimension and coefficient-magnitude bounds, in `q,n`. -/
theorem compileX3C_size (I : X3CInstance) :
    (compileX3C I).d ≤ 4*(3*I.q)*(8*I.n^2+1) ∧
    (∀ i, |(compileX3C I).generator i| ≤ 2*(penaltyBound (3*I.q) I.n : ℤ)) ∧
    (∀ i, |(compileX3C I).target i| ≤ 2*(penaltyBound (3*I.q) I.n : ℤ)) ∧
    (compileX3C I).threshold ≤ ((penaltyBound (3*I.q) I.n)^2 * I.n + (3*I.q)*I.n^2 : ℕ) :=
  ⟨x3c_dimension_le I, I.reductionData.generator_coeff_bound,
    I.reductionData.target_coeff_bound, I.reductionData.threshold_le⟩

end Hardness
