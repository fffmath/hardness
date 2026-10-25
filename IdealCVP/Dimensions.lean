import IdealCVP.Main

/-! # Explicit polynomial dimension bounds

No model of computation is introduced. These are ordinary natural-number
bounds for the finite coefficient constructions.
-/
namespace IdealCVP
namespace SidonPositions
variable {M n : ℕ} (p : SidonPositions n)

/-- The chosen power-of-two half-dimension is at most twice the required row span. -/
theorem N_le (hM : 0 < M) : p.N M ≤ 2 * (M * p.L) := by
  let r := M * p.L
  have hr : 0 < r := Nat.mul_pos hM p.L_pos
  by_cases he : r = 1
  · change 2 ^ Nat.clog 2 r ≤ 2 * r
    simp [he]
  · have hr1 : 1 < r := by omega
    have hlog : 0 < Nat.clog 2 r :=
      (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by simpa using hr1)
    have hpow := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hr1
    simp only [Nat.pred_eq_sub_one] at hpow
    have hstep : 2 ^ Nat.clog 2 r = 2 ^ (Nat.clog 2 r - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    change 2 ^ Nat.clog 2 r ≤ 2 * r
    rw [hstep]
    omega

end SidonPositions
namespace ReductionData
variable {M n : ℕ} (D : ReductionData M n)

/-- The output dimension is bounded by the number of rows and the Sidon span. -/
theorem dimension_le : D.d ≤ 4 * M * (2 * D.positions.c + 1) := by
  have h := D.positions.N_le D.M_pos
  change 2 * D.N ≤ _
  dsimp [SidonPositions.L] at h
  nlinarith

end ReductionData

/-- The paper’s quadratic Sidon construction gives dimension O(M n²). -/
theorem x3c_dimension_le (I : X3CInstance) :
    (x3cToCVP I).d ≤ 4 * (3 * I.q) * (8 * I.n ^ 2 + 1) := by
  have hd := I.reductionData.dimension_le
  have hc := SidonPositions.erdosTuran_size I.n
  have hm := Nat.mul_le_mul_left (4 * (3 * I.q))
    (show 2 * (SidonPositions.erdosTuran I.n).c + 1 ≤ 8 * I.n ^ 2 + 1 by omega)
  exact le_trans hd hm

end IdealCVP
