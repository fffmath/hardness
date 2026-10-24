import IdealCVP.Lattice

/-! # Scalar separation estimate

The final square-root estimates in Case 2 of Lemma `lem:admissible`.
-/
namespace IdealCVP

/-- The paper's choice of P amplifies the integral rounding gap past Δ+4.
The hypotheses on c and e say that they bound the two real ceilings in P. -/
theorem penalty_separation (ω ν s W c e P R : ℝ)
    (hω : 0 ≤ ω) (hν : 0 ≤ ν) (hs : 0 ≤ s) (hW : 0 ≤ W)
    (hsq : ω + 4 ≤ s ^ 2)
    (hc : 0 ≤ c) (he : Real.sqrt (ν + 4) ≤ e)
    (hP : P = 1 + s * (s * W + c + e))
    (hR : (P - W) * Real.sqrt (ω + 4) - W * Real.sqrt ω - c ≤ R) :
    P ^ 2 * ω + ν + 4 < R ^ 2 := by
  let A := Real.sqrt (ω + 4)
  let B := Real.sqrt ω
  let E := Real.sqrt (ν + 4)
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hE0 : 0 ≤ E := Real.sqrt_nonneg _
  have hA : A ^ 2 = ω + 4 := Real.sq_sqrt (by linarith)
  have hB : B ^ 2 = ω := Real.sq_sqrt hω
  have hE : E ^ 2 = ν + 4 := Real.sq_sqrt (by linarith)
  have hAs : A ≤ s := (Real.sqrt_le_iff).mpr ⟨hs, hsq⟩
  have hBs : B ≤ s := (Real.sqrt_le_iff).mpr ⟨hs, by linarith⟩
  have hgap : 0 < A - B := by nlinarith
  have hsum : A + B ≤ 2 * s := by linarith
  have hdiff : 2 ≤ s * (A - B) := by
    have := mul_nonneg hgap.le (show 0 ≤ 2 * s - (A + B) by linarith)
    nlinarith
  have he0 : 0 ≤ e := le_trans hE0 he
  have hC : 0 ≤ s * W + c + e := by positivity
  have hbig : 2 * s * W + c + E < P * (A - B) := by
    calc
      2 * s * W + c + E < (A - B) + 2 * (s * W + c + e) := by
        dsimp [E] at *
        nlinarith
      _ ≤ (A - B) + (s * (A - B)) * (s * W + c + e) :=
        by have := mul_le_mul_of_nonneg_right hdiff hC; linarith
      _ = P * (A - B) := by rw [hP]; ring
  have hPl : 0 ≤ P := by rw [hP]; positivity
  have hR' : P * B + E < R := by
    change (P - W) * A - W * B - c ≤ R at hR
    have hw := mul_le_mul_of_nonneg_left hsum hW
    nlinarith
  have hbase : 0 ≤ P * B + E := by positivity
  have hcross : 0 ≤ 2 * P * B * E := by positivity
  have hR0 : 0 < R := lt_of_le_of_lt hbase hR'
  nlinarith [sq_nonneg (R - (P * B + E))]

end IdealCVP
