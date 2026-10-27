import Power2IdealSVP.Glue.Spin
import Power2IdealSVP.Glue.Theta
import Power2IdealSVP.Spin.Equivalence

/-!
# Unconditional correctness of the CLIQUE reduction

The executable parameters, sparse-spin equivalence, and principal ideal construction combine
to discharge equation (1) for the total coefficient-list reduction.

Paper: `paper/power2-ideal-svp.txt`, Theorem 1 and equations (1)–(3).
-/

namespace Power2IdealSVP.Glue

open Cslib.Complexity Power2ModuleSVP

/-- Equal canonical coefficient lists give equal sparse-spin objectives across degrees. -/
theorem Theta_eq_of_toList_eq {n m : ℕ} {G : Coeff n} {H : Coeff m}
    (h : IdealCVP.toList G = IdealCVP.toList H) : Spin.Theta G = Spin.Theta H := by
  have hnm : n = m := by simpa using congrArg List.length h
  subst m
  have hGH : G = H := by
    simpa using congrArg (IdealCVP.ofList (d := n)) h
  rw [hGH]

/-- Equation (1) for the executable main case, with the source difference-set interface. -/
theorem runtime_eq1 (x : Graph × ℕ) (hx : Runtime.mainCase x = true) :
    runtimeTau x ≤ Ideal.thetaOf (degree_pos x) (runtimeG x) ↔
      ∃ P : Finset ℤ, x.2 ≤ P.card ∧
        Source.PositiveDifferences P (differenceSet x) ∧ 0 ∈ P := by
  rw [thetaOf_eq_Theta, Theta_eq_of_toList_eq (runtimeG_eq_toList x), runtimeTau_eq]
  have hh := (Runtime.mainCase_eq_true x).mp hx
  rw [Spin.theta_threshold_iff_differences (spinDistances_valid x) (by omega)]
  simp only [positiveDifferences_iff]
  constructor
  · rintro ⟨P, h0, hc, hP⟩
    exact ⟨P, hc, hP, h0⟩
  · rintro ⟨P, hc, hP, h0⟩
    exact ⟨P, h0, hc, hP⟩

end Power2IdealSVP.Glue

namespace Power2IdealSVP

/-- The total polynomial-time list reduction preserves CLIQUE on every encoded input. -/
theorem reduceList_correct (x : Cslib.Complexity.Graph × ℕ) :
    x ∈ Cslib.Complexity.Clique ↔ Runtime.reduceList x ∈ IdealSVPLang :=
  Glue.reduceList_correct_of_eq1 Glue.runtime_eq1 x

end Power2IdealSVP
