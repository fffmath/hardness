import Power2ModuleSVP.Membership.PolyTime

/-!
# Binary radius checks and squared coefficient norms

Shared executable coefficient scans for arbitrary binary radii, together with the squared
Euclidean bound used by the Cramer certificate estimates for both new languages.

Paper: `paper/power2svp-subsetsum.pdf`, Definition 2.1 and Theorem 1.1;
`Power2IdealSVP/paper/power2-ideal-svp.pdf`, Theorem 1.
-/

namespace Power2ModuleSVPSubsetSum.Membership

open IdealCVP Power2ModuleSVP Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Check each signed coefficient against a natural radius stored in binary. -/
def listWithin (p : ℕ × List ℤ) : Bool :=
  p.2.all fun z => decide (z.natAbs ≤ p.1)

/-- A coefficient maximum bound is equivalent to its coordinate bounds. -/
theorem coeffSup_le_iff {d : ℕ} (a : Power2ModuleSVP.Coeff d) (T : ℕ) :
    coeffSup a ≤ T ↔ ∀ i, (a i).natAbs ≤ T := by
  simp only [coeffSup, Finset.sup_le_iff, Finset.mem_univ, forall_const]

/-- The executable scan recognizes the coefficient maximum bound on exact-length arrays. -/
theorem listWithin_spec {d : ℕ} (l : List ℤ) (hl : l.length = d) (T : ℕ) :
    listWithin (T, l) = true ↔ coeffSup (ofList (d := d) l) ≤ T := by
  simp only [listWithin, List.all_eq_true, decide_eq_true_eq]
  rw [Power2ModuleSVP.list_all_iff l hl, coeffSup_le_iff]

/-- A radius bound on every coefficient bounds the squared norm by `d * T²`. -/
theorem sqNorm_le_of_coeffSup_le {d : ℕ} (a : Power2ModuleSVP.Coeff d) (T : ℕ)
    (h : coeffSup a ≤ T) : sqNorm a ≤ (d : ℤ) * (T : ℤ) ^ 2 := by
  calc
    _ ≤ ∑ _i : Fin d, (T : ℤ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi : |a i| ≤ (T : ℤ) := by
        simpa only [Int.natCast_natAbs] using
          (show ((a i).natAbs : ℤ) ≤ (T : ℤ) from by
            exact_mod_cast (coeffSup_le_iff a T).mp h i)
      have hi' := abs_le.mp hi
      nlinarith
    _ = _ := by simp

/-- The radius scan has a native tidy multitape-TM polynomial-time certificate. -/
@[fun_prop] theorem listWithin_polytime : ComputableTidilyInPolyTime
    listWithin (encPair encNat (encList encIntBin)) encBool := by
  unfold listWithin
  fun_prop

end Power2ModuleSVPSubsetSum.Membership
