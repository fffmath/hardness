import Power2ModuleSVPSubsetSum.Problem
import Power2ModuleSVPSubsetSum.Membership.Radius

/-!
# Arbitrary-radius module verifier

Integer multiplier lists certify a nonzero module vector within the binary radius.
The stored columns use the existing negacyclic product and independence recognizer.

Paper: `paper/power2svp-subsetsum.pdf`, Definition 2.1 and Theorem 1.1.
-/
namespace Power2ModuleSVPSubsetSum
open IdealCVP
open Power2ModuleSVP (pairSup moduleVector)
open Power2ModuleSVPSubsetSum.Membership

/-- Check that a stored pair is nonzero and has coefficient maximum at most the radius. -/
def moduleVectorCheck (p : ℕ × (List ℤ × List ℤ)) : Bool :=
  (p.2.1.any (fun t => decide (t ≠ 0)) || p.2.2.any (fun t => decide (t ≠ 0))) &&
    listWithin (p.1, p.2.1) && listWithin (p.1, p.2.2)

/-- Verify wellformedness, exact multiplier lengths, and the nonzero bounded product. -/
def moduleVerifier (p : SVPInput × (List ℤ × List ℤ)) : Bool :=
  Power2ModuleSVP.moduleWellFormedCheck p.1.1 && decide (p.2.1.length = p.1.1.1) &&
    decide (p.2.2.length = p.1.1.1) &&
      moduleVectorCheck (p.1.2, Power2ModuleSVP.moduleProduct p.1.1 p.2)

/-- The bounded scan expresses exactly the coefficient maximum of both arrays. -/
theorem moduleVectorCheck_spec (T d : ℕ) (z : List ℤ × List ℤ)
    (hl : z.1.length = d) (hr : z.2.length = d) :
    moduleVectorCheck (T, z) = true ↔
      (ofList (d := d) z.1, ofList (d := d) z.2) ≠ 0 ∧
        pairSup (ofList (d := d) z.1, ofList (d := d) z.2) ≤ T := by
  have hz (a b : Coeff d) : (a ≠ 0 ∨ b ≠ 0) ↔ (a, b) ≠ 0 := by
    simp only [ne_eq, Prod.mk_eq_zero, not_and_or]
  simp only [moduleVectorCheck, Bool.and_eq_true, Bool.or_eq_true,
    list_any_ne_zero _ _ hl, list_any_ne_zero _ _ hr, listWithin_spec _ hl,
    listWithin_spec _ hr, hz, pairSup, max_le_iff, and_assoc]

/-- The executable verifier recognizes exact-length witnesses for the specified language. -/
theorem moduleVerifier_spec (x : SVPInput) (uv : List ℤ × List ℤ) :
    moduleVerifier (x, uv) = true ↔ SVPInput.WellFormed x ∧
      uv.1.length = x.1.1 ∧ uv.2.length = x.1.1 ∧
      let z := moduleVector (ofList (d := x.1.1) x.1.2.1.1, ofList x.1.2.1.2)
        (ofList x.1.2.2.1, ofList x.1.2.2.2) (ofList uv.1) (ofList uv.2)
      z ≠ 0 ∧ pairSup z ≤ x.2 := by
  simp only [moduleVerifier, Bool.and_eq_true, decide_eq_true_eq,
    Power2ModuleSVP.moduleWellFormedCheck_spec,
    moduleVectorCheck_spec _ _ _ (Power2ModuleSVP.length_moduleProduct x.1 uv).1
      (Power2ModuleSVP.length_moduleProduct x.1 uv).2,
    Power2ModuleSVP.ofList_moduleProduct, SVPInput.WellFormed, and_assoc]

/-- A module input belongs to the language exactly when a multiplier pair is accepted. -/
theorem moduleVerifier_correct (x : SVPInput) :
    x ∈ ModuleSVPLang ↔ ∃ uv, moduleVerifier (x, uv) = true := by
  constructor
  · rintro ⟨hw, u, v, hn, hbound⟩
    refine ⟨(toList u, toList v), (moduleVerifier_spec x _).mpr
      ⟨hw, length_toList u, length_toList v, ?_⟩⟩
    simpa only [ofList_toList] using And.intro hn hbound
  · rintro ⟨uv, h⟩
    obtain ⟨hw, _, _, hn, hb⟩ := (moduleVerifier_spec x uv).mp h
    exact ⟨hw, ofList uv.1, ofList uv.2, hn, hb⟩

end Power2ModuleSVPSubsetSum
