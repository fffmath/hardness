import Power2IdealSVP.Problem
import Power2ModuleSVPSubsetSum.Membership.Radius

/-!
# Principal ideal SVP verifier

An integer multiplier certifies a nonzero ideal element within the binary radius.

Paper: `paper/power2-ideal-svp.pdf`, Theorem 1 (NP membership).
-/
namespace Power2IdealSVP
open IdealCVP
open Power2ModuleSVPSubsetSum.Membership

/-- Check the dyadic degree, generator length, and nonzero generator. -/
def idealWellFormedCheck (x : IdealInput) : Bool :=
  cvpWellFormedCheck (x.1, x.2.1, x.2.1, 0) &&
    x.2.1.any (fun z => decide (z ≠ 0))

/-- The executable shape check recognizes exactly the fixed wellformedness predicate. -/
theorem idealWellFormedCheck_spec (x : IdealInput) :
    idealWellFormedCheck x = true ↔ IdealInput.WellFormed x := by
  simp only [idealWellFormedCheck, Bool.and_eq_true, cvpWellFormedCheck_eq,
    CVPInput.WellFormed]
  constructor
  · rintro ⟨⟨hd, hl, _⟩, hn⟩
    exact ⟨hd, hl, (list_any_ne_zero _ _ hl).mp hn⟩
  · rintro ⟨hd, hl, hn⟩
    exact ⟨⟨hd, hl, hl⟩, (list_any_ne_zero _ _ hl).mpr hn⟩

/-- Recompute the ideal element by negacyclic list multiplication. -/
def idealProduct (x : IdealInput) (u : List ℤ) : List ℤ :=
  negacyclicMul x.1 x.2.1 u

/-- The recomputed product always has exactly the stored degree many coefficients. -/
@[simp] theorem length_idealProduct (x : IdealInput) (u : List ℤ) :
    (idealProduct x u).length = x.1 := length_negacyclicMul _ _ _

/-- The executable product agrees with multiplication in the coefficient model. -/
theorem ofList_idealProduct (x : IdealInput) (u : List ℤ) :
    ofList (d := x.1) (idealProduct x u) =
      Cyclotomic.mul (ofList x.2.1) (ofList u) := ofList_negacyclicMul _ _ _

/-- Verify an exact-length multiplier and a nonzero product within the radius. -/
def idealVerifier (p : IdealInput × List ℤ) : Bool :=
  idealWellFormedCheck p.1 && decide (p.2.length = p.1.1) &&
    (idealProduct p.1 p.2).any (fun z => decide (z ≠ 0)) &&
    listWithin (p.1.2.2, idealProduct p.1 p.2)

/-- Exact semantic specification of the multiplier verifier. -/
theorem idealVerifier_spec (x : IdealInput) (u : List ℤ) :
    idealVerifier (x, u) = true ↔ IdealInput.WellFormed x ∧ u.length = x.1 ∧
      Cyclotomic.mul (ofList (d := x.1) x.2.1) (ofList u) ≠ 0 ∧
      Power2ModuleSVP.coeffSup
        (Cyclotomic.mul (ofList (d := x.1) x.2.1) (ofList u)) ≤ x.2.2 := by
  simp only [idealVerifier, Bool.and_eq_true, idealWellFormedCheck_spec,
    decide_eq_true_eq, list_any_ne_zero _ _ (length_idealProduct x u),
    listWithin_spec _ (length_idealProduct x u), ofList_idealProduct, and_assoc]

/-- Accepted multiplier lists characterize the ideal language. -/
theorem idealVerifier_correct (x : IdealInput) :
    x ∈ IdealSVPLang ↔ ∃ u, idealVerifier (x, u) = true := by
  constructor
  · rintro ⟨hw, u, hn, hb⟩
    refine ⟨toList u, (idealVerifier_spec x _).mpr ⟨hw, length_toList u, ?_⟩⟩
    simpa only [ofList_toList] using And.intro hn hb
  · rintro ⟨u, hu⟩
    obtain ⟨hw, _, hn, hb⟩ := (idealVerifier_spec x u).mp hu
    exact ⟨hw, ofList u, hn, hb⟩

end Power2IdealSVP
