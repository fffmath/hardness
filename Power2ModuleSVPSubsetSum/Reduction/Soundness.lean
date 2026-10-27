import Power2ModuleSVPSubsetSum.Reduction.Validity
import Power2ModuleSVPSubsetSum.Reduction.Boolean
import Power2ModuleSVPSubsetSum.Reduction.UnitAction
import Power2ModuleSVPSubsetSum.Rigidity.Multiplier

/-!
# Soundness and normalization of short vectors

A short nonzero vector has a signed monomial second multiplier. After its inverse signed
shift, the first multiplier is a unique Boolean word.

Paper: `paper/power2svp-subsetsum.pdf`, Proposition 4.2.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Power2ModuleSVPSubsetSum.Reduction
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- The bottom coordinate of a short gadget vector bounds its centered multiplier by one. -/
theorem short_centered_cube (w : List ℕ) (B : ℕ)
    (a b : Coeff (2 * halfDegree w.length))
    (hshort : pairSup (moduleVector (gadgetA w B) (gadgetB w B) a b) ≤
      (gadget w B).M) :
    coeffSup ((2 : ℤ) • a - mul (gadgetU w B) b) ≤ 1 := by
  rw [gadgetA, gadgetB, model_vector] at hshort
  have h := (le_max_right _ _).trans hshort
  change coeffSup (((gadget w B).M : ℤ) • ((2 : ℤ) • a - mul (gadgetU w B) b)) ≤ _ at h
  rw [coeffSup_smul] at h
  simp only [Int.natAbs_natCast] at h
  have hp := gadget_M_pos w B
  nlinarith

/-- Every nonzero short vector has a signed monomial second multiplier. -/
theorem short_second_monomial (w : List ℕ) (B : ℕ)
    (a b : Coeff (2 * halfDegree w.length))
    (hne : moduleVector (gadgetA w B) (gadgetB w B) a b ≠ 0)
    (hshort : pairSup (moduleVector (gadgetA w B) (gadgetB w B) a b) ≤
      (gadget w B).M) : SignedMonomial b := by
  have hz := short_centered_cube w B a b hshort
  have htop : coeffSup (mul (gadgetH w B) ((2 : ℤ) • a - mul (gadgetU w B) b) -
      mul (Rigidity.Q (gadgetH w B) (gadgetV w B) + gadgetV w B) b) ≤
      Rigidity.M (gadgetH w B) (gadgetV w B) := by
    rw [gadgetA, gadgetB, model_vector] at hshort
    exact (le_max_left _ _).trans (hshort.trans_eq (gadget_M w B))
  have hr := Rigidity.multiplier_rigidity
    (by have := two_le_halfDegree w.length; omega : 0 < halfDegree w.length)
    (gadgetH w B) (gadgetV w B) b _ hz htop
  rcases hr with hb | hb
  · subst b
    simp only [mul_zero, sub_zero, coeffSup_smul] at hz
    have ha : a = 0 := (coeffSup_eq_zero_iff a).mp (by norm_num at hz; omega)
    subst a
    exact False.elim (hne (by simp [moduleVector]))
  · exact hb

/-- A normalized short multiplier is the coefficient vector of a unique Boolean word. -/
theorem normalized_short_boolean (w : List ℕ) (B : ℕ)
    (a : Coeff (2 * halfDegree w.length))
    (hshort : pairSup (moduleVector (gadgetA w B) (gadgetB w B) a
      (coeffOne (degree_dyadic w.length).pos)) ≤ (gadget w B).M) :
    ∃! ξ : Fin w.length → Bool,
      a = booleanWord (show w.length ≤ degree w.length from
        (length_le_halfDegree w.length).trans (by unfold degree; omega)) ξ := by
  apply (boolean_encoding _ a).mp
  have h := short_centered_cube w B a (coeffOne (degree_dyadic w.length).pos) hshort
  simpa only [mul_coeffOne_right, gadgetU, gadget] using h

/-- Every short nonzero vector normalizes to a Boolean multiplier at exactly the same norm. -/
theorem short_normalizes_to_boolean (w : List ℕ) (B : ℕ)
    (a b : Coeff (2 * halfDegree w.length))
    (hne : moduleVector (gadgetA w B) (gadgetB w B) a b ≠ 0)
    (hshort : pairSup (moduleVector (gadgetA w B) (gadgetB w B) a b) ≤
      (gadget w B).M) :
    ∃ ξ : Fin w.length → Bool,
      pairSup (moduleVector (gadgetA w B) (gadgetB w B)
        (booleanWord (show w.length ≤ degree w.length from
          (length_le_halfDegree w.length).trans (by unfold degree; omega)) ξ)
        (coeffOne (degree_dyadic w.length).pos)) =
      pairSup (moduleVector (gadgetA w B) (gadgetB w B) a b) := by
  have hb := short_second_monomial w B a b hne hshort
  obtain ⟨a', _, hn⟩ := normalize_short_vector (degree_dyadic w.length).pos
    (gadgetA w B) (gadgetB w B) a b hb hne
  obtain ⟨ξ, hξ, _⟩ := normalized_short_boolean w B a' (hn.le.trans hshort)
  exact ⟨ξ, hξ ▸ hn⟩

end Power2ModuleSVPSubsetSum.Reduction
