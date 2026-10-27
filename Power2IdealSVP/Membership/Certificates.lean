import Power2IdealSVP.Membership.PolyTime
import Power2ModuleSVP.Membership.Certificates

/-!
# Polynomial ideal multiplier certificates

The nonsingular multiplication matrix and squared bound `d*r²` control every accepted
multiplier through the existing Cramer bound and its binary encoding estimate.

Paper: `paper/power2-ideal-svp.pdf`, Theorem 1 (NP membership).
-/
namespace Power2IdealSVP.Membership
open IdealCVP Turing.MultiTapeTM
open Power2ModuleSVPSubsetSum.Membership

/-- Every accepted multiplier already satisfies the generic Cramer coefficient bound. -/
theorem ideal_certificate_bound (x : IdealInput) (u : List ℤ)
    (hu : idealVerifier (x, u) = true) :
    ∀ z ∈ u, |z| ≤ cvpCertificateBound (idealBoundInput x) := by
  obtain ⟨hw, hl, _, hc⟩ := (idealVerifier_spec x u).mp hu
  have hz : ofList (d := x.1) ([] : List ℤ) = 0 := by ext; simp [ofList]
  have hn : sqNorm ((multiplicationMatrix (ofList (d := x.1) x.2.1)).mulVec
      (ofList u) - ofList ([] : List ℤ)) ≤ (x.1 : ℤ) * (x.2.2 : ℤ) ^ 2 := by
    simpa only [multiplicationMatrix_mulVec, hz, sub_zero] using
      sqNorm_le_of_coeffSup_le _ _ hc
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
  have hi' : i < x.1 := by omega
  have hh := certificate_coeff_le _ (multiplicationMatrix_det_ne_zero hw.1 _ hw.2.2)
    _ _ (ofList u) hn ⟨i, hi'⟩
  change |u.getD i 0| ≤ _ at hh
  rwa [List.getD_eq_getElem u 0 hi] at hh

/-- Framed signed-binary multiplier encodings have polynomial length. -/
theorem ideal_certificate_length (x : IdealInput) (u : List ℤ)
    (hu : idealVerifier (x, u) = true) :
    (encList encIntBin u).length ≤
      witnessPolynomial.eval (encCVP (idealBoundInput x)).length := by
  apply Power2ModuleSVP.Membership.list_length_bound
  · exact ((idealVerifier_spec x u).mp hu).2.1.le
  · exact ideal_certificate_bound x u hu

end Power2IdealSVP.Membership
