import Power2IdealSVP.Membership.Certificates

/-!
# NP membership of principal ideal SVP

Combine the native multiplier verifier and polynomial certificate bound using `mem_NP_of_witness`.

Paper: `paper/power2-ideal-svp.pdf`, Theorem 1 (NP membership).
-/
namespace Power2IdealSVP
open IdealCVP Turing.MultiTapeTM Cslib.Complexity

/-- Principal ideal SVP with a binary coefficient radius belongs to NP. -/
theorem idealSVP_mem_NP : IdealSVPLang ∈ Cslib.Complexity.NP encIdeal := by
  obtain ⟨p, hp⟩ := Membership.idealBoundInput_polytime.polyBounded_length.exists_polynomial
  have he : IdealSVPLang = {x | ∃ u, idealVerifier (x, u) = true} := by
    ext x
    exact idealVerifier_correct x
  rw [he]
  apply mem_NP_of_witness (p := witnessPolynomial.comp p) intBinDecoder.list
    idealVerifier_polytime (fun _ _ => Iff.rfl)
  intro x u hu
  refine ⟨u, hu, (Membership.ideal_certificate_length x u hu).trans ?_⟩
  rw [Polynomial.eval_comp]
  exact witnessPolynomial.eval_mono (hp x)

end Power2IdealSVP
