import Power2ModuleSVP.MembershipCert

/-! NP membership for both unit coefficient-sup-norm languages.
Certificates are integral multipliers; the verifiers only perform the
imported polynomial-time integer-list arithmetic and Boolean scans. -/
namespace Power2ModuleSVP
open IdealCVP Turing.MultiTapeTM Cslib.Complexity

theorem coset_mem_NP : CosetLang ∈ Cslib.Complexity.NP encCoset := by
  obtain ⟨p, hp⟩ := Membership.cosetBoundInput_polytime.polyBounded_length.exists_polynomial
  have he : CosetLang = {x | ∃ u, cosetVerifier (x, u) = true} := by
    ext x
    exact cosetVerifier_correct x
  rw [he]
  apply mem_NP_of_witness (p := witnessPolynomial.comp p) intBinDecoder.list
    cosetVerifier_polytime (fun _ _ => Iff.rfl)
  intro x u hu
  refine ⟨u, hu, (Membership.coset_certificate_length x u hu).trans ?_⟩
  rw [Polynomial.eval_comp]
  exact witnessPolynomial.eval_mono (hp x)

theorem moduleSVP_mem_NP : ModuleSVPLang ∈ Cslib.Complexity.NP encSVP := by
  obtain ⟨p, hp⟩ := Membership.moduleBoundInput_polytime.polyBounded_length.exists_polynomial
  have he : ModuleSVPLang = {x | ∃ uv, moduleVerifier (x, uv) = true} := by
    ext x
    exact moduleVerifier_correct x
  rw [he]
  apply mem_NP_of_witness (p := moduleWitnessPolynomial.comp p)
    (intBinDecoder.list.pair intBinDecoder.list) moduleVerifier_polytime (fun _ _ => Iff.rfl)
  intro x uv huv
  refine ⟨uv, huv, (Membership.module_certificate_length x uv huv).trans ?_⟩
  rw [Polynomial.eval_comp]
  exact moduleWitnessPolynomial.eval_mono (hp x)

end Power2ModuleSVP
