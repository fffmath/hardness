import Power2ModuleSVP.Membership.Certificates

/-!
# NP membership for cosets and module SVP

Combine executable Boolean verifiers, native runtime bounds, and polynomially bounded integer
witnesses to prove NP membership of both encoded languages.

Paper: `paper/power2svp.pdf`, Section 3.3 (proof of Theorem 1, NP membership).
-/
namespace Power2ModuleSVP
open IdealCVP Turing.MultiTapeTM Cslib.Complexity

/-- The principal-coset language has polynomially bounded verifiable certificates. -/
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

/-- The module-SVP language has polynomially bounded verifiable certificates. -/
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
