import Power2ModuleSVPSubsetSum.Membership.Certificates

/-!
# NP membership of arbitrary-radius module SVP

The native TM verifier and polynomially bounded signed-binary multipliers supply
`mem_NP_of_witness` for the fixed decision language.

Paper: `paper/power2svp-subsetsum.pdf`, Theorem 1.1 (NP membership).
-/
namespace Power2ModuleSVPSubsetSum
open IdealCVP Turing.MultiTapeTM Cslib.Complexity

/-- Exact coefficient-maximum rank-two module SVP belongs to NP. -/
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

end Power2ModuleSVPSubsetSum
