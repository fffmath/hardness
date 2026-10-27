import Power2ModuleSVPSubsetSum.Membership.PolyTime
import Power2ModuleSVP.Membership.Certificates

/-!
# Polynomial module multiplier certificates

The full-rank expanded integer basis bounds every accepted multiplier by Cramer's rule.
A product of coefficient maximum `T` has squared norm at most `2*d*T²`.

Paper: `paper/power2svp-subsetsum.pdf`, Theorem 1.1 (NP membership).
-/
namespace Power2ModuleSVPSubsetSum.Membership
open IdealCVP Turing.MultiTapeTM
open IdealCVP.ModuleSIVP
open Power2ModuleSVP (pairSup moduleVector)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every accepted multiplier pair satisfies the auxiliary Cramer coefficient bound. -/
theorem module_certificate_bound (x : SVPInput) (uv : List ℤ × List ℤ)
    (huv : moduleVerifier (x, uv) = true) :
    ∀ z ∈ uv.1 ++ uv.2, |z| ≤ cvpCertificateBound (moduleBoundInput x) := by
  obtain ⟨hw, hl, hr, hn, hc⟩ := (moduleVerifier_spec x uv).mp huv
  let : Fact (∃ k : ℕ, x.1.1 = 2 ^ k) := ⟨hw.1⟩
  let : Fact (∃ k : ℕ, (moduleNormInput x).1 = 2 ^ k) := ⟨hw.1⟩
  let M := generalMatrix (listRingPair x.1.1 x.1.2.1) (listRingPair x.1.1 x.1.2.2)
  have hdet : M.det ≠ 0 := (generalMatrix_det_iff _ _).mpr
    ((listIndependent_iff _ _).mp hw.2.2.2.2.2)
  have hnorm : sqNorm (M.mulVec (Cyclic.concat (ofList uv.1) (ofList uv.2)) - 0) ≤
      (2 : ℤ) * x.1.1 * (x.2 : ℤ) ^ 2 := by
    rw [sub_zero, Power2ModuleSVP.Membership.module_matrix_product, Cyclic.sqNorm_concat]
    have hc' : pairSup
        (ofList (d := x.1.1) (Power2ModuleSVP.moduleProduct x.1 uv).1,
          ofList (Power2ModuleSVP.moduleProduct x.1 uv).2) ≤ x.2 := by
      rwa [Power2ModuleSVP.ofList_moduleProduct]
    obtain ⟨h₁, h₂⟩ := max_le_iff.mp hc'
    have h₁' := sqNorm_le_of_coeffSup_le _ x.2 h₁
    have h₂' := sqNorm_le_of_coeffSup_le _ x.2 h₂
    linarith
  have hb (i : Fin (2 * x.1.1)) :
      |Cyclic.concat (ofList uv.1) (ofList uv.2) i| ≤
        cvpCertificateBound (moduleBoundInput x) :=
    (certificate_coeff_le M hdet 0 _ _ hnorm i).trans
      (moduleBoundInput_dominates (moduleNormInput x))
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
    have hi' : i < x.1.1 := by omega
    have hh := hb (Cyclic.blockEquiv x.1.1 (.inl ⟨i, hi'⟩))
    rw [Cyclic.concat_left] at hh
    change |uv.1.getD i 0| ≤ _ at hh
    rwa [List.getD_eq_getElem uv.1 0 hi] at hh
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
    have hi' : i < x.1.1 := by omega
    have hh := hb (Cyclic.blockEquiv x.1.1 (.inr ⟨i, hi'⟩))
    rw [Cyclic.concat_right] at hh
    change |uv.2.getD i 0| ≤ _ at hh
    rwa [List.getD_eq_getElem uv.2 0 hi] at hh

/-- The framed signed-binary multiplier pair has polynomial encoded length. -/
theorem module_certificate_length (x : SVPInput) (uv : List ℤ × List ℤ)
    (huv : moduleVerifier (x, uv) = true) :
    (Power2ModuleSVP.encMultipliers uv).length ≤
      moduleWitnessPolynomial.eval (encCVP (moduleBoundInput x)).length := by
  have hl := ((moduleVerifier_spec x uv).mp huv).2.1
  have hr := ((moduleVerifier_spec x uv).mp huv).2.2.1
  have hb := module_certificate_bound x uv huv
  have h₁ := Power2ModuleSVP.Membership.list_length_bound (moduleBoundInput x) uv.1
    (by dsimp [moduleBoundInput, IdealCVP.moduleBoundInput, moduleNormInput]; omega)
    (fun z hz => hb z (List.mem_append_left _ hz))
  have h₂ := Power2ModuleSVP.Membership.list_length_bound (moduleBoundInput x) uv.2
    (by dsimp [moduleBoundInput, IdealCVP.moduleBoundInput, moduleNormInput]; omega)
    (fun z hz => hb z (List.mem_append_right _ hz))
  simp only [Power2ModuleSVP.encMultipliers, length_encPair, moduleWitnessPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

end Power2ModuleSVPSubsetSum.Membership
