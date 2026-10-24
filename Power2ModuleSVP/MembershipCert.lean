import Power2ModuleSVP.MembershipPoly

/-! Polynomial witness lengths for the unit cube languages.
Both promised bases are nonsingular, so the imported Cramer bound controls
the original multipliers. No linear-system algorithm is needed in the verifier. -/
namespace Power2ModuleSVP.Membership
open IdealCVP Turing.MultiTapeTM
open IdealCVP.ModuleSIVP
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem ofList_map_neg {d : ℕ} (l : List ℤ) :
    ofList (d := d) (l.map (fun z => -z)) = -ofList l := by
  ext i
  change (l.map (fun z => -z)).getD i.val 0 = -l.getD i.val 0
  simpa only [neg_zero] using (List.getD_map (l := l) (d := (0 : ℤ))
    (n := i.val) (fun z => -z))

/-- Every accepted coset multiplier already satisfies the imported bound. -/
theorem coset_certificate_bound (x : CosetInput) (u : List ℤ)
    (hu : cosetVerifier (x, u) = true) :
    ∀ z ∈ u, |z| ≤ cvpCertificateBound (cosetBoundInput x) := by
  obtain ⟨hw, hl, hc⟩ := (cosetVerifier_spec x u).mp hu
  have hn : sqNorm ((multiplicationMatrix (ofList (d := x.1) x.2.1)).mulVec
      (ofList u) - ofList (x.2.2.map (fun z => -z))) ≤ (x.1 : ℤ) := by
    rw [multiplicationMatrix_mulVec, ofList_map_neg, sub_neg_eq_add, add_comm]
    exact hc.sqNorm_le
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
  have hi' : i < x.1 := by omega
  have hh := certificate_coeff_le _ (multiplicationMatrix_det_ne_zero hw.1 _ hw.2.2.2.1)
    _ _ (ofList u) hn ⟨i, hi'⟩
  change |u.getD i 0| ≤ _ at hh
  rwa [List.getD_eq_getElem u 0 hi] at hh

/-- A general framing bound, reused for each multiplier list. -/
theorem list_length_bound (b : CVPInput) (l : List ℤ) (hl : l.length ≤ b.1)
    (hb : ∀ z ∈ l, |z| ≤ cvpCertificateBound b) :
    (encList encIntBin l).length ≤ witnessPolynomial.eval (encCVP b).length := by
  have he := intList_encoding_length_le l _ (cvpCertificateBound_nonneg b) hb
  have hbits := cvpCertificateBound_bits b
  have hd := hl.trans (cvp_input_length_bounds b).1
  simp only [witnessPolynomial, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one]
  exact he.trans (Nat.mul_le_mul hd (by unfold certificateBitBound at hbits; omega))

theorem coset_certificate_length (x : CosetInput) (u : List ℤ)
    (hu : cosetVerifier (x, u) = true) :
    (encList encIntBin u).length ≤ witnessPolynomial.eval (encCVP (cosetBoundInput x)).length := by
  apply list_length_bound _ _
  · exact ((cosetVerifier_spec x u).mp hu).2.1.le
  · exact coset_certificate_bound x u hu

/-- The expanded integer basis sends concatenated multipliers to the
concatenated coordinates of the module vector. -/
theorem module_matrix_product (x : SVPInput) [Fact (∃ k : ℕ, x.1 = 2 ^ k)]
    (uv : List ℤ × List ℤ) :
    (generalMatrix (listRingPair x.1 x.2.1) (listRingPair x.1 x.2.2)).mulVec
      (Cyclic.concat (ofList uv.1) (ofList uv.2)) =
      Cyclic.concat (ofList (moduleProduct x uv).1) (ofList (moduleProduct x uv).2) := by
  simpa only [listRingPair, moduleProduct, ofList_listAdd, ofList_negacyclicMul] using
    generalMatrix_mulVec_concat (ofList (d := x.1) x.2.1.1) (ofList x.2.1.2)
      (ofList x.2.2.1) (ofList x.2.2.2) (ofList uv.1) (ofList uv.2)

/-- Every accepted pair of module multipliers satisfies the same auxiliary bound. -/
theorem module_certificate_bound (x : SVPInput) (uv : List ℤ × List ℤ)
    (huv : moduleVerifier (x, uv) = true) :
    ∀ z ∈ uv.1 ++ uv.2, |z| ≤ cvpCertificateBound (moduleBoundInput x) := by
  obtain ⟨hw, hl, hr, hn, hc, he⟩ := (moduleVerifier_spec x uv).mp huv
  letI : Fact (∃ k : ℕ, x.1 = 2 ^ k) := ⟨hw.1⟩
  letI : Fact (∃ k : ℕ, (moduleNormInput x).1 = 2 ^ k) := ⟨hw.1⟩
  let M := generalMatrix (listRingPair x.1 x.2.1) (listRingPair x.1 x.2.2)
  have hdet : M.det ≠ 0 := (generalMatrix_det_iff _ _).mpr
    ((listIndependent_iff _ _).mp hw.2.2.2.2.2)
  have hnorm : sqNorm (M.mulVec (Cyclic.concat (ofList uv.1) (ofList uv.2)) - 0) ≤
      (2 : ℤ) * x.1 := by
    rw [sub_zero, module_matrix_product, Cyclic.sqNorm_concat]
    have hc' : Cube (ofList (d := x.1) (moduleProduct x uv).1) := by
      simpa only [moduleProduct, moduleVector, ofList_listAdd, ofList_negacyclicMul] using hc
    have he' : Cube (ofList (d := x.1) (moduleProduct x uv).2) := by
      simpa only [moduleProduct, moduleVector, ofList_listAdd, ofList_negacyclicMul] using he
    linarith [hc'.sqNorm_le, he'.sqNorm_le]
  have hb (i : Fin (2*x.1)) :
      |Cyclic.concat (ofList uv.1) (ofList uv.2) i| ≤ cvpCertificateBound (moduleBoundInput x) :=
    (certificate_coeff_le M hdet 0 _ _ hnorm i).trans
      (moduleBoundInput_dominates (moduleNormInput x))
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
    have hi' : i < x.1 := by omega
    have hh := hb (Cyclic.blockEquiv x.1 (.inl ⟨i, hi'⟩))
    rw [Cyclic.concat_left] at hh
    change |uv.1.getD i 0| ≤ _ at hh
    rwa [List.getD_eq_getElem uv.1 0 hi] at hh
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
    have hi' : i < x.1 := by omega
    have hh := hb (Cyclic.blockEquiv x.1 (.inr ⟨i, hi'⟩))
    rw [Cyclic.concat_right] at hh
    change |uv.2.getD i 0| ≤ _ at hh
    rwa [List.getD_eq_getElem uv.2 0 hi] at hh

theorem module_certificate_length (x : SVPInput) (uv : List ℤ × List ℤ)
    (huv : moduleVerifier (x, uv) = true) :
    (encMultipliers uv).length ≤
      moduleWitnessPolynomial.eval (encCVP (moduleBoundInput x)).length := by
  have hl := ((moduleVerifier_spec x uv).mp huv).2.1
  have hr := ((moduleVerifier_spec x uv).mp huv).2.2.1
  have hb := module_certificate_bound x uv huv
  have h₁ := list_length_bound (moduleBoundInput x) uv.1
    (by dsimp [moduleBoundInput, IdealCVP.moduleBoundInput, moduleNormInput]; omega)
    (fun z hz => hb z (List.mem_append_left _ hz))
  have h₂ := list_length_bound (moduleBoundInput x) uv.2
    (by dsimp [moduleBoundInput, IdealCVP.moduleBoundInput, moduleNormInput]; omega)
    (fun z hz => hb z (List.mem_append_right _ hz))
  simp only [encMultipliers, length_encPair, moduleWitnessPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

end Power2ModuleSVP.Membership
