import Power2ModuleSVP.Problem

/-!
# Verifier

Executable checks and their exact semantic specifications.

Paper: `paper/power2svp.pdf`, Section 3.3 (proof of Theorem 1, NP membership).
-/
namespace Power2ModuleSVP
open IdealCVP

/-- Check that every stored coefficient lies between minus one and one. -/
def listCube (l : List ℤ) : Bool :=
  l.all fun z => decide (-1 ≤ z) && decide (z ≤ 1)

/-- Check that every stored coefficient is even. -/
def listEven (l : List ℤ) : Bool := l.all fun z => decide (z.natAbs % 2 = 0)

/-- Convert an exact-length list scan to the coefficient function. -/
theorem list_all_iff {d : ℕ} (l : List ℤ) (hl : l.length = d) (P : ℤ → Prop) :
    (∀ z ∈ l, P z) ↔ ∀ i : Fin d, P (ofList l i) := by
  constructor
  · intro h i
    have hi : i.val < l.length := by omega
    change P (l.getD i.val 0)
    rw [List.getD_eq_getElem l 0 hi]
    exact h _ (List.getElem_mem hi)
  · intro h z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
    have hi' : i < d := by omega
    have hh := h ⟨i, hi'⟩
    change P (l.getD i 0) at hh
    rwa [List.getD_eq_getElem l 0 hi] at hh

theorem listCube_spec {d : ℕ} (l : List ℤ) (hl : l.length = d) :
    listCube l = true ↔ Cube (ofList (d := d) l) := by
  simp only [listCube, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rw [list_all_iff l hl]
  simp only [Cube, abs_le]

theorem listEven_spec {d : ℕ} (l : List ℤ) (hl : l.length = d) :
    listEven l = true ↔ EvenCoeffs (ofList (d := d) l) := by
  simp only [listEven, List.all_eq_true, decide_eq_true_eq]
  rw [list_all_iff l hl]
  simp only [EvenCoeffs, ← Nat.even_iff, Int.natAbs_even]

/-- Check the dyadic degree, array lengths, and nonzero even coset generator. -/
def cosetWellFormedCheck (x : CosetInput) : Bool :=
  cvpWellFormedCheck (x.1, x.2.1, x.2.2, 0) &&
    x.2.1.any (fun z => decide (z ≠ 0)) && listEven x.2.1

/-- Check the dyadic degree, array lengths, and independence of the generators. -/
def moduleWellFormedCheck (x : SVPInput) : Bool :=
  cvpWellFormedCheck (x.1, x.2.1.1, x.2.1.2, 0) &&
    decide (x.2.2.1.length = x.1) && decide (x.2.2.2.length = x.1) &&
    listIndependent x.1 x.2.1 x.2.2

theorem cosetWellFormedCheck_spec (x : CosetInput) :
    cosetWellFormedCheck x = true ↔ CosetInput.WellFormed x := by
  simp only [cosetWellFormedCheck, Bool.and_eq_true, cvpWellFormedCheck_eq,
    CVPInput.WellFormed]
  constructor
  · rintro ⟨⟨⟨hd, hg, hh⟩, hn⟩, he⟩
    exact ⟨hd, hg, hh, (list_any_ne_zero _ _ hg).mp hn, (listEven_spec _ hg).mp he⟩
  · rintro ⟨hd, hg, hh, hn, he⟩
    exact ⟨⟨⟨hd, hg, hh⟩, (list_any_ne_zero _ _ hg).mpr hn⟩,
      (listEven_spec _ hg).mpr he⟩

theorem moduleWellFormedCheck_spec (x : SVPInput) :
    moduleWellFormedCheck x = true ↔ SVPInput.WellFormed x := by
  simp [moduleWellFormedCheck, cvpWellFormedCheck_eq, CVPInput.WellFormed,
    SVPInput.WellFormed, Dyadic, and_assoc]

/-- Compute the translated coset vector from a stored multiplier. -/
def cosetProduct (x : CosetInput) (u : List ℤ) : List ℤ :=
  listAdd x.1 x.2.2 (negacyclicMul x.1 x.2.1 u)

/-- Compute both coefficient arrays of the module vector from stored multipliers. -/
def moduleProduct (x : SVPInput) (uv : List ℤ × List ℤ) : List ℤ × List ℤ :=
  (listAdd x.1 (negacyclicMul x.1 x.2.1.1 uv.1) (negacyclicMul x.1 x.2.2.1 uv.2),
   listAdd x.1 (negacyclicMul x.1 x.2.1.2 uv.1) (negacyclicMul x.1 x.2.2.2 uv.2))

@[simp] theorem length_cosetProduct (x : CosetInput) (u : List ℤ) :
    (cosetProduct x u).length = x.1 := by simp [cosetProduct, listAdd]
@[simp] theorem length_moduleProduct (x : SVPInput) (uv : List ℤ × List ℤ) :
    (moduleProduct x uv).1.length = x.1 ∧ (moduleProduct x uv).2.length = x.1 := by
  simp [moduleProduct, listAdd]

theorem ofList_cosetProduct (x : CosetInput) (u : List ℤ) :
    ofList (d := x.1) (cosetProduct x u) =
      ofList x.2.2 + Cyclotomic.mul (ofList x.2.1) (ofList u) := by
  simp [cosetProduct, ofList_listAdd, ofList_negacyclicMul]

theorem ofList_moduleProduct (x : SVPInput) (uv : List ℤ × List ℤ) :
    (ofList (d := x.1) (moduleProduct x uv).1, ofList (moduleProduct x uv).2) =
      moduleVector (ofList x.2.1.1, ofList x.2.1.2)
        (ofList x.2.2.1, ofList x.2.2.2) (ofList uv.1) (ofList uv.2) := by
  simp [moduleProduct, moduleVector, ofList_listAdd, ofList_negacyclicMul]

/-- Verify the input shape and a multiplier witnessing coset membership in the unit cube. -/
def cosetVerifier (p : CosetInput × List ℤ) : Bool :=
  cosetWellFormedCheck p.1 && decide (p.2.length = p.1.1) &&
    listCube (cosetProduct p.1 p.2)

/-- Check that a stored pair is nonzero and lies in the coefficient unit cube. -/
def moduleVectorCheck (z : List ℤ × List ℤ) : Bool :=
  (z.1.any (fun t => decide (t ≠ 0)) || z.2.any (fun t => decide (t ≠ 0))) &&
    listCube z.1 && listCube z.2

/-- Verify the input shape and multipliers witnessing a nonzero unit-cube module vector. -/
def moduleVerifier (p : SVPInput × (List ℤ × List ℤ)) : Bool :=
  moduleWellFormedCheck p.1 && decide (p.2.1.length = p.1.1) &&
    decide (p.2.2.length = p.1.1) && moduleVectorCheck (moduleProduct p.1 p.2)

theorem cosetVerifier_spec (x : CosetInput) (u : List ℤ) :
    cosetVerifier (x, u) = true ↔ CosetInput.WellFormed x ∧ u.length = x.1 ∧
      Cube (ofList (d := x.1) x.2.2 + Cyclotomic.mul (ofList x.2.1) (ofList u)) := by
  simp only [cosetVerifier, Bool.and_eq_true, cosetWellFormedCheck_spec,
    decide_eq_true_eq, listCube_spec _ (length_cosetProduct x u), ofList_cosetProduct,
    and_assoc]

theorem moduleVerifier_spec (x : SVPInput) (uv : List ℤ × List ℤ) :
    moduleVerifier (x, uv) = true ↔ SVPInput.WellFormed x ∧
      uv.1.length = x.1 ∧ uv.2.length = x.1 ∧
      let z := moduleVector (ofList (d := x.1) x.2.1.1, ofList x.2.1.2)
        (ofList x.2.2.1, ofList x.2.2.2) (ofList uv.1) (ofList uv.2)
      z ≠ 0 ∧ Cube z.1 ∧ Cube z.2 := by
  have hz (a b : Coeff x.1) : (a ≠ 0 ∨ b ≠ 0) ↔ (a, b) ≠ 0 := by
    simp only [ne_eq, Prod.mk_eq_zero, not_and_or]
  simp only [moduleVerifier, moduleVectorCheck, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq,
    moduleWellFormedCheck_spec, list_any_ne_zero _ _ (length_moduleProduct x uv).1,
    list_any_ne_zero _ _ (length_moduleProduct x uv).2,
    listCube_spec _ (length_moduleProduct x uv).1,
    listCube_spec _ (length_moduleProduct x uv).2, hz, and_assoc]
  rw [ofList_moduleProduct]
  simp only [moduleProduct, moduleVector, ofList_listAdd, ofList_negacyclicMul]

theorem cosetVerifier_correct (x : CosetInput) :
    x ∈ CosetLang ↔ ∃ u, cosetVerifier (x, u) = true := by
  constructor
  · rintro ⟨hw, u, hu⟩
    refine ⟨toList u, (cosetVerifier_spec x _).mpr ⟨hw, length_toList u, ?_⟩⟩
    simpa only [ofList_toList] using hu
  · rintro ⟨u, hu⟩
    obtain ⟨hw, _, h⟩ := (cosetVerifier_spec x u).mp hu
    exact ⟨hw, ofList u, h⟩

theorem moduleVerifier_correct (x : SVPInput) :
    x ∈ ModuleSVPLang ↔ ∃ uv, moduleVerifier (x, uv) = true := by
  constructor
  · rintro ⟨hw, u, v, hn, hu, hv⟩
    refine ⟨(toList u, toList v), (moduleVerifier_spec x _).mpr
      ⟨hw, length_toList u, length_toList v, ?_⟩⟩
    simpa only [ofList_toList] using And.intro hn (And.intro hu hv)
  · rintro ⟨uv, h⟩
    obtain ⟨hw, _, _, hn, hu, hv⟩ := (moduleVerifier_spec x uv).mp h
    exact ⟨hw, ofList uv.1, ofList uv.2, hn, hu, hv⟩

end Power2ModuleSVP
