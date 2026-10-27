import Power2IdealSVP.Spin.Support
import Power2IdealSVP.Spin.Interaction
import Power2IdealSVP.Spin.Guard

/-!
# Canonical configurations as actual sparse spins

The integer interaction table is transferred to negacyclic coefficient multiplication after
placing the canonical support in the short interval. This supplies the converse sparse-spin
witness and the field formula used in both directions of the decision equivalence.

Paper: `paper/power2-ideal-svp.txt`, Sections 1.3–1.4; audit Sections 8–10.
-/

namespace Power2IdealSVP.Spin

open Power2ModuleSVP (Coeff)
open IdealCVP.Cyclotomic (mul)

/-- Translate the canonical integer configuration before embedding it into the ring. -/
def translatedConfiguration (P : Finset ℤ) (t : ℤ) : Finset ℤ :=
  (configuration P).image fun x => x + t

/-- The actual odd alternating spin associated with a placed component set. -/
def configurationSpin (A0 : ℕ) (P : Finset ℤ) (t : ℤ) : Coeff (n A0) :=
  embedSupport (n A0) (translatedConfiguration P t) 1

/-- A short placement is a valid placement inside the coefficient interval. -/
theorem shortPlacement_bounds {A0 : ℕ} {P : Finset ℤ} {t : ℤ}
    (ht : ∀ x ∈ configuration P, 0 ≤ x + t ∧ x + t ≤ R0 A0) :
    ∀ z ∈ translatedConfiguration P t, 0 ≤ z ∧ z < n A0 := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  have := ht x hx
  have := separation_lt_n A0
  omega

/-- The coefficient spin has exactly the prescribed translated integer support. -/
theorem integerSupport_configurationSpin {A0 : ℕ} {P : Finset ℤ} {t : ℤ}
    (ht : ∀ x ∈ configuration P, 0 ≤ x + t ∧ x + t ≤ R0 A0) :
    integerSupport (configurationSpin A0 P t) = translatedConfiguration P t := by
  exact integerSupport_embedSupport (shortPlacement_bounds ht) (Or.inr rfl)

/-- The canonical coefficient construction is an odd alternating sparse spin. -/
theorem oddAlternating_configurationSpin {A0 : ℕ} {P : Finset ℤ} {t : ℤ}
    (h0 : 0 ∈ P) (ht : ∀ x ∈ configuration P, 0 ≤ x + t ∧ x + t ≤ R0 A0) :
    OddAlternating (configurationSpin A0 P t) := by
  apply oddAlternating_embedSupport (shortPlacement_bounds ht) _ (Or.inr rfl)
  rw [translatedConfiguration, Finset.card_image_of_injective]
  · exact odd_card_configuration h0
  · exact fun _ _ h => add_right_cancel h

/-- At a component position the actual coefficient has its canonical sign. -/
theorem configurationSpin_at {A0 : ℕ} {P : Finset ℤ} {t q x : ℤ}
    (h0 : 0 ∈ P) (ht : ∀ y ∈ configuration P, 0 ≤ y + t ∧ y + t ≤ R0 A0)
    (hq : q ∈ P) (hx : x ∈ component q) (i : Fin (n A0))
    (hi : (i.val : ℤ) = x + t) :
    configurationSpin A0 P t i = componentSign q x := by
  rw [configurationSpin, embedSupport_apply (shortPlacement_bounds ht), one_mul, hi,
    translatedConfiguration, integerAlternating_translate,
    integerAlternating_configuration h0 hq hx]
  rfl

/-- Every active coefficient of a placed configuration stays in the short interval. -/
theorem configurationSpin_short {A0 : ℕ} {P : Finset ℤ} {t : ℤ}
    (ht : ∀ y ∈ configuration P, 0 ≤ y + t ∧ y + t ≤ R0 A0)
    {i : Fin (n A0)} (hi : i ∈ support (configurationSpin A0 P t)) :
    (i.val : ℤ) ≤ R0 A0 := by
  have hi' := (coe_mem_integerSupport (configurationSpin A0 P t) i).mpr hi
  rw [integerSupport_configurationSpin ht] at hi'
  obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hi'
  rw [← he]
  exact (ht x hx).2

/-- Sum over ordinary integer representatives instead of coefficient support indices. -/
theorem sum_integerSupport {m : ℕ} (σ : Coeff m) (F : ℤ → ℤ) :
    (∑ j ∈ support σ, F (j.val : ℤ)) = ∑ z ∈ integerSupport σ, F z := by
  rw [integerSupport, Finset.sum_image]
  intro i _ j _ he
  change (i.val : ℤ) = (j.val : ℤ) at he
  exact Fin.ext (by exact_mod_cast he)

/-- Translation and disjoint component grouping for an ordinary integer kernel sum. -/
theorem configuration_kernel_group {P : Finset ℤ} (h0 : 0 ∈ P) (t x : ℤ)
    (F : ℤ → ℤ) :
    (∑ z ∈ translatedConfiguration P t,
      F (x + t - z) * integerAlternating (translatedConfiguration P t) z) =
      ∑ r ∈ P, ∑ y ∈ component r, F (x - y) * componentSign r y := by
  rw [translatedConfiguration, Finset.sum_image]
  · calc
      _ = ∑ y ∈ configuration P,
          F (x - y) * integerAlternating (configuration P) y := by
        apply Finset.sum_congr rfl
        intro y _
        rw [integerAlternating_translate, show x + t - (y + t) = x - y by ring]
      _ = _ := by
        rw [configuration, Finset.sum_biUnion]
        · apply Finset.sum_congr rfl
          intro r hr
          apply Finset.sum_congr rfl
          intro y hy
          have heq : integerAlternating (configuration P) y = componentSign r y :=
            integerAlternating_configuration h0 hr hy
          exact congrArg (fun a : ℤ => F (x - y) * a) heq
        · intro r _ u _ hru
          exact components_disjoint hru
  · intro y _ z _ he
    exact add_right_cancel he

/-- Kernel sums on the actual coefficient support equal sums over signed components. -/
theorem configurationSpin_kernel_sum {A0 : ℕ} {P : Finset ℤ} {t q x : ℤ}
    (h0 : 0 ∈ P) (ht : ∀ y ∈ configuration P, 0 ≤ y + t ∧ y + t ≤ R0 A0)
    (hq : q ∈ P) (hx : x ∈ component q) (i : Fin (n A0))
    (hi : (i.val : ℤ) = x + t) (F : ℤ → ℤ) :
    configurationSpin A0 P t i * ∑ j ∈ support (configurationSpin A0 P t),
        F ((i.val : ℤ) - j.val) * configurationSpin A0 P t j =
      ∑ r ∈ P, componentSign q x *
        ∑ y ∈ component r, F (x - y) * componentSign r y := by
  let W := translatedConfiguration P t
  let σ := configurationSpin A0 P t
  have hs : integerSupport σ = W := integerSupport_configurationSpin ht
  have hval (j : Fin (n A0)) : σ j = integerAlternating W (j.val : ℤ) := by
    change embedSupport (n A0) (translatedConfiguration P t) 1 j =
      integerAlternating (translatedConfiguration P t) (j.val : ℤ)
    exact (embedSupport_apply (shortPlacement_bounds ht) 1 j).trans (one_mul _)
  have hsum : (∑ j ∈ support σ, F ((i.val : ℤ) - j.val) * σ j) =
      ∑ r ∈ P, ∑ y ∈ component r, F (x - y) * componentSign r y := by
    calc
      _ = ∑ j ∈ support σ, F ((i.val : ℤ) - j.val) *
          integerAlternating W (j.val : ℤ) := by
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg (fun a : ℤ => F ((i.val : ℤ) - j.val) * a) (hval j)
      _ = ∑ z ∈ integerSupport σ, F ((i.val : ℤ) - z) * integerAlternating W z :=
        sum_integerSupport σ (fun z => F ((i.val : ℤ) - z) * integerAlternating W z)
      _ = ∑ z ∈ W, F ((i.val : ℤ) - z) * integerAlternating W z :=
        congrArg (fun V : Finset ℤ => ∑ z ∈ V,
          F ((i.val : ℤ) - z) * integerAlternating W z) hs
      _ = ∑ z ∈ W, F (x + t - z) * integerAlternating W z :=
        congrArg (fun a : ℤ => ∑ z ∈ W, F (a - z) * integerAlternating W z) hi
      _ = _ := configuration_kernel_group h0 t x F
  calc
    _ = componentSign q x *
        ∑ j ∈ support σ, F ((i.val : ℤ) - j.val) * σ j :=
      congrArg (fun a : ℤ => a *
        ∑ j ∈ support σ, F ((i.val : ℤ) - j.val) * σ j)
          (configurationSpin_at h0 ht hq hx i hi)
    _ = componentSign q x *
        ∑ r ∈ P, ∑ y ∈ component r, F (x - y) * componentSign r y :=
      congrArg (fun a : ℤ => componentSign q x * a) hsum
    _ = _ := Finset.mul_sum _ _ _

/-- The actual `T`-field has exactly the component-table total. -/
theorem configurationSpin_T_field {D : Finset ℕ} {A0 : ℕ} {P : Finset ℤ}
    (hD : DValid D A0) (h0 : 0 ∈ P) {t q x : ℤ}
    (ht : ∀ y ∈ configuration P, 0 ≤ y + t ∧ y + t ≤ R0 A0)
    (hq : q ∈ P) (hx : x ∈ component q) (i : Fin (n A0))
    (hi : (i.val : ℤ) = x + t) :
    fieldAt (T D A0) (configurationSpin A0 P t) i = configurationField D P q x := by
  have hiW : x ∈ configuration P := Finset.mem_biUnion.mpr ⟨q, hq, hx⟩
  have hiB := ht x hiW
  unfold fieldAt
  rw [mul_T_on_short_support hD _ i]
  · exact configurationSpin_kernel_sum h0 ht hq hx i hi (interactionKernel D)
  · intro j hj
    have hjB := configurationSpin_short ht hj
    apply abs_le.mpr
    constructor <;> omega

/-- The actual nearest-neighbour field has exactly the component-table value. -/
theorem configurationSpin_neighbor_field {A0 : ℕ} {P : Finset ℤ}
    (h0 : 0 ∈ P) {t q x : ℤ}
    (ht : ∀ y ∈ configuration P, 0 ≤ y + t ∧ y + t ≤ R0 A0)
    (hq : q ∈ P) (hx : x ∈ component q) (i : Fin (n A0))
    (hi : (i.val : ℤ) = x + t) :
    -(configurationSpin A0 P t i *
      (lift (configurationSpin A0 P t) ((i.val : ℤ) - 1) +
       lift (configurationSpin A0 P t) ((i.val : ℤ) + 1))) =
      neighborConfigurationField P q x := by
  let σ := configurationSpin A0 P t
  have hiW : x ∈ configuration P := Finset.mem_biUnion.mpr ⟨q, hq, hx⟩
  have hiB := ht x hiW
  have hm : lift σ ((i.val : ℤ) - 1) + lift σ ((i.val : ℤ) + 1) =
      mul (xpow (n A0) 1 + xpow (n A0) (-1)) σ i := by
    simp [IdealCVP.Cyclotomic.mul_add_left, mul_xpow_apply (n_pos A0)]
  rw [hm, mul_on_support]
  have hk : ∀ j ∈ support σ,
      lift (xpow (n A0) 1 + xpow (n A0) (-1)) ((i.val : ℤ) - j.val) =
        neighborKernel ((i.val : ℤ) - j.val) := by
    intro j hj
    have hjB := configurationSpin_short ht hj
    apply lift_neighbors_eq_kernel
    apply abs_le.mpr
    constructor <;> omega
  have hsum : (∑ j ∈ support σ,
      lift (xpow (n A0) 1 + xpow (n A0) (-1)) ((i.val : ℤ) - j.val) * σ j) =
      ∑ j ∈ support σ, neighborKernel ((i.val : ℤ) - j.val) * σ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hk j hj]
  rw [hsum, configurationSpin_kernel_sum h0 ht hq hx i hi neighborKernel]
  unfold neighborConfigurationField
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r _
  unfold neighborComponentField
  ring

/-- The guard vanishes at every active coordinate of a placed allowed configuration. -/
theorem configurationSpin_guard_zero {D : Finset ℕ} {A0 : ℕ} {P : Finset ℤ}
    (hP : PositiveDifferences D P) {t q x : ℤ}
    (ht : ∀ y ∈ configuration P, 0 ≤ y + t ∧ y + t ≤ R0 A0)
    (hq : q ∈ P) (hx : x ∈ component q) (i : Fin (n A0))
    (hi : (i.val : ℤ) = x + t) :
    mul (A D A0) (configurationSpin A0 P t) i = 0 := by
  have hxW : x ∈ configuration P := Finset.mem_biUnion.mpr ⟨q, hq, hx⟩
  have hiB := ht x hxW
  rw [mul_on_support]
  apply Finset.sum_eq_zero
  intro j hj
  have hjW := (coe_mem_integerSupport (configurationSpin A0 P t) j).mpr hj
  rw [integerSupport_configurationSpin ht] at hjW
  obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hjW
  have hjB := ht y hy
  rw [lift_A_eq_zero]
  · ring
  · apply abs_le.mpr
    constructor <;> omega
  · rcases lt_trichotomy x y with hxy | rfl | hyx
    · right
      have ha := configuration_allowed hP hxW hy hxy
      have habs : ((i.val : ℤ) - j.val).natAbs = (y - x).toNat := by
        rw [hi, ← he, show x + t - (y + t) = -(y - x) by ring, Int.natAbs_neg]
        have ha : (((y - x).natAbs : ℕ) : ℤ) = y - x :=
          Int.natAbs_of_nonneg (by omega)
        have hb : (((y - x).toNat : ℕ) : ℤ) = y - x :=
          Int.toNat_of_nonneg (by omega)
        omega
      rwa [habs]
    · left
      omega
    · right
      have ha := configuration_allowed hP hy hxW hyx
      have habs : ((i.val : ℤ) - j.val).natAbs = (x - y).toNat := by
        rw [hi, ← he, show x + t - (y + t) = x - y by ring]
        have ha : (((x - y).natAbs : ℕ) : ℤ) = x - y :=
          Int.natAbs_of_nonneg (by omega)
        have hb : (((x - y).toNat : ℕ) : ℤ) = x - y :=
          Int.toNat_of_nonneg (by omega)
        omega
      rwa [habs]

/-- Actual coefficient fields agree with the entire small-field table. -/
theorem configurationSpin_field {D : Finset ℕ} {A0 h : ℕ} {P : Finset ℤ}
    (hD : DValid D A0) (hP : PositiveDifferences D P) (h0 : 0 ∈ P) {t q x : ℤ}
    (ht : ∀ y ∈ configuration P, 0 ≤ y + t ∧ y + t ≤ R0 A0)
    (hq : q ∈ P) (hx : x ∈ component q) (i : Fin (n A0))
    (hi : (i.val : ℤ) = x + t) :
    fieldAt (G D A0 h) (configurationSpin A0 P t) i =
      smallConfigurationField (C D A0 h) D P q x := by
  rw [fieldAt_G_decomposition, show fieldAt (A D A0) (configurationSpin A0 P t) i = 0 by
    unfold fieldAt; rw [configurationSpin_guard_zero hP ht hq hx i hi, mul_zero]]
  have hn := configurationSpin_neighbor_field h0 ht hq hx i hi
  have hT := configurationSpin_T_field hD h0 ht hq hx i hi
  unfold fieldAt at hT
  unfold smallConfigurationField
  rw [hT]
  rw [← hn]
  ring

/-- The placed coefficient spin passes precisely when its component count reaches the target. -/
theorem configurationSpin_threshold_iff {D : Finset ℕ} {A0 h : ℕ} {P : Finset ℤ}
    (hD : DValid D A0) (hP : PositiveDifferences D P) (h0 : 0 ∈ P) {t : ℤ}
    (ht : ∀ y ∈ configuration P, 0 ≤ y + t ∧ y + t ≤ R0 A0) :
    (∀ i ∈ support (configurationSpin A0 P t),
      tau D A0 h ≤ fieldAt (G D A0 h) (configurationSpin A0 P t) i) ↔ h ≤ P.card := by
  constructor
  · intro hfield
    apply (smallConfigurationField_threshold hD hP h0).mp
    intro q hq x hx
    have hxW : x ∈ configuration P := Finset.mem_biUnion.mpr ⟨q, hq, hx⟩
    have hxB := ht x hxW
    have hn := separation_lt_n A0
    let i : Fin (n A0) := ⟨(x + t).toNat, by omega⟩
    have hi : (i.val : ℤ) = x + t := Int.toNat_of_nonneg hxB.1
    have his : i ∈ support (configurationSpin A0 P t) := by
      rw [← coe_mem_integerSupport, integerSupport_configurationSpin ht]
      exact Finset.mem_image.mpr ⟨x, hxW, hi.symm⟩
    have hf := hfield i his
    rwa [configurationSpin_field hD hP h0 ht hq hx i hi] at hf
  · intro hh i his
    have hiW := (coe_mem_integerSupport (configurationSpin A0 P t) i).mpr his
    rw [integerSupport_configurationSpin ht] at hiW
    obtain ⟨x, hxW, hi⟩ := Finset.mem_image.mp hiW
    obtain ⟨q, hq, hx⟩ := Finset.mem_biUnion.mp hxW
    rw [configurationSpin_field hD hP h0 ht hq hx i hi.symm]
    exact (smallConfigurationField_threshold hD hP h0).mpr hh q hq x hx

/-- The finite-ring sparse-spin minimum equals the exact endpoint-table minimum. -/
theorem spinValue_configurationSpin {D : Finset ℕ} {A0 h : ℕ} {P : Finset ℤ}
    (hD : DValid D A0) (hP : PositiveDifferences D P) (h0 : 0 ∈ P) {t : ℤ}
    (ht : ∀ y ∈ configuration P, 0 ≤ y + t ∧ y + t ≤ R0 A0) :
    spinValue (G D A0 h) (configurationSpin A0 P t) = C D A0 h + P.card - 1 := by
  have hσ := oddAlternating_configurationSpin h0 ht
  have hmin := smallConfigurationField_min hD hP h0 (le_of_lt (C_pos D A0 h))
  apply le_antisymm
  · have hx : (0 : ℤ) ∈ component 0 := by simp [component]
    have hxW : (0 : ℤ) ∈ configuration P := Finset.mem_biUnion.mpr ⟨0, h0, hx⟩
    have hb := ht 0 hxW
    have hn := separation_lt_n A0
    let i : Fin (n A0) := ⟨t.toNat, by omega⟩
    have hi : (i.val : ℤ) = 0 + t := by dsimp [i]; omega
    have his : i ∈ support (configurationSpin A0 P t) := by
      rw [← coe_mem_integerSupport, integerSupport_configurationSpin ht]
      exact Finset.mem_image.mpr ⟨0, hxW, hi.symm⟩
    have hf := (le_spinValue_iff (G := G D A0 h) hσ
      (spinValue (G D A0 h) (configurationSpin A0 P t))).mp le_rfl i his
    rwa [configurationSpin_field hD hP h0 ht h0 hx i hi, hmin.2] at hf
  · apply (le_spinValue_iff hσ _).mpr
    intro i his
    have hiW := (coe_mem_integerSupport (configurationSpin A0 P t) i).mpr his
    rw [integerSupport_configurationSpin ht] at hiW
    obtain ⟨x, hxW, hi⟩ := Finset.mem_image.mp hiW
    obtain ⟨q, hq, hx⟩ := Finset.mem_biUnion.mp hxW
    rw [configurationSpin_field hD hP h0 ht hq hx i hi.symm]
    exact hmin.1 q hq x hx

/-- Any anchored difference set of the requested size yields an actual passing sparse spin. -/
theorem exists_spin_of_differences {D : Finset ℕ} {A0 h : ℕ} {P : Finset ℤ}
    (hD : DValid D A0) (hP : PositiveDifferences D P) (h0 : 0 ∈ P)
    (hh : h ≤ P.card) :
    ∃ σ : Coeff (n A0), OddAlternating σ ∧
      ∀ i ∈ support σ, tau D A0 h ≤ fieldAt (G D A0 h) σ i := by
  obtain ⟨s, hs⟩ := configuration_in_short_interval hD hP h0
  have ht : ∀ y ∈ configuration P, 0 ≤ y + -s ∧ y + -s ≤ R0 A0 := by
    intro y hy
    simpa only [sub_eq_add_neg] using hs y hy
  exact ⟨configurationSpin A0 P (-s), oddAlternating_configurationSpin h0 ht,
    (configurationSpin_threshold_iff hD hP h0 ht).mpr hh⟩

end Power2IdealSVP.Spin
