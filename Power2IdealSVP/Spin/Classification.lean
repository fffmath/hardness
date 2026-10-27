import Power2IdealSVP.Spin.Normalization
import Power2IdealSVP.Spin.Support

/-!
# Geometry of a passing coefficient spin

The guard and the signed cut reduce a passing spin to the integer run classification.
Every step retains the original coefficient multiplication and its local-field inequalities.

Paper: `paper/power2-ideal-svp.txt`, Section 1.3; audit Section 7.
-/

namespace Power2IdealSVP.Spin

open Power2ModuleSVP (Coeff)
open IdealCVP.Cyclotomic (mul monomial)

/-- A passing spin on the short coefficient arc has no isolated integer support position. -/
theorem short_passing_support_noIsolated {D : Finset ℕ} {A0 h : ℕ} (hh : 0 < h)
    {σ : Coeff (n A0)} (hσ : Ternary σ)
    (hf : ∀ i ∈ support σ, tau D A0 h ≤ fieldAt (G D A0 h) σ i)
    (hshort : ∀ x ∈ integerSupport σ, x ≤ R0 A0) : NoIsolated (integerSupport σ) := by
  have hsep := separation_lt_n A0
  have hb : ∀ i ∈ support σ, i.val ≤ R0 A0 := by
    intro i hi
    have := hshort i.val (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    exact_mod_cast this
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  rcases guard_active_has_neighbor hh hσ hf i hi with hm | hp
  · left
    exact lift_mem_support_image_of_short (by omega) hb (by omega) (by
      have := hb i hi
      omega) hm
  · right
    exact lift_mem_support_image_of_short (by omega) hb (by omega) (by
      have := hb i hi
      omega) hp

/-- Undoing a translation of a finite integer support gives the opposite translation. -/
theorem eq_image_add_of_image_sub_eq {W V : Finset ℤ} {t : ℤ}
    (he : W.image (fun x => x - t) = V) : W = V.image (fun x => x + t) := by
  ext x
  constructor
  · intro hx
    refine Finset.mem_image.mpr ⟨x - t, ?_, by omega⟩
    rw [← he]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    rw [← he] at hy
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
    have hzx : z = x := by omega
    exact hzx ▸ hz

/-- A passing spin already in the short coefficient arc has canonical integer geometry. -/
theorem classify_short_passing_spin {D : Finset ℕ} {A0 h : ℕ} (hD : DValid D A0)
    (hh : 0 < h) {σ : Coeff (n A0)} (hσ : OddAlternating σ)
    (hf : ∀ i ∈ support σ, tau D A0 h ≤ fieldAt (G D A0 h) σ i)
    (hshort : ∀ x ∈ integerSupport σ, 0 ≤ x ∧ x ≤ R0 A0) :
    ∃ (t : ℤ) (P : Finset ℤ), 0 ∈ P ∧ PositiveDifferences D P ∧
      integerSupport σ = (configuration P).image (fun x => x + t) := by
  have hdist : PositiveDifferences (Eplus D) (integerSupport σ) :=
    short_support_positiveDifferences (D := D) (A0 := A0) (h := h) hh hσ.1 hf
      (fun x hx => (hshort x hx).2)
  have hiso : NoIsolated (integerSupport σ) :=
    short_passing_support_noIsolated (D := D) (A0 := A0) (h := h) hh hσ.1 hf
      (fun x hx => (hshort x hx).2)
  have hodd : Odd (integerSupport σ).card := by
    simpa only [card_integerSupport] using hσ.2.1
  obtain ⟨t, P, h0, hP, htrans⟩ := integer_geometry hD hdist hiso hodd
  refine ⟨t, P, h0, hP, ?_⟩
  exact eq_image_add_of_image_sub_eq htrans

/-- Lemma 3 in coefficient form, including the signed shift and the component-label set. -/
theorem classify_passing_spin {D : Finset ℕ} {A0 h : ℕ} (hD : DValid D A0)
    (hh : 0 < h) {σ : Coeff (n A0)} (hσ : OddAlternating σ)
    (hf : ∀ i ∈ support σ, tau D A0 h ≤ fieldAt (G D A0 h) σ i) :
    ∃ (e : Fin (n A0)) (t : ℤ) (P : Finset ℤ),
      0 ∈ P ∧ PositiveDifferences D P ∧
      integerSupport (mul (monomial e 1) σ) =
        (configuration P).image (fun x => x + t) ∧
      (∀ x ∈ integerSupport (mul (monomial e 1) σ), 0 ≤ x ∧ x ≤ R0 A0) := by
  obtain ⟨e, he⟩ := exists_signed_shift_short_support hD hσ.support_nonempty
    (fun _ hi _ hj hij => guard_cyclic_pair_allowed hh hσ.1 hf hi hj hij)
  have hρ : OddAlternating (mul (monomial e 1) σ) := hσ.monomial_mul e
  have hfρ : ∀ i ∈ support (mul (monomial e 1) σ),
      tau D A0 h ≤ fieldAt (G D A0 h) (mul (monomial e 1) σ) i :=
    (active_fields_monomial_mul_iff e (G D A0 h) σ _).mpr hf
  obtain ⟨t, P, h0, hP, htrans⟩ :=
    classify_short_passing_spin (D := D) (A0 := A0) (h := h) hD hh hρ hfρ he
  exact ⟨e, t, P, h0, hP, htrans, he⟩

end Power2IdealSVP.Spin
