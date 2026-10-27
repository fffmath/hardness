import Power2IdealSVP.Spin.Classification
import Power2IdealSVP.Spin.Converse

/-!
# The sparse-spin decision equivalence

This is equation (1) before the separate source-label extraction is glued in. The distance
set is arbitrary, subject only to positivity and its upper bound. Every witness here is an
actual coefficient array or finite integer set; no geometric or interaction claim is assumed.

Paper: `paper/power2-ideal-svp.txt`, equation (1); audit Section 10.
-/

namespace Power2IdealSVP.Spin

open Power2ModuleSVP (Coeff)
open IdealCVP.Cyclotomic (mul monomial)

/-- Equation (1) in the abstract difference-set form of the source interface.

The equivalence holds for every positive target, including targets one and two. The graph
dispatcher uses it at targets at least three, where the source extraction lemma applies.
-/
theorem theta_threshold_iff_differences {D : Finset ℕ} {A0 h : ℕ}
    (hD : DValid D A0) (hh : 0 < h) :
    tau D A0 h ≤ Theta (G D A0 h) ↔
      ∃ P : Finset ℤ, 0 ∈ P ∧ h ≤ P.card ∧ PositiveDifferences D P := by
  rw [le_Theta_iff (n_pos A0)]
  constructor
  · rintro ⟨σ, hσ, hf⟩
    obtain ⟨e, t, P, h0, hP, hsupport, hshort⟩ := classify_passing_spin hD hh hσ hf
    let ρ := mul (monomial e 1) σ
    have hρ : OddAlternating ρ := hσ.monomial_mul e
    have hfρ : ∀ i ∈ support ρ, tau D A0 h ≤ fieldAt (G D A0 h) ρ i :=
      (active_fields_monomial_mul_iff e (G D A0 h) σ _).mpr hf
    have ht : ∀ x ∈ configuration P, 0 ≤ x + t ∧ x + t ≤ R0 A0 := by
      intro x hx
      apply hshort
      rw [hsupport]
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hs : support ρ = support (configurationSpin A0 P t) := by
      apply support_eq_of_integerSupport_eq
      exact hsupport.trans (integerSupport_configurationSpin ht).symm
    have hfields : ∀ i ∈ support (configurationSpin A0 P t),
        tau D A0 h ≤ fieldAt (G D A0 h) (configurationSpin A0 P t) i := by
      intro i hi
      have hiρ : i ∈ support ρ := hs.symm ▸ hi
      have heq := hρ.fieldAt_eq_of_support_eq (oddAlternating_configurationSpin h0 ht)
        hs (G D A0 h) i
      exact heq ▸ hfρ i hiρ
    exact ⟨P, h0, (configurationSpin_threshold_iff hD hP h0 ht).mp hfields, hP⟩
  · rintro ⟨P, h0, hcard, hP⟩
    exact exists_spin_of_differences hD hP h0 hcard

end Power2IdealSVP.Spin
