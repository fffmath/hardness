import Power2IdealSVP.Ideal.FullSigns
import Power2IdealSVP.Ideal.Parity
import Power2IdealSVP.Problem

/-!
# The shortest vector lies in the full-sign layer

For every integer multiplier `K`, domination by `M = 3 ‖K‖₁ + 1` separates
images of full signs from every other nonzero vector in the parity ideal.
This proves equation (3) before using any threshold or graph promise.

Paper: `paper/power2-ideal-svp.pdf`, Section 1.5; audit Section 12.
-/

namespace Power2IdealSVP.Ideal
open Power2ModuleSVP IdealCVP.Cyclotomic Power2IdealSVP.Algebra

/-- The scalar amplitude that strictly separates the first two parity layers. -/
def amplitude {n : ℕ} (K : Coeff n) : ℤ := 3 * coeffL1 K + 1

/-- The principal generator `(M-K)S`. -/
def generator {n : ℕ} (hn : 0 < n) (K : Coeff n) : Coeff n :=
  mul (amplitude K • coeffOne hn - K) (sumPoly n)

/-- Multiplication by the output generator factors through the parity ideal. -/
theorem generator_mul {n : ℕ} (hn : 0 < n) (K a : Coeff n) :
    mul (generator hn K) a =
      amplitude K • mul (sumPoly n) a - mul K (mul (sumPoly n) a) := by
  rw [generator, coeff_mul_assoc hn, coeff_mul_sub_left, mul_smul_left, mul_coeffOne]

/-- The amplitude strictly dominates the coefficient one norm. -/
theorem l1_lt_amplitude {n : ℕ} (K : Coeff n) : coeffL1 K < amplitude K := by
  have := coeffL1_nonneg K
  dsimp [amplitude]
  omega

/-- Every nonzero parity vector outside the full-sign layer has norm at least two. -/
theorem two_le_normInf_of_not_signs {n : ℕ} {y : Coeff n}
    (hp : CommonParity y) (hy : y ≠ 0) (hs : ¬ Signs y) : 2 ≤ normInf y := by
  by_contra h
  apply hs
  apply commonParity_cube_signs hp hy
  intro i
  have := abs_le_normInf y i
  omega

/-- Every nonzero output ideal vector has the asserted lower norm bound. -/
theorem objective_le_ideal_image {n : ℕ} (hn : 0 < n) (K a : Coeff n)
    (ha : mul (generator hn K) a ≠ 0) :
    amplitude K - psi hn K ≤ normInf (mul (generator hn K) a) := by
  let y := mul (sumPoly n) a
  have he : mul (generator hn K) a = amplitude K • y - mul K y := generator_mul hn K a
  have hy : y ≠ 0 := by
    intro hz
    apply ha
    rw [he, hz]
    simp
  have hp : CommonParity y := (mem_sumPoly_ideal_iff hn y).mp ⟨a, rfl⟩
  rw [he]
  by_cases hs : Signs y
  · exact objective_le_sign_image hn K y _ (l1_lt_amplitude K) hs
  · have htwo := two_le_normInf_of_not_signs hp hy hs
    have hc := coercive hn K y (amplitude K)
      (le_trans (coeffL1_nonneg K) (le_of_lt (l1_lt_amplitude K)))
    have hb := (psi_bounds hn K).1
    have hk := coeffL1_nonneg K
    dsimp [amplitude] at *
    nlinarith

/-- A nonzero ideal vector attains the lower bound, through a full sign. -/
theorem exists_ideal_image_eq {n : ℕ} (hn : 0 < n) (K : Coeff n) :
    ∃ a : Coeff n, mul (generator hn K) a ≠ 0 ∧
      normInf (mul (generator hn K) a) = amplitude K - psi hn K := by
  obtain ⟨s, hs, he⟩ := exists_sign_image_eq hn K _ (l1_lt_amplitude K)
  obtain ⟨a, ha⟩ := (mem_sumPoly_ideal_iff hn s).mpr (signs_commonParity hs)
  refine ⟨a, ?_, ?_⟩
  · rw [generator_mul, ha]
    intro hz
    have hz' := (dominated_eq_zero_iff hn K s _ (l1_lt_amplitude K)).mp hz
    have hi := hs ⟨0, hn⟩
    rw [hz'] at hi
    simp at hi
  · rw [generator_mul, ha]
    exact he

/-- The constructed principal generator is nonzero in every positive dimension. -/
theorem generator_ne_zero {n : ℕ} (hn : 0 < n) (K : Coeff n) : generator hn K ≠ 0 := by
  obtain ⟨a, ha, _⟩ := exists_ideal_image_eq hn K
  intro hz
  apply ha
  rw [hz, coeff_mul_zero_left]

/-- The first coefficient maximum norm of a principal ideal, as a natural infimum.
The infimum is only used below when an explicit nonzero vector attains it. -/
noncomputable def lambdaInf {n : ℕ} (f : Coeff n) : ℕ :=
  sInf {r : ℕ | ∃ a : Coeff n, mul f a ≠ 0 ∧ coeffSup (mul f a) = r}

/-- Equation (3), expressed as an integer equality with the actual ideal minimum. -/
theorem lambdaInf_generator {n : ℕ} (hn : 0 < n) (K : Coeff n) :
    (lambdaInf (generator hn K) : ℤ) = amplitude K - psi hn K := by
  obtain ⟨a, ha, he⟩ := exists_ideal_image_eq hn K
  have hmin : lambdaInf (generator hn K) = coeffSup (mul (generator hn K) a) := by
    apply le_antisymm
    · exact Nat.sInf_le ⟨a, ha, rfl⟩
    · have hex : ({r : ℕ | ∃ b : Coeff n,
          mul (generator hn K) b ≠ 0 ∧ coeffSup (mul (generator hn K) b) = r} :
          Set ℕ).Nonempty := ⟨_, a, ha, rfl⟩
      obtain ⟨b, hb, heq⟩ := Nat.sInf_mem hex
      have hl := objective_le_ideal_image hn K b hb
      rw [← he] at hl
      dsimp [normInf] at hl
      change coeffSup (mul (generator hn K) a) ≤
        sInf {r : ℕ | ∃ b : Coeff n,
          mul (generator hn K) b ≠ 0 ∧ coeffSup (mul (generator hn K) b) = r}
      rw [← heq]
      exact_mod_cast hl
  rw [hmin]
  exact he

/-- The exact decision form of equation (3), compatible with the fixed problem interface. -/
theorem idealYes_generator_iff {n : ℕ} (hn : 0 < n) (K : Coeff n) (r : ℕ) :
    IdealYes (generator hn K) r ↔ amplitude K - psi hn K ≤ (r : ℤ) := by
  constructor
  · rintro ⟨a, ha, hr⟩
    have hl := objective_le_ideal_image hn K a ha
    have hr' : normInf (mul (generator hn K) a) ≤ (r : ℤ) := by
      dsimp [normInf]
      exact_mod_cast hr
    exact hl.trans hr'
  · intro hr
    obtain ⟨a, ha, he⟩ := exists_ideal_image_eq hn K
    refine ⟨a, ha, ?_⟩
    have : normInf (mul (generator hn K) a) ≤ (r : ℤ) := by rwa [he]
    dsimp [normInf] at this
    exact_mod_cast this

end Power2IdealSVP.Ideal
