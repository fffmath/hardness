import Power2IdealSVP.Ideal.Minimum
import Power2IdealSVP.Ideal.Theta

/-!
# Principal ideal construction and its additive gap

All constants in Section 1.5 are explicit functions of an arbitrary multiplier `G` and
an integer threshold `τ`. Only clock domination needs the elementary hypothesis `0 ≤ τ`.
The equalities hold on both sides of the threshold, without a promise on `thetaOf G`.

Paper: `paper/power2-ideal-svp.pdf`, Section 1.5, equations (2) and (3).
-/

namespace Power2IdealSVP.Ideal
open Power2ModuleSVP IdealCVP.Cyclotomic Power2IdealSVP.Algebra

/-- The perturbation `H = G(1-X)`. -/
def perturbation {n : ℕ} (hn : 0 < n) (G : Coeff n) : Coeff n := mul G (difference hn)

/-- The perturbation one norm `R_H`. -/
def perturbationNorm {n : ℕ} (hn : 0 < n) (G : Coeff n) : ℤ := coeffL1 (perturbation hn G)

/-- The clock amplitude `B = R_H + 2τ + 1`. -/
def clockAmplitude {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) : ℤ :=
  perturbationNorm hn G + 2 * τ + 1

/-- The multiplier `K = BX + H`. -/
def constructedK {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) : Coeff n :=
  clockMultiplier hn G (clockAmplitude hn G τ)

/-- The clock multiplier one norm `R_K`. -/
def clockNorm {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) : ℤ :=
  coeffL1 (constructedK hn G τ)

/-- The scalar `M = 3 R_K + 1`. -/
def constructedM {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) : ℤ :=
  amplitude (constructedK hn G τ)

/-- The final generator `f = (M-K)S`. -/
def constructedF {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) : Coeff n :=
  generator hn (constructedK hn G τ)

/-- The integer radius `r = M+B-2τ`. -/
def radius {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) : ℤ :=
  constructedM hn G τ + clockAmplitude hn G τ - 2 * τ

/-- The chosen clock strictly dominates the perturbation. -/
theorem clock_dominates {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) (hτ : 0 ≤ τ) :
    coeffL1 (mul G (difference hn)) < clockAmplitude hn G τ := by
  dsimp [clockAmplitude, perturbationNorm, perturbation]
  omega

/-- Equation (2) with all construction constants substituted. -/
theorem psi_constructedK {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) (hτ : 0 ≤ τ) :
    psi hn (constructedK hn G τ) = -clockAmplitude hn G τ + 2 * thetaOf hn G :=
  psi_clock_eq hn G _ (clock_dominates hn G τ hτ)

/-- Equation (3) for every multiplier `G`, without a threshold promise. -/
theorem lambdaInf_constructedF {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ)
    (hτ : 0 ≤ τ) :
    (lambdaInf (constructedF hn G τ) : ℤ) =
      constructedM hn G τ + clockAmplitude hn G τ - 2 * thetaOf hn G := by
  rw [constructedF, lambdaInf_generator, psi_constructedK hn G τ hτ]
  dsimp [constructedM]
  ring

/-- Domination proves nonzeroness without irreducibility or a threshold promise. -/
theorem constructedF_ne_zero {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) :
    constructedF hn G τ ≠ 0 := generator_ne_zero hn _

/-- Cancellation of the threshold terms gives `r = M + R_H + 1`. -/
theorem radius_eq {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) :
    radius hn G τ = constructedM hn G τ + perturbationNorm hn G + 1 := by
  dsimp [radius, clockAmplitude]
  ring

/-- The output radius is at least one for every integer threshold. -/
theorem radius_pos {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) : 1 ≤ radius hn G τ := by
  rw [radius_eq]
  have hH := coeffL1_nonneg (perturbation hn G)
  have hK := coeffL1_nonneg (constructedK hn G τ)
  dsimp [constructedM, amplitude, perturbationNorm]
  omega

/-- The natural radius in the fixed decision-language interface has the specified value. -/
theorem radius_natCast {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) :
    ((radius hn G τ).toNat : ℤ) = radius hn G τ :=
  Int.toNat_of_nonneg (by have := radius_pos hn G τ; omega)

/-- The exact decision equivalence from sparse spins to a nonzero principal ideal vector. -/
theorem idealYes_constructedF_iff {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ)
    (hτ : 0 ≤ τ) :
    IdealYes (constructedF hn G τ) (radius hn G τ).toNat ↔ τ ≤ thetaOf hn G := by
  rw [constructedF, idealYes_generator_iff, psi_constructedK hn G τ hτ,
    radius_natCast]
  dsimp [radius, constructedM]
  omega

/-- A NO threshold instance has the exact additive gap of two. -/
theorem no_gap {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) (hτ : 0 ≤ τ)
    (hno : thetaOf hn G < τ) :
    radius hn G τ + 2 ≤ (lambdaInf (constructedF hn G τ) : ℤ) := by
  rw [lambdaInf_constructedF hn G τ hτ]
  dsimp [radius]
  omega

/-- The additive NO gap bounds every nonzero output ideal vector. -/
theorem no_gap_vector {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) (hτ : 0 ≤ τ)
    (hno : thetaOf hn G < τ) (a : Coeff n) (ha : mul (constructedF hn G τ) a ≠ 0) :
    radius hn G τ + 2 ≤ normInf (mul (constructedF hn G τ) a) := by
  have hl := objective_le_ideal_image hn (constructedK hn G τ) a ha
  rw [psi_constructedK hn G τ hτ] at hl
  change radius hn G τ + 2 ≤ normInf (mul (generator hn (constructedK hn G τ)) a)
  dsimp [radius, constructedM]
  omega

/-- The coefficient-list target instance, without runtime certificates. -/
def outputInput {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) : IdealInput :=
  (n, IdealCVP.toList (constructedF hn G τ), (radius hn G τ).toNat)

/-- Dyadic degree is the only additional condition for a well-formed target instance. -/
theorem outputInput_wellFormed {n : ℕ} (hn : 0 < n) (hd : Dyadic n)
    (G : Coeff n) (τ : ℤ) : IdealInput.WellFormed (outputInput hn G τ) := by
  exact ⟨hd, IdealCVP.length_toList _, by
    change IdealCVP.ofList (d := n) (IdealCVP.toList (constructedF hn G τ)) ≠ 0
    rw [IdealCVP.ofList_toList]
    exact constructedF_ne_zero hn G τ⟩

/-- The fixed target language accepts exactly when the sparse threshold is attained. -/
theorem outputInput_mem_iff {n : ℕ} (hn : 0 < n) (hd : Dyadic n)
    (G : Coeff n) (τ : ℤ) (hτ : 0 ≤ τ) :
    outputInput hn G τ ∈ IdealSVPLang ↔ τ ≤ thetaOf hn G := by
  change IdealInput.WellFormed (outputInput hn G τ) ∧
    IdealYes (IdealCVP.ofList (d := n) (IdealCVP.toList (constructedF hn G τ)))
      (radius hn G τ).toNat ↔ _
  rw [IdealCVP.ofList_toList,
    and_iff_right (outputInput_wellFormed hn hd G τ), idealYes_constructedF_iff hn G τ hτ]

/-- The efficient direct formula `f = (M-B)S + 2B - 2G`. -/
theorem constructedF_explicit {n : ℕ} (hn : 0 < n) (G : Coeff n) (τ : ℤ) :
    constructedF hn G τ =
      (constructedM hn G τ - clockAmplitude hn G τ) • sumPoly n +
        (2 * clockAmplitude hn G τ) • coeffOne hn - (2 : ℤ) • G := by
  have hH : mul (mul G (difference hn)) (sumPoly n) = (2 : ℤ) • G := by
    rw [coeff_mul_assoc hn, difference_sumPoly, mul_smul_right, mul_coeffOne_right]
  dsimp [constructedF, generator, constructedK, clockMultiplier]
  rw [coeff_mul_sub_left, mul_smul_left, mul_coeffOne, mul_add_left,
    mul_smul_left, xPoly_sumPoly, hH]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, constructedM]
  dsimp [constructedK, clockMultiplier]
  ring

end Power2IdealSVP.Ideal
