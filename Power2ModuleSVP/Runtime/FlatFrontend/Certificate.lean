import Power2ModuleSVP.Runtime.FlatFrontend.Parameters
import Power2ModuleSVP.Runtime.FlatFrontend.Words
import Power2ModuleSVP.Runtime.FlatFrontend.Chebyshev
import Power2ModuleSVP.Runtime.FlatFrontend.Scan

/-!
# Certificate

Native runtime for the concrete rational frontend, including malformed
inputs. No geometric promise or coloring correctness premise is used.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP.FlatFrontend
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
open ColoringRuntime
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
attribute [local irreducible] List.getD rsWords stage stageIndex blockShift stageWidth
  stablePrefix cosineSelected cosineCoefficient background gridRatio gridSize height
  precision taylorOrder phase expTaylor cosTaylor piTaylor sqrtApprox chebyshevPair
  clamp gridSample cosinePolynomialValue markedCell scanCells intervals kernelEntry
  fractionalCoefficient derivativeEntry intervalInput coefficientInput

/-- Casting a unary natural number to a rational is computable in polynomial time. -/
@[fun_prop] theorem unaryNatCast_polytime : ComputableTidilyInPolyTime
    (fun n : ℕ => (n : ℚ)) encUnary encColoringRational :=
  natCast_polytime.comp unary_to_binary

private theorem cosineTests_polytime :
    ComputableTidilyInPolyTime (fun a : ℕ × ℕ => decide
      (blockShift a.1 ≤ a.2 ∧ a.2 < blockShift a.1 + 2 ^ stage a.1))
      (encPair encUnary encUnary) encBool ∧
    ComputableTidilyInPolyTime (fun a : ℕ × ℕ => decide
      (2 * blockShift a.1 ≤ a.2 ∧ a.2 < 2 * blockShift a.1 + 2 ^ stage a.1))
      (encPair encUnary encUnary) encBool := by
  have hT := blockShift_unary_polytime.comp (fst encUnary encUnary)
  have hm := stagePower_unary_polytime.comp (fst encUnary encUnary)
  have hj := snd encUnary encUnary
  have hT₂ := unary_mul.comp ((const 2).prod hT)
  constructor
  · exact (bool_and.comp ((unary_le.comp (hT.prod hj)).prod
      (unary_lt.comp (hj.prod (unary_add.comp (hT.prod hm)))))).of_enc_eq
      (fun a => congrArg encBool (by simp))
  · exact (bool_and.comp ((unary_le.comp (hT₂.prod hj)).prod
      (unary_lt.comp (hj.prod (unary_add.comp (hT₂.prod hm)))))).of_enc_eq
      (fun a => congrArg encBool (by simp))

/-- The `cosineSelected` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem cosineSelected_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × ℕ => cosineSelected a.1 a.2)
    (encPair encUnary encUnary) encBool := by
  exact (bool_or.comp (cosineTests_polytime.1.prod cosineTests_polytime.2)).of_enc_eq
    (fun a => congrArg encBool (by simp [cosineSelected]))

/-- The `cosineCoefficient` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem cosineCoefficient_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × ℕ => cosineCoefficient a.1 a.2)
    (encPair encUnary encUnary) encIntBin := by
  have he₁ : ComputableTidilyInPolyTime (fun a : ℕ × ℕ =>
      (rsWords (stage a.1)).1.getD (a.2 - blockShift a.1) 0)
      (encPair encUnary encUnary) encIntBin := by
    exact rsWordEntry_polytime.fst'.comp
      (g := fun a : ℕ × ℕ => (stage a.1, a.2 - blockShift a.1)) (by fun_prop)
  have he₂ : ComputableTidilyInPolyTime (fun a : ℕ × ℕ =>
      (rsWords (stage a.1)).2.getD (a.2 - 2 * blockShift a.1) 0)
      (encPair encUnary encUnary) encIntBin := by
    exact rsWordEntry_polytime.snd'.comp
      (g := fun a : ℕ × ℕ => (stage a.1, a.2 - 2 * blockShift a.1)) (by fun_prop)
  exact (cosineTests_polytime.1.ite_decide he₁
    (cosineTests_polytime.2.ite_decide he₂ (const 0))).of_enc_eq
      (fun a => congrArg encIntBin (by unfold cosineCoefficient; rfl))

/-- The `background` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem background_polytime : ComputableTidilyInPolyTime background
    encUnary (encList encIntBin) := by
  unfold background
  apply mapWithInput (range)
  fun_prop

/-- The `clamp` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem clamp_polytime : ComputableTidilyInPolyTime
    (fun a : ℚ × (ℚ × ℚ) => clamp a.1 a.2.1 a.2.2)
    (encPair encColoringRational (encPair encColoringRational encColoringRational))
    encColoringRational := by
  simp only [clamp, max_def, min_def]
  fun_prop

/-- The `gridSize` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem gridSize_polytime : ComputableTidilyInPolyTime gridSize
    encUnary encUnary := by unfold gridSize; fun_prop

/-- The `gridSample` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem gridSample_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × ℕ => gridSample a.1 a.2)
    (encPair encUnary encUnary) encColoringRational := by
  have hN := fst encUnary encUnary
  have hM := gridSize_polytime.comp hN
  have hc : ComputableTidilyInPolyTime (fun a : ℕ × ℕ => decide (2 * a.2 < gridSize a.1))
      (encPair encUnary encUnary) encBool := by fun_prop
  have hs := hc.ite_decide (snd encUnary encUnary)
    (unary_sub.comp (hM.prod (snd _ _)))
  have harg := div_polytime' (mul_polytime' (unaryNatCast_polytime.comp hs)
    (piTaylor_polytime.comp (frontendPrecision_polytime.comp hN)))
    (unaryNatCast_polytime.comp hM)
  have hy := clamp_polytime.comp ((const 0).prod ((const 1).prod
    (cosTaylor_polytime.comp ((taylorOrder_polytime.comp hN).prod harg))))
  have hz : ComputableTidilyInPolyTime (fun a : ℕ × ℕ => decide (a.2 = 0))
      (encPair encUnary encUnary) encBool := by fun_prop
  have he : ComputableTidilyInPolyTime (fun a : ℕ × ℕ => decide (gridSize a.1 ≤ a.2))
      (encPair encUnary encUnary) encBool := by fun_prop
  have hm : ComputableTidilyInPolyTime (fun a : ℕ × ℕ => decide (2 * a.2 = gridSize a.1))
      (encPair encUnary encUnary) encBool := by fun_prop
  exact (hz.ite_decide (const 1) (he.ite_decide (const (-1))
    (hm.ite_decide (const 0) (hc.ite_decide hy (neg_polytime.comp hy))))).of_enc_eq
    (fun a => congrArg encColoringRational (by unfold gridSample; rfl))

/-- The `cosinePolynomialValue` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem cosinePolynomialValue_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × ℚ => cosinePolynomialValue a.1 a.2)
    (encPair encUnary encColoringRational) encColoringRational := by
  unfold cosinePolynomialValue
  apply sum_polytime.comp
  apply mapWithInput (range.comp (fst encUnary encColoringRational))
  fun_prop

/-- Rational absolute value is computable in polynomial time. -/
@[fun_prop] theorem rationalAbs_polytime : ComputableTidilyInPolyTime
    (fun q : ℚ => |q|) encColoringRational encColoringRational := by
  have h : ComputableTidilyInPolyTime (fun q : ℚ => if q < 0 then -q else q)
      encColoringRational encColoringRational :=
    (lt_polytime.comp (id'.prod (const 0))).ite_decide neg_polytime id'
  exact h.of_enc_eq fun q => congrArg _ (by
    by_cases hq : q < 0
    · simp [hq, abs_of_neg hq]
    · simp [hq, abs_of_nonneg (le_of_not_gt hq)])

/-- The `markedCell` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem markedCell_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × ℕ => markedCell a.1 a.2)
    (encPair encUnary encUnary) encBool := by
  have hidx : ComputableTidilyInPolyTime (fun a : (ℕ × ℕ) × ℕ =>
      (a.1.1, a.1.2 * gridRatio a.1.1 + a.2))
      (encPair (encPair encUnary encUnary) encUnary) (encPair encUnary encUnary) := by
    fun_prop
  have hN := (fst encUnary encUnary).comp (fst (encPair encUnary encUnary) encUnary)
  have hv := cosinePolynomialValue_polytime.comp (hN.prod (gridSample_polytime.comp hidx))
  have hh : ComputableTidilyInPolyTime (fun a : (ℕ × ℕ) × ℕ => 3 * height a.1.1 / 4)
      (encPair (encPair encUnary encUnary) encUnary) encColoringRational := by fun_prop
  have hp : ComputableTidilyInPolyTime (fun a : (ℕ × ℕ) × ℕ => decide
      (|cosinePolynomialValue a.1.1 (gridSample a.1.1 (a.1.2 * gridRatio a.1.1 + a.2))| ≤
        3 * height a.1.1 / 4))
      (encPair (encPair encUnary encUnary) encUnary) encBool :=
    (le_polytime.comp ((rationalAbs_polytime.comp hv).prod hh)).of_enc_eq (fun _ => rfl)
  have hl : ComputableTidilyInPolyTime (fun a : ℕ × ℕ => List.range (gridRatio a.1 + 1))
      (encPair encUnary encUnary) (encList encUnary) := by fun_prop
  exact (anyWithInput hl hp).of_enc_eq
    (fun a => congrArg encBool (by unfold markedCell; rfl))

/-- The `intervals` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem intervals_polytime : ComputableTidilyInPolyTime intervals
    encUnary (encList encRun) := by
  unfold intervals
  apply scanCells_polytime.comp
  apply mapWithInput (by fun_prop)
  exact markedCell_polytime

/-- Encoding of the degree, run endpoints, and kernel index. -/
abbrev encKernel := encPair encUnary (encPair encRun encUnary)
/-- The `kernelEntry` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem kernelEntry_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × ((ℕ × ℕ) × ℕ) => kernelEntry a.1 a.2.1 a.2.2)
    encKernel encColoringRational := by
  have ha : ComputableTidilyInPolyTime (fun a : ℕ × ((ℕ × ℕ) × ℕ) =>
      cosTaylor (taylorOrder a.1)
        ((((2 * a.2.2 + 1) * a.2.1.1 : ℕ) : ℚ) * piTaylor (precision a.1) / a.1))
      encKernel encColoringRational := by unfold encKernel encRun; fun_prop
  have hb : ComputableTidilyInPolyTime (fun a : ℕ × ((ℕ × ℕ) × ℕ) =>
      cosTaylor (taylorOrder a.1)
        ((((2 * a.2.2 + 1) * a.2.1.2 : ℕ) : ℚ) * piTaylor (precision a.1) / a.1))
      encKernel encColoringRational := by unfold encKernel encRun; fun_prop
  have hN : ComputableTidilyInPolyTime (fun a : ℕ × ((ℕ × ℕ) × ℕ) => a.1)
      encKernel encUnary := fst _ _
  have hs := sqrtApprox_polytime.comp ((frontendPrecision_polytime.comp hN).prod hN)
  have hm : ComputableTidilyInPolyTime (fun a : ℕ × ((ℕ × ℕ) × ℕ) => (2 * a.2.2 + 1 : ℕ))
      encKernel encUnary := by unfold encKernel; fun_prop
  exact (div_polytime' (mul_polytime' (mul_polytime' (const 36000) hs)
    (sub_polytime.comp (ha.prod hb))) (unaryNatCast_polytime.comp hm)).of_enc_eq
    (fun a => congrArg encColoringRational (by unfold kernelEntry; rfl))

/-- The `intervalInput` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem intervalInput_polytime : ComputableTidilyInPolyTime intervalInput
    encUnary encPartialColoring := by
  unfold intervalInput encPartialColoring
  fun_prop

/-- Encoding of the degree and indices for a fractional coefficient. -/
abbrev encFractional := encPair encUnary
  (encPair (encList encRun) (encPair (encList encColoringRational) encUnary))
/-- The `fractionalCoefficient` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem fractionalCoefficient_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × (List (ℕ × ℕ) × (List ℚ × ℕ)) =>
      fractionalCoefficient a.1 a.2.1 a.2.2.1 a.2.2.2)
    encFractional encColoringRational := by
  unfold fractionalCoefficient
  apply sum_polytime.comp
  apply mapWithInput (by unfold encFractional; fun_prop)
  unfold encFractional encRun
  fun_prop

/-- Unary encoding of the four derivative-entry parameters. -/
abbrev encDerivative := encPair encUnary (encPair encUnary (encPair encUnary encUnary))
/-- The `derivativeEntry` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem derivativeEntry_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × (ℕ × (ℕ × ℕ)) => derivativeEntry a.1 a.2.1 a.2.2.1 a.2.2.2)
    encDerivative encColoringRational := by
  have hN : ComputableTidilyInPolyTime (fun a : ℕ × (ℕ × (ℕ × ℕ)) => a.1)
      encDerivative encUnary := fst _ _
  have hnum : ComputableTidilyInPolyTime (fun a : ℕ × (ℕ × (ℕ × ℕ)) =>
      (2 * a.2.2.2 + 1) * (2 * a.2.1 + 1)) encDerivative encUnary := by
    unfold encDerivative; fun_prop
  have hq := div_polytime' (mul_polytime' (unaryNatCast_polytime.comp hnum)
    (piTaylor_polytime.comp (frontendPrecision_polytime.comp hN)))
    (mul_polytime' (const 64) (unaryNatCast_polytime.comp hN))
  have ht := expTaylor_polytime.comp ((taylorOrder_polytime.comp hN).prod hq)
  have hm : ComputableTidilyInPolyTime (fun a : ℕ × (ℕ × (ℕ × ℕ)) =>
      2 * a.2.2.2 + 1) encDerivative encUnary := by unfold encDerivative; fun_prop
  have hden : ComputableTidilyInPolyTime (fun a : ℕ × (ℕ × (ℕ × ℕ)) =>
      2 * a.1) encDerivative encUnary := by unfold encDerivative; fun_prop
  have hell : ComputableTidilyInPolyTime (fun a : ℕ × (ℕ × (ℕ × ℕ)) => a.2.2.1)
      encDerivative encUnary := by unfold encDerivative; fun_prop
  have hph := phase_polytime.comp hell
  have hscale := pow_polytime' (div_polytime' (unaryNatCast_polytime.comp hm)
    (unaryNatCast_polytime.comp hden)) hell
  exact (mul_polytime' hscale (add_polytime' (mul_polytime' hph.fst' ht.snd')
    (mul_polytime' hph.snd' ht.fst'))).of_enc_eq
    (fun a => congrArg encColoringRational (by unfold derivativeEntry; rfl))

/-- The `coefficientInput` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem coefficientInput_polytime : ComputableTidilyInPolyTime coefficientInput
    encSeedSecondInput encPartialColoring := by
  unfold coefficientInput encSeedSecondInput encPartialColoring
  fun_prop

/-- A native rational certificate bounds both canonical components, rather
than merely the absolute value of the represented number. -/
theorem rationalBits_polyBounded_of {α : Type} {enc : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableTidilyInPolyTime f enc encColoringRational) :
    PolyBounded (fun a => (enc a).length)
      (fun a => ColoringRuntime.rationalBits (f a)) := by
  apply hf.polyBounded_length.mono
  intro a
  simp only [ColoringRuntime.rationalBits, encColoringRational,
    Function.Embedding.coeFn_mk, length_encPair, length_encIntBin,
    encNat_apply, ← Nat.size_eq_bits_len]
  omega

/-- Kernel entries have polynomially bounded canonical numerator and denominator bit lengths. -/
theorem kernelEntry_bits_polyBounded :
    PolyBounded (fun a => (encKernel a).length)
      (fun a => ColoringRuntime.rationalBits (kernelEntry a.1 a.2.1 a.2.2)) :=
  rationalBits_polyBounded_of kernelEntry_polytime

/-- Derivative entries have polynomially bounded rational component bit lengths. -/
theorem derivativeEntry_bits_polyBounded :
    PolyBounded (fun a => (encDerivative a).length)
      (fun a => ColoringRuntime.rationalBits
        (derivativeEntry a.1 a.2.1 a.2.2.1 a.2.2.2)) :=
  rationalBits_polyBounded_of derivativeEntry_polytime

/-- Square-root approximations have polynomially bounded rational component bit lengths. -/
theorem sqrtApprox_bits_polyBounded :
    PolyBounded (fun a : ℕ × ℕ => (encPair encUnary encUnary a).length)
      (fun a => ColoringRuntime.rationalBits (sqrtApprox a.1 a.2)) :=
  rationalBits_polyBounded_of sqrtApprox_polytime

theorem taylor_bits_polyBounded :
    PolyBounded (fun a : ℕ × ℚ => (encPair encUnary encColoringRational a).length)
      (fun a => ColoringRuntime.rationalBits (expTaylor a.1 a.2).1 +
        ColoringRuntime.rationalBits (expTaylor a.1 a.2).2) :=
  (rationalBits_polyBounded_of expTaylor_polytime.fst').add
    (rationalBits_polyBounded_of expTaylor_polytime.snd')

/-- Chebyshev recurrence outputs have polynomially bounded rational component bit lengths. -/
theorem chebyshev_bits_polyBounded :
    PolyBounded (fun a : ℕ × ℚ => (encPair encUnary encColoringRational a).length)
      (fun a => ColoringRuntime.rationalBits (chebyshevPair a.1 a.2).1 +
        ColoringRuntime.rationalBits (chebyshevPair a.1 a.2).2) :=
  (rationalBits_polyBounded_of chebyshevPair_polytime.fst').add
    (rationalBits_polyBounded_of chebyshevPair_polytime.snd')

end Power2ModuleSVP.FlatFrontend
namespace Power2ModuleSVP
/-- The three actual frontend programs, on all raw inputs, have native
multitape polynomial-time certificates. -/
theorem flatFrontend_runtime : FlatSeedFrontendRuntimeHypothesis flatFrontend where
  background := FlatFrontend.background_polytime
  intervals := FlatFrontend.intervalInput_polytime
  coefficients := FlatFrontend.coefficientInput_polytime
end Power2ModuleSVP
