import Power2ModuleSVP.FlatFrontend.Program
import Power2ModuleSVP.Runtime.Seed.Composition
import Power2ModuleSVP.Runtime.Coloring.Initialization

/-!
# Taylor

Native rational Taylor certificates, independent of the frontend's precision policy.
The certified common-denominator list sum accounts for intermediate bit lengths.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP.FlatFrontend
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
open ColoringRuntime
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

private theorem phase_four (n : ℕ) : phase (n + 4) = phase n := by
  simp [phase]

private theorem phase_mod (n : ℕ) : phase n = phase (n % 4) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 4
    · rw [Nat.mod_eq_of_lt hn]
    · have he : n = n - 4 + 4 := by omega
      rw [he, phase_four, ih (n - 4) (by omega)]
      congr 1
      omega

private def phaseSmall (n : ℕ) : ℚ × ℚ :=
  if n = 0 then (1, 0) else if n = 1 then (0, 1)
  else if n = 2 then (-1, 0) else (0, -1)

/-- The `phase` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem phase_polytime : ComputableTidilyInPolyTime phase encUnary
    (encPair encColoringRational encColoringRational) := by
  have h : ComputableTidilyInPolyTime (fun n => phaseSmall (n % 4)) encUnary
      (encPair encColoringRational encColoringRational) := by
    unfold phaseSmall
    fun_prop
  exact h.of_enc_eq fun n => congrArg _ (by
    rw [phase_mod]
    have hn : n % 4 < 4 := Nat.mod_lt _ (by omega)
    interval_cases hq : n % 4 <;> norm_num [phaseSmall, phase])

private theorem expTaylor_sum (n : ℕ) (q : ℚ) :
    expTaylor n q =
      (((List.range n).map fun k => q ^ k / (k.factorial : ℚ) * (phase k).1).sum,
       ((List.range n).map fun k => q ^ k / (k.factorial : ℚ) * (phase k).2).sum) := by
  induction n with
  | zero => simp [expTaylor]
  | succ n ih => simp [expTaylor, ih, List.range_succ]

/-- The `expTaylor` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem expTaylor_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × ℚ => expTaylor a.1 a.2)
    (encPair encUnary encColoringRational)
    (encPair encColoringRational encColoringRational) := by
  have hterm : ComputableTidilyInPolyTime
      (fun a : (ℕ × ℚ) × ℕ => a.1.2 ^ a.2 / (a.2.factorial : ℚ))
      (encPair (encPair encUnary encColoringRational) encUnary) encColoringRational := by
    apply div_polytime'
      (pow_polytime' ((snd encUnary encColoringRational).comp (fst _ _)) (snd _ _))
    exact natCast_polytime.comp (factorial_polytime.comp (snd _ _))
  have hp : ComputableTidilyInPolyTime (fun a : (ℕ × ℚ) × ℕ => phase a.2)
      (encPair (encPair encUnary encColoringRational) encUnary)
      (encPair encColoringRational encColoringRational) := by fun_prop
  have h₁ : ComputableTidilyInPolyTime (fun a : ℕ × ℚ =>
      ((List.range a.1).map fun k => a.2 ^ k / (k.factorial : ℚ) * (phase k).1).sum)
      (encPair encUnary encColoringRational) encColoringRational :=
    sum_polytime.comp (mapWithInput (range.comp (fst encUnary encColoringRational))
      (mul_polytime' hterm hp.fst'))
  have h₂ : ComputableTidilyInPolyTime (fun a : ℕ × ℚ =>
      ((List.range a.1).map fun k => a.2 ^ k / (k.factorial : ℚ) * (phase k).2).sum)
      (encPair encUnary encColoringRational) encColoringRational :=
    sum_polytime.comp (mapWithInput (range.comp (fst encUnary encColoringRational))
      (mul_polytime' hterm hp.snd'))
  exact (h₁.prod h₂).of_enc_eq fun a => congrArg _ (expTaylor_sum a.1 a.2)

/-- The `cosTaylor` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem cosTaylor_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × ℚ => cosTaylor a.1 a.2)
    (encPair encUnary encColoringRational) encColoringRational := expTaylor_polytime.fst'

/-- The `arctanTaylor` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem arctanTaylor_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × ℚ => arctanTaylor a.1 a.2)
    (encPair encUnary encColoringRational) encColoringRational := by
  unfold arctanTaylor
  apply sum_polytime.comp
  apply mapWithInput (range.comp (fst encUnary encColoringRational))
  fun_prop

/-- The `piTaylor` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem piTaylor_polytime : ComputableTidilyInPolyTime piTaylor
    encUnary encColoringRational := by
  unfold piTaylor
  fun_prop

/-- The frontend precision parameter is computable in unary within polynomial time. -/
@[fun_prop] theorem frontendPrecision_polytime : ComputableTidilyInPolyTime precision
    encUnary encUnary := by
  unfold precision
  fun_prop

/-- The `taylorOrder` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem taylorOrder_polytime : ComputableTidilyInPolyTime taylorOrder
    encUnary encUnary := by
  unfold taylorOrder
  fun_prop

/-- The `sqrtApprox` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem sqrtApprox_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × ℕ => sqrtApprox a.1 a.2)
    (encPair encUnary encUnary) encColoringRational := by
  unfold sqrtApprox
  fun_prop

end Power2ModuleSVP.FlatFrontend
