import Power2ModuleSVP.Anchor.Repair
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log

/-!
# Repair parameter runtime certificates

Native-machine certificates for repair parameters and bounded arithmetic. Candidate, row,
potential, and loop certificates are assembled in the other Runtime/Repair modules.

Paper: `paper/power2svp.pdf`, Section 5 (Theorems 3–4 and deterministic anchor repair).
-/
namespace Power2ModuleSVP
namespace AnchorRepairRuntime
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

set_option maxRecDepth 4096
set_option exponentiation.threshold 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] List.getD

@[fun_prop] theorem log2_polytime :
    ComputableTidilyInPolyTime Nat.log2 encUnary encUnary := by
  have he : Nat.log2 = Nat.log 2 := funext fun _ => Nat.log2_eq_log_two
  rw [he]
  exact unary_log_two

@[fun_prop] theorem flipBudget_polytime :
    ComputableTidilyInPolyTime AnchorRepair.flipBudget encUnary encUnary := by
  unfold AnchorRepair.flipBudget
  fun_prop

/-- Explicit list implementation of applying an exposed flag word. -/
def applyFlags (a : ℕ × (List ℤ × List Bool)) : List ℤ :=
  (List.range a.1).map fun i =>
    if a.2.2.getD i false then -a.2.1.getD i 0 else a.2.1.getD i 0

abbrev encFlagsInput := encPair encUnary (encPair (encList encIntBin) (encList encBool))

@[fun_prop] theorem applyFlags_polytime :
    ComputableTidilyInPolyTime applyFlags encFlagsInput (encList encIntBin) := by
  unfold applyFlags
  apply mapWithInput (encA := encUnary)
  · unfold encFlagsInput
    fun_prop
  · unfold encFlagsInput
    fun_prop

theorem applyFlags_eq (d : ℕ) (s : List ℤ) (σ : List Bool) :
    applyFlags (d, (s, σ)) = IdealCVP.toList (AnchorRepair.flipped d s σ) := by
  apply List.ext_getElem
  · simp [applyFlags, IdealCVP.toList]
  · intro n hn hm
    simp [applyFlags, IdealCVP.toList, AnchorRepair.flipped, IdealCVP.ofList]

/-- Unnormalised signed-binary fractions. Positive denominators are the
invariant; no gcd computation or rational oracle is needed for these primitives. -/
abbrev Fraction := ℤ × ℤ
abbrev encFraction := encPair encIntBin encIntBin

def fractionValue (a : Fraction) : ℚ := (a.1 : ℚ) / (a.2 : ℚ)
def fractionAdd (a : Fraction × Fraction) : Fraction :=
  (a.1.1*a.2.2 + a.2.1*a.1.2, a.1.2*a.2.2)
def fractionMul (a : Fraction × Fraction) : Fraction :=
  (a.1.1*a.2.1, a.1.2*a.2.2)
def fractionLE (a : Fraction × Fraction) : Bool :=
  decide (a.1.1*a.2.2 ≤ a.2.1*a.1.2)

@[fun_prop] theorem fractionAdd_polytime :
    ComputableTidilyInPolyTime fractionAdd (encPair encFraction encFraction) encFraction := by
  unfold fractionAdd encFraction
  fun_prop

@[fun_prop] theorem fractionMul_polytime :
    ComputableTidilyInPolyTime fractionMul (encPair encFraction encFraction) encFraction := by
  unfold fractionMul encFraction
  fun_prop

@[fun_prop] theorem fractionLE_polytime :
    ComputableTidilyInPolyTime fractionLE (encPair encFraction encFraction) encBool := by
  unfold fractionLE encFraction
  fun_prop

theorem fractionAdd_spec (a b : Fraction) (ha : 0 < a.2) (hb : 0 < b.2) :
    0 < (fractionAdd (a,b)).2 ∧
      fractionValue (fractionAdd (a,b)) = fractionValue a + fractionValue b := by
  refine ⟨mul_pos ha hb, ?_⟩
  have ha' : (a.2 : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b.2 : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  unfold fractionAdd fractionValue
  push_cast
  field_simp [ha', hb']

theorem fractionMul_spec (a b : Fraction) (ha : 0 < a.2) (hb : 0 < b.2) :
    0 < (fractionMul (a,b)).2 ∧
      fractionValue (fractionMul (a,b)) = fractionValue a * fractionValue b := by
  refine ⟨mul_pos ha hb, ?_⟩
  simp [fractionMul, fractionValue, div_mul_div_comm]

theorem fractionLE_spec (a b : Fraction) (ha : 0 < a.2) (hb : 0 < b.2) :
    fractionLE (a,b) = true ↔ fractionValue a ≤ fractionValue b := by
  simp only [fractionLE, decide_eq_true_eq, fractionValue]
  have ha' : (0 : ℚ) < a.2 := by exact_mod_cast ha
  have hb' : (0 : ℚ) < b.2 := by exact_mod_cast hb
  rw [div_le_div_iff₀ ha' hb']
  exact_mod_cast Iff.rfl

abbrev encRepairInput := encPair encUnary (encList encIntBin)

/-- The repair composition interface: supplying a native certificate
for the already defined repair program converts the uniform seed family to
the existing uniform anchor interface. The certificate is an explicit premise;
the full repair runtime theorem has not been established in this file. -/
theorem rigidAnchorFamily_of_seed_of_repair_polytime
    (hrepair : ComputableTidilyInPolyTime
      (fun a : ℕ × List ℤ => repair a.1 a.2) encRepairInput (encList encIntBin))
    (hseed : SpectralSeedFamilyHypothesis) : RigidAnchorFamilyHypothesis := by
  obtain ⟨k0, s, htime, hspec⟩ := hseed.exists_family
  refine ⟨max k0 3600, (fun d => repair d (s d)), ?_, ?_⟩
  · exact hrepair.comp (id'.prod htime)
  · intro d hd hlarge
    have hseedlarge : 2^k0 ≤ d :=
      (Nat.pow_le_pow_right (by decide) (le_max_left k0 3600)).trans hlarge
    have hrepairlarge : 2^3600 ≤ d :=
      (Nat.pow_le_pow_right (by decide) (le_max_right k0 3600)).trans hlarge
    have hs := (hspec d hd hseedlarge).2
    exact repair_spec (AnchorRepair.admissible_of_cutoff hd hrepairlarge) (s d) hs

end AnchorRepairRuntime
end Power2ModuleSVP
