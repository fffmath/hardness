import Power2ModuleSVP.RepairRuntimePotential

/-! A native polynomial-time implementation equal to the original total repair. -/
namespace Power2ModuleSVP.AnchorRepairRuntime
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] List.getD potentialFraction

def nextFlagFast (a : PotentialInput) : Bool :=
  if fractionLE (potentialFraction (a.1,a.2++[false]),
      potentialFraction (a.1,a.2++[true])) then false else true

attribute [local irreducible] nextFlagFast

@[fun_prop] theorem nextFlagFast_polytime :
    ComputableTidilyInPolyTime nextFlagFast encPotentialInput encBool := by
  unfold nextFlagFast
  have ht : ComputableTidilyInPolyTime (fun a : PotentialInput =>
      fractionLE (potentialFraction (a.1,a.2++[false]),
        potentialFraction (a.1,a.2++[true]))) encPotentialInput encBool := by
    apply fractionLE_polytime.comp
    apply ComputableTidilyInPolyTime.prod
    · apply potentialFraction_polytime.comp
      unfold encPotentialInput
      fun_prop
    · apply potentialFraction_polytime.comp
      unfold encPotentialInput
      fun_prop
  exact ht.ite' (const false) (const true)

theorem nextFlagFast_eq (a : PotentialInput) :
    nextFlagFast a = AnchorRepair.nextFlag (AnchorRepair.potential a.1.1 a.1.2) a.2 := by
  have h0 := potentialFraction_spec (a.1,a.2++[false])
  have h1 := potentialFraction_spec (a.1,a.2++[true])
  have hle := fractionLE_spec _ _ h0.1 h1.1
  rw [h0.2,h1.2] at hle
  unfold nextFlagFast AnchorRepair.nextFlag
  simp only [hle]

def flagStep (a : ℕ × List ℤ) (pre : List Bool) : List Bool :=
  pre ++ [nextFlagFast (a,pre)]

def flagsFast (a : ℕ × List ℤ) : List Bool := (flagStep a)^[a.1] []

@[fun_prop] theorem flagStep_polytime : ComputableTidilyInPolyTime
    (fun a : PotentialInput => flagStep a.1 a.2) encPotentialInput (encList encBool) := by
  unfold flagStep
  have hn := nextFlagFast_polytime
  unfold encPotentialInput at *
  fun_prop

@[fun_prop] theorem flagsFast_polytime :
    ComputableTidilyInPolyTime flagsFast encRepairInput (encList encBool) := by
  unfold flagsFast
  apply iterateWith_of_bounded_growth (encPar := encRepairInput)
    (growth := fun _ => 3) id'
    (by unfold encRepairInput; fun_prop) (const []) flagStep_polytime (.const 3)
  intro a pre
  simp [flagStep, encList_append, encList_cons]

theorem minimize_eq_iterate (F : List Bool → ℚ) (n : ℕ) (pre : List Bool) :
    AnchorRepair.minimize F n pre =
      (fun σ => σ ++ [AnchorRepair.nextFlag F σ])^[n] pre := by
  induction n generalizing pre with
  | zero => rfl
  | succ n ih => rw [AnchorRepair.minimize, ih, Function.iterate_succ_apply]

theorem flagsFast_eq (a : ℕ × List ℤ) : flagsFast a = AnchorRepair.repairFlags a.1 a.2 := by
  unfold flagsFast AnchorRepair.repairFlags
  rw [minimize_eq_iterate]
  have he : flagStep a = fun σ =>
      σ ++ [AnchorRepair.nextFlag (AnchorRepair.potential a.1 a.2) σ] := by
    funext σ
    simp only [flagStep,nextFlagFast_eq]
  rw [he]

/-- The optimized program is total, including arbitrary coefficients and zero degree. -/
def repairFast (a : ℕ × List ℤ) : List ℤ :=
  applyFlags (a.1,(a.2,flagsFast a))

@[fun_prop] theorem repairFast_polytime :
    ComputableTidilyInPolyTime repairFast encRepairInput (encList encIntBin) := by
  unfold repairFast
  apply applyFlags_polytime.comp
  unfold encFlagsInput encRepairInput
  fun_prop

theorem repairFast_eq : repairFast = fun a : ℕ × List ℤ => repair a.1 a.2 := by
  funext a
  rw [repairFast,flagsFast_eq,applyFlags_eq]
  rfl

/-- One uniform native multitape machine and one fixed polynomial, for all
raw input pairs. All rational evaluation is replaced by exact fractions. -/
@[fun_prop] theorem repair_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × List ℤ => repair a.1 a.2) encRepairInput (encList encIntBin) := by
  rw [← repairFast_eq]
  exact repairFast_polytime

end Power2ModuleSVP.AnchorRepairRuntime
