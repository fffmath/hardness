import Hardness.Complexity.Problem

/-! # A total executable compiler with a list interface

This reference implementation evaluates the existing finite compiler and lists
its coefficients. It is not yet the independent bounded-search / `countP`
implementation proposed in the research plan. Its runtime certificate is an
explicit hypothesis in `CompilePolyTime.lean`; correctness is unconditional.
-/
namespace Hardness

namespace MaskedSys

/-- Add an independent dummy equation `x₀=1`, ensuring both sizes are positive. -/
def paddedSystem (S : MaskedSys) : MaskedSystem (S.rows.length + 1) (S.cols + 1) where
  A := Fin.cases (Fin.cases true (fun _ => false))
    (fun i => Fin.cases false (fun j => S.toSystem.A i j))
  b := Fin.cases true S.toSystem.b
  μ := Fin.cases true S.toSystem.μ

/-- No choice or oracle is used: positions come from the executable prime search. -/
def reductionData (S : MaskedSys) : ReductionData (S.rows.length + 1) (S.cols + 1) where
  system := S.paddedSystem
  positions := SidonPositions.erdosTuran (S.cols + 1)
  M_pos := Nat.succ_pos _
  n_pos := Nat.succ_pos _

end MaskedSys

/-- Package the existing general compiler output, including its proved promises. -/
def ReductionData.toPrincipalCVPInstance {M n : ℕ} (D : ReductionData M n) :
    PrincipalCVPInstance where
  d := D.d
  power_two := D.d_power_two
  g := D.g
  g_ne_zero := D.g_ne_zero
  T := D.T
  Δ := D.Δ
  Δ_nonneg := by unfold ReductionData.Δ; positivity

/-- A fixed well-formed NO instance, with a negative squared threshold. -/
def cvpNoInput : CVPInput := (1, [0], [0], -1)

/-- Total computable reference compiler. Malformed systems are rejected; all
well-formed systems, including zero rows/columns, use the padded compiler. -/
def compileList (S : MaskedSys) : CVPInput :=
  if S.WellFormed then toCVPInput S.reductionData.toPrincipalCVPInstance else cvpNoInput

end Hardness
