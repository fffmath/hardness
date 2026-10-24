import IdealCVP.Main
import Complexity.Computability.Complexity.Problems.ExactThreeSAT
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
import Mathlib.Data.List.OfFn

/-! # Finite binary-data decision problems

Dimensions and column counts are unary. Coefficients and thresholds are signed
binary integers. Ill-formed inputs are NO instances; zero generators are allowed.
-/
namespace IdealCVP
open Turing.MultiTapeTM

/-- Total coefficient lookup, padded by zero. -/
def ofList {α : Type} [Zero α] {d : ℕ} (l : List α) : Fin d → α :=
  fun i => l.getD i.val 0

/-- Coefficients in increasing order. -/
def toList {α : Type} {d : ℕ} (v : Fin d → α) : List α := List.ofFn v

@[simp] theorem length_toList {α : Type} {d : ℕ} (v : Fin d → α) :
    (toList v).length = d := List.length_ofFn

@[simp] theorem ofList_toList {α : Type} [Zero α] {d : ℕ} (v : Fin d → α) :
    ofList (toList v) = v := by
  funext i
  simp [ofList, toList, List.getD_eq_getElem?_getD, i.isLt]

@[simp] theorem toList_ofList {α : Type} [Zero α] (l : List α) :
    toList (ofList (d := l.length) l) = l := by
  calc
    _ = List.ofFn l.get := by
      congr 1
      funext i
      simp [ofList, List.getD_eq_getElem?_getD]
    _ = l := List.ofFn_get l

/-- `(d,g,T,Δ)`, without proof fields. -/
abbrev CVPInput := ℕ × (List ℤ × (List ℤ × ℤ))

def encCVP : CVPInput ↪ List Bool :=
  encPair encUnary (encPair (encList encIntBin) (encPair (encList encIntBin) encIntBin))

namespace CVPInput

def WellFormed (x : CVPInput) : Prop :=
  (∃ k : ℕ, x.1 = 2 ^ k) ∧ x.2.1.length = x.1 ∧ x.2.2.1.length = x.1

end CVPInput

/-- Exact decision CVP in the principal ideal, with squared threshold `Δ`. -/
def PrincipalCVP : Set CVPInput := {x | x.WellFormed ∧
  ∃ q : Coeff x.1,
    sqNorm (Cyclotomic.mul (ofList x.2.1) q - ofList x.2.2.1) ≤ x.2.2.2}

theorem principalCVP_iff (x : CVPInput) : x ∈ PrincipalCVP ↔
    x.WellFormed ∧ CVPYes (Cyclotomic.principalIdealLattice (ofList (d := x.1) x.2.1))
      (ofList x.2.2.1) x.2.2.2 := by
  constructor
  · rintro ⟨hw, q, hq⟩
    exact ⟨hw, Cyclotomic.mul (ofList x.2.1) q, ⟨q, rfl⟩, hq⟩
  · rintro ⟨hw, v, ⟨q, rfl⟩, hq⟩
    exact ⟨hw, q, hq⟩

/-- Forget proof fields, retaining every coefficient. -/
def toCVPInput (J : PrincipalCVPInstance) : CVPInput :=
  (J.d, toList J.g, toList J.T, J.Δ)

@[simp] theorem toCVPInput_mem_iff (J : PrincipalCVPInstance) :
    toCVPInput J ∈ PrincipalCVP ↔
      CVPYes (Cyclotomic.principalIdealLattice J.g) J.T J.Δ := by
  rw [principalCVP_iff]
  simp [toCVPInput, CVPInput.WellFormed, J.power_two]

/-- `(columns, rows, rhs, mask)`. Counts are explicit even for zero rows. -/
abbrev MaskedSys := ℕ × (List (List Bool) × (List Bool × List Bool))

def encMasked : MaskedSys ↪ List Bool :=
  encPair encUnary (encPair (encList (encList encBool))
    (encPair (encList encBool) (encList encBool)))

namespace MaskedSys

def cols (S : MaskedSys) : ℕ := S.1
def rows (S : MaskedSys) : List (List Bool) := S.2.1
def rhs (S : MaskedSys) : List Bool := S.2.2.1
def mask (S : MaskedSys) : List Bool := S.2.2.2

def WellFormed (S : MaskedSys) : Prop :=
  (∀ r ∈ S.rows, r.length = S.cols) ∧
    S.rhs.length = S.rows.length ∧ S.mask.length = S.cols

instance (S : MaskedSys) : Decidable S.WellFormed :=
  inferInstanceAs (Decidable ((∀ r ∈ S.rows, r.length = S.cols) ∧
    S.rhs.length = S.rows.length ∧ S.mask.length = S.cols))

/-- Total bridge: malformed lists are padded with false. -/
def toSystem (S : MaskedSys) : MaskedSystem S.rows.length S.cols where
  A i j := (S.rows.getD i.val []).getD j.val false
  b i := S.rhs.getD i.val false
  μ j := S.mask.getD j.val false

/-- Well-formed 0/1 linear equations with a selection mask. -/
def Feasible (S : MaskedSys) : Prop := S.WellFormed ∧ S.toSystem.HasSolution

theorem feasible_iff (S : MaskedSys) :
    S.Feasible ↔ S.WellFormed ∧ S.toSystem.HasSolution := Iff.rfl

/-- The bridge also gives an entirely list-valued certificate. -/
theorem feasible_iff_list (S : MaskedSys) : S.Feasible ↔ S.WellFormed ∧
    ∃ w : List Bool, w.length = S.cols ∧
      (∀ j : Fin S.cols, w.getD j.val false = true → S.mask.getD j.val false = true) ∧
      ∀ i : Fin S.rows.length,
        (∑ j : Fin S.cols, bit ((S.rows.getD i.val []).getD j.val false) *
          bit (w.getD j.val false)) = bit (S.rhs.getD i.val false) := by
  constructor
  · rintro ⟨hw, ξ, hmask, heq⟩
    refine ⟨hw, List.ofFn ξ, List.length_ofFn, ?_, ?_⟩
    · simpa [toSystem, MaskedSystem.Allowed, List.getD_eq_getElem?_getD] using hmask
    · intro i
      have hi := congrFun heq i
      simpa [toSystem, MaskedSystem.residual, List.getD_eq_getElem?_getD,
        sub_eq_zero] using hi
  · rintro ⟨hw, w, _, hmask, heq⟩
    refine ⟨hw, (fun j => w.getD j.val false), hmask, ?_⟩
    funext i
    exact sub_eq_zero.mpr (heq i)

end MaskedSys
end IdealCVP
