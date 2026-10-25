import IdealCVP.Lattice

/-! # Indexed exact covers and masked Boolean systems

These finite incidence systems give the input language and Boolean
formulation used in `paper/src/chapter/principal-ideal.tex`.
-/
namespace IdealCVP

/-- The integer represented by a Boolean bit. -/
def bit (b : Bool) : ℤ := if b then 1 else 0

@[simp] theorem bit_false : bit false = 0 := rfl
@[simp] theorem bit_true : bit true = 1 := rfl
theorem bit_nonneg (b : Bool) : 0 ≤ bit b := by cases b <;> simp
theorem bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> simp
theorem bit_injective : Function.Injective bit := by
  intro a b h; cases a <;> cases b <;> simp_all

/-- The masked Boolean system of equation (masked-system). -/
structure MaskedSystem (M n : ℕ) where
  A : Fin M → Fin n → Bool
  b : Fin M → Bool
  μ : Fin n → Bool

namespace MaskedSystem
variable {M n : ℕ} (S : MaskedSystem M n)

/-- Every selected variable is permitted by the mask. -/
def Allowed (ξ : Fin n → Bool) : Prop := ∀ j, ξ j = true → S.μ j = true

/-- The integral residual vector of the Boolean incidence equations. -/
def residual (ξ : Fin n → Bool) : Coeff M :=
  fun i => (∑ j, bit (S.A i j) * bit (ξ j)) - bit (S.b i)

/-- A Boolean assignment satisfies both the mask and every incidence equation. -/
def Feasible (ξ : Fin n → Bool) : Prop := S.Allowed ξ ∧ S.residual ξ = 0

/-- There exists a feasible Boolean assignment. -/
def HasSolution : Prop := ∃ ξ, S.Feasible ξ

end MaskedSystem

/-- An indexed collection: repeated triples retain their distinct indices.
The universe has size 3q; positive q and n match the paper's conventions. -/
structure X3CInstance where
  q : ℕ
  n : ℕ
  q_pos : 0 < q
  n_pos : 0 < n
  triples : Fin n → Finset (Fin (3 * q))
  triple_card : ∀ j, (triples j).card = 3

namespace X3CInstance
variable (I : X3CInstance)

/-- Each universe element belongs to exactly one selected indexed triple. -/
def IsExactCover (s : Finset (Fin I.n)) : Prop :=
  ∀ i, (s.filter fun j => i ∈ I.triples j).card = 1

/-- Some subcollection of indexed triples covers every universe element exactly once. -/
def HasExactCover : Prop := ∃ s, I.IsExactCover s

/-- The all-ones incidence equations associated to an indexed X3C instance. -/
def system : MaskedSystem (3 * I.q) I.n where
  A i j := decide (i ∈ I.triples j)
  b _ := true
  μ _ := true

/-- The canonical correspondence between index sets and Boolean vectors. -/
def selectionEquiv : Finset (Fin I.n) ≃ (Fin I.n → Bool) where
  toFun s j := decide (j ∈ s)
  invFun ξ := Finset.univ.filter fun j => ξ j = true
  left_inv s := by ext j; simp
  right_inv ξ := by funext j; cases h : ξ j <;> simp [h]

/-- Indexed exact covers correspond exactly to feasible Boolean incidence selections. -/
theorem cover_iff_feasible (s : Finset (Fin I.n)) :
    I.IsExactCover s ↔ I.system.Feasible (I.selectionEquiv s) := by
  have hsum (i : Fin (3 * I.q)) :
      (∑ j, bit (I.system.A i j) * bit (I.selectionEquiv s j)) =
        ((s.filter fun j => i ∈ I.triples j).card : ℤ) := by
    simp only [system, selectionEquiv, Equiv.coe_fn_mk, bit, decide_eq_true_eq]
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun j => j ∈ s) = s := by ext j; simp
    rw [hf]
    rw [← Finset.sum_filter]
    simp
  change (∀ i, (s.filter fun j => i ∈ I.triples j).card = 1) ↔
    ((∀ j, I.selectionEquiv s j = true → true = true) ∧
      (fun i => (∑ j, bit (I.system.A i j) * bit (I.selectionEquiv s j)) - 1) = 0)
  simp only [implies_true, true_and, funext_iff, Pi.zero_apply,
    sub_eq_zero, hsum, Nat.cast_eq_one]

/-- The indexed cover instance and its masked Boolean system are equisatisfiable. -/
theorem hasExactCover_iff_hasSolution : I.HasExactCover ↔ I.system.HasSolution := by
  constructor
  · rintro ⟨s, hs⟩; exact ⟨I.selectionEquiv s, (I.cover_iff_feasible s).mp hs⟩
  · rintro ⟨ξ, hξ⟩
    refine ⟨I.selectionEquiv.symm ξ, ?_⟩
    exact (I.cover_iff_feasible _).mpr (by simpa using hξ)

/-- A bijection of the solution types, rather than only equisatisfiability. -/
def exactCoverEquivFeasible :
    {s // I.IsExactCover s} ≃ {ξ // I.system.Feasible ξ} :=
  I.selectionEquiv.subtypeEquiv (fun s => I.cover_iff_feasible s)

end X3CInstance
end IdealCVP
