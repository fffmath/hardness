import IdealCVP.Complexity.Problem

/-! # X3C with unary universe size and binary element labels

Repeated triples keep their indices. Out-of-range labels and triples with
repeated elements are rejected. The empty universe has the empty exact cover.
-/
namespace IdealCVP
open Turing.MultiTapeTM

abbrev X3CTriple := ℕ × ℕ × ℕ
abbrev X3CList := ℕ × List X3CTriple

def encX3CTriple : X3CTriple ↪ List Bool := encPair encNat (encPair encNat encNat)
def encX3C : X3CList ↪ List Bool := encPair encUnary (encList encX3CTriple)

namespace X3CList

def ValidTriple (q : ℕ) (t : X3CTriple) : Prop :=
  t.1 < 3*q ∧ t.2.1 < 3*q ∧ t.2.2 < 3*q ∧
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

instance (q : ℕ) (t : X3CTriple) : Decidable (ValidTriple q t) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def WellFormed (x : X3CList) : Prop := ∀ t ∈ x.2, ValidTriple x.1 t

instance (x : X3CList) : Decidable x.WellFormed :=
  inferInstanceAs (Decidable (∀ t ∈ x.2, ValidTriple x.1 t))

def incident (u : ℕ) (t : X3CTriple) : Bool :=
  decide (u = t.1 ∨ u = t.2.1 ∨ u = t.2.2)

/-- Every element is incident to exactly one selected index. -/
def HasExactCover (x : X3CList) : Prop :=
  ∃ ξ : Fin x.2.length → Bool, ∀ u : Fin (3*x.1),
    (∑ j : Fin x.2.length, bit (incident u.val x.2[j.val]) * bit (ξ j)) = 1

def tripleFinset (q : ℕ) (t : X3CTriple) (h : ValidTriple q t) : Finset (Fin (3*q)) :=
  {⟨t.1, h.1⟩, ⟨t.2.1, h.2.1⟩, ⟨t.2.2, h.2.2.1⟩}

theorem tripleFinset_card (q : ℕ) (t : X3CTriple) (h : ValidTriple q t) :
    (tripleFinset q t h).card = 3 := by
  unfold tripleFinset
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simpa only [Finset.mem_singleton, Fin.mk.injEq] using h.2.2.2.2.2
  · simpa only [Finset.mem_insert, Finset.mem_singleton, Fin.mk.injEq, not_or] using
      And.intro h.2.2.2.1 h.2.2.2.2.1

/-- Package a nondegenerate list as the paper's proof-carrying instance. -/
def toInstance (x : X3CList) (hw : x.WellFormed)
    (hq : 0 < x.1) (hn : 0 < x.2.length) : X3CInstance where
  q := x.1
  n := x.2.length
  q_pos := hq
  n_pos := hn
  triples j := tripleFinset x.1 x.2[j.val] (hw _ (List.getElem_mem j.isLt))
  triple_card j := tripleFinset_card _ _ _

@[simp] theorem toInstance_system (x : X3CList) (hw : x.WellFormed)
    (hq : 0 < x.1) (hn : 0 < x.2.length) (u : Fin (3*x.1)) (j : Fin x.2.length) :
    (toInstance x hw hq hn).system.A u j = incident u.val x.2[j.val] := by
  change decide (u ∈ tripleFinset x.1 x.2[j.val] (hw _ (List.getElem_mem j.isLt))) = incident u.val x.2[j.val]
  apply Bool.eq_iff_iff.mpr
  simp [tripleFinset, incident, Fin.ext_iff]

theorem hasExactCover_iff_toInstance (x : X3CList) (hw : x.WellFormed)
    (hq : 0 < x.1) (hn : 0 < x.2.length) :
    x.HasExactCover ↔ (toInstance x hw hq hn).HasExactCover := by
  rw [X3CInstance.hasExactCover_iff_hasSolution]
  unfold HasExactCover MaskedSystem.HasSolution MaskedSystem.Feasible
  apply exists_congr
  intro ξ
  change _ ↔ ((∀ j, ξ j = true → true = true) ∧
    (fun u => (∑ j, bit ((toInstance x hw hq hn).system.A u j) * bit (ξ j)) - 1) = 0)
  simp only [implies_true, true_and, funext_iff, Pi.zero_apply, sub_eq_zero]
  change _ ↔ ∀ u : Fin (3*x.1),
    (∑ j : Fin x.2.length, bit ((toInstance x hw hq hn).system.A u j) * bit (ξ j)) = 1
  simp only [toInstance_system]

@[simp] theorem zero_universe (ts : List X3CTriple) :
    WellFormed (0, ts) ↔ ts = [] := by
  cases ts with
  | nil => simp [WellFormed]
  | cons t ts =>
    constructor
    · intro h
      have ht := h t (by simp)
      have : t.1 < 0 := ht.1
      omega
    · simp

@[simp] theorem empty_hasExactCover (q : ℕ) :
    HasExactCover (q, []) ↔ q = 0 := by
  constructor
  · rintro ⟨ξ, hξ⟩
    by_contra hq
    have h := hξ ⟨0, by omega⟩
    simp at h
  · rintro rfl
    exact ⟨Fin.elim0, fun u => Fin.elim0 u⟩

end X3CList

def X3CLang : Set X3CList := {x | x.WellFormed ∧ x.HasExactCover}

theorem x3cList_mem_iff (x : X3CList) (hw : x.WellFormed)
    (hq : 0 < x.1) (hn : 0 < x.2.length) :
    x ∈ X3CLang ↔ (x.toInstance hw hq hn).HasExactCover := by
  exact (and_iff_right hw).trans (x.hasExactCover_iff_toInstance hw hq hn)

@[simp] theorem x3cList_empty_mem (q : ℕ) : (q, []) ∈ X3CLang ↔ q = 0 := by
  simp [X3CLang, X3CList.WellFormed]

@[simp] theorem x3cList_zero_mem (ts : List X3CTriple) :
    (0, ts) ∈ X3CLang ↔ ts = [] := by
  constructor
  · exact fun h => (X3CList.zero_universe ts).mp h.1
  · rintro rfl
    exact (x3cList_empty_mem 0).mpr rfl

end IdealCVP
