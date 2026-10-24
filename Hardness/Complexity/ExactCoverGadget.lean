import Hardness.Complexity.X3CList
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.List.NodupEquivFin

/-! # A degree-three exact-cover gadget

An arbitrary positive exact-one system is converted to a family of genuine
three-element sets. Three copies of each equation supply the padding: a port
has selected/unselected columns, cyclic consistency equations, and one column
shared by its three copies. This file proves finite combinatorial correctness;
it does not assert a polynomial-time certificate for finite-type enumeration.
-/
namespace Hardness.ExactCoverGadget

variable {M n : ℕ} (K : Fin n → ℕ)

abbrev Edge := (j : Fin n) × Fin (K j)
abbrev Port := Edge K × Fin 3
abbrev Node := (Fin M × Fin 3) ⊕ (Port K × Fin 3)
abbrev Column := Port K ⊕ Port K ⊕ Edge K

def next : Edge K ≃ Edge K := Equiv.sigmaCongrRight fun j => finRotate (K j)
def nextPort : Port K ≃ Port K := (next K).prodCongr (Equiv.refl _)

def original (i : Fin M) (r : Fin 3) : Node (M := M) K := .inl (i,r)
def internal (p : Port K) (t : Fin 3) : Node (M := M) K := .inr (p,t)
def selected (p : Port K) : Column K := .inl p
def unselected (p : Port K) : Column K := .inr (.inl p)
def shared (e : Edge K) : Column K := .inr (.inr e)

variable (row : Edge K → Fin M)

def triple : Column K → Finset (Node (M := M) K)
  | .inl p => {original K (row p.1) p.2, internal K p 0,
      internal K ((nextPort K).symm p) 1}
  | .inr (.inl p) => {internal K p 0, internal K p 1, internal K p 2}
  | .inr (.inr e) => {internal K (e,0) 2, internal K (e,1) 2, internal K (e,2) 2}

theorem triple_card (c : Column K) : (triple K row c).card = 3 := by
  rcases c with p | p | e <;>
    simp [triple, original, internal, Finset.card_insert_of_notMem]

def Covers (ξ : Column K → Bool) : Prop :=
  ∀ u : Node (M := M) K, (∑ c, if u ∈ triple K row c then bit (ξ c) else 0) = 1

def Solvable : Prop := ∃ v : Fin n → Bool, ∀ i : Fin M,
  (∑ e : Edge K, if row e = i then bit (v e.1) else 0) = 1

theorem mem_internal_zero (p : Port K) (c : Column K) :
    internal (M := M) K p 0 ∈ triple K row c ↔ c = selected K p ∨ c = unselected K p := by
  rcases c with q | q | e <;> simp [triple, internal, original, selected, unselected, eq_comm]

theorem mem_internal_one (p : Port K) (c : Column K) :
    internal (M := M) K p 1 ∈ triple K row c ↔
      c = selected K (nextPort K p) ∨ c = unselected K p := by
  rcases c with q | q | e
  · simp [triple, internal, original, selected, unselected, Equiv.eq_symm_apply, eq_comm]
  · simp [triple, internal, original, selected, unselected, eq_comm]
  · simp [triple, internal, original, selected, unselected]

theorem mem_internal_two (p : Port K) (c : Column K) :
    internal (M := M) K p 2 ∈ triple K row c ↔ c = unselected K p ∨ c = shared K p.1 := by
  rcases c with q | q | e
  · simp [triple, internal, original, unselected, shared]
  · simp [triple, internal, original, unselected, shared, eq_comm]
  · rcases p with ⟨e',r⟩
    fin_cases r <;> simp [triple, internal, original, unselected, shared, eq_comm]

theorem sum_pair {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α) (hab : a ≠ b) (f : α → ℤ) :
    (∑ c, if c = a ∨ c = b then f c else 0) = f a + f b := by
  have he (c : α) : (if c = a ∨ c = b then f c else 0) =
      (if c = a then f c else 0) + (if c = b then f c else 0) := by
    by_cases ha : c = a <;> by_cases hb : c = b <;> simp_all
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

theorem internal_equations (ξ : Column K → Bool) (hξ : Covers K row ξ) (p : Port K) :
    bit (ξ (selected K p)) + bit (ξ (unselected K p)) = 1 ∧
    bit (ξ (selected K (nextPort K p))) + bit (ξ (unselected K p)) = 1 ∧
    bit (ξ (unselected K p)) + bit (ξ (shared K p.1)) = 1 := by
  have h₀ := hξ (internal K p 0)
  have h₁ := hξ (internal K p 1)
  have h₂ := hξ (internal K p 2)
  simp_rw [mem_internal_zero] at h₀
  simp_rw [mem_internal_one] at h₁
  simp_rw [mem_internal_two] at h₂
  rw [sum_pair _ _ (by simp [selected, unselected])] at h₀ h₁
  rw [sum_pair _ _ (by simp [unselected, shared])] at h₂
  exact ⟨h₀,h₁,h₂⟩

theorem original_equation (ξ : Column K → Bool) (i : Fin M) (r : Fin 3) :
    (∑ c, if original K i r ∈ triple K row c then bit (ξ c) else 0) =
      ∑ e : Edge K, if row e = i then bit (ξ (selected K (e,r))) else 0 := by
  simp only [Fintype.sum_sum_type, triple, original, internal, selected]
  simp only [Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, or_false, false_or, ite_false, Finset.sum_const_zero,
    add_zero, Prod.mk.injEq]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : row e = i
  · simp [h, eq_comm]
  · simp [h, Ne.symm h]

theorem covers_iff (ξ : Column K → Bool) : Covers K row ξ ↔
    (∀ i r, (∑ e : Edge K, if row e = i then bit (ξ (selected K (e,r))) else 0) = 1) ∧
    ∀ p : Port K,
      bit (ξ (selected K p)) + bit (ξ (unselected K p)) = 1 ∧
      bit (ξ (selected K (nextPort K p))) + bit (ξ (unselected K p)) = 1 ∧
      bit (ξ (unselected K p)) + bit (ξ (shared K p.1)) = 1 := by
  constructor
  · intro h
    exact ⟨fun i r => (original_equation K row ξ i r) ▸ h (original K i r),
      internal_equations K row ξ h⟩
  · rintro ⟨ho, hp⟩ u
    rcases u with ⟨i,r⟩ | ⟨p,t⟩
    · exact (original_equation K row ξ i r).trans (ho i r)
    · fin_cases t
      · change (∑ c, if internal (M := M) K p 0 ∈ triple K row c then bit (ξ c) else 0) = 1
        simp_rw [mem_internal_zero]
        exact (sum_pair _ _ (by simp [selected, unselected]) _).trans (hp p).1
      · change (∑ c, if internal (M := M) K p 1 ∈ triple K row c then bit (ξ c) else 0) = 1
        simp_rw [mem_internal_one]
        exact (sum_pair _ _ (by simp [selected, unselected]) _).trans (hp p).2.1
      · change (∑ c, if internal (M := M) K p 2 ∈ triple K row c then bit (ξ c) else 0) = 1
        simp_rw [mem_internal_two]
        exact (sum_pair _ _ (by simp [unselected, shared]) _).trans (hp p).2.2

theorem rotation_constant {k : ℕ} (f : Fin k → Bool)
    (hf : ∀ i, f (finRotate k i) = f i) (a b : Fin k) : f a = f b := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := a.isLt; omega : k ≠ 0)
  have hz (i : ℕ) (hi : i < k'+1) : f ⟨i,hi⟩ = f ⟨0,by omega⟩ := by
    induction i with
    | zero => rfl
    | succ i ih =>
      have hp : i < k'+1 := by omega
      have he := hf ⟨i,hp⟩
      rw [finRotate_of_lt (show i < k' by omega)] at he
      exact he.trans (ih hp)
  exact (hz a.val a.isLt).trans (hz b.val b.isLt).symm

/-- Both directions of the cubic exact-cover gadget, without a runtime premise. -/
theorem correct : (∃ ξ, Covers K row ξ) ↔ Solvable K row := by
  constructor
  · rintro ⟨ξ,hξ⟩
    obtain ⟨ho,hp⟩ := (covers_iff K row ξ).mp hξ
    have hx (p : Port K) : ξ (selected K p) = ξ (shared K p.1) := by
      apply bit_injective
      have h := hp p
      omega
    have hn (e : Edge K) : ξ (shared K (next K e)) = ξ (shared K e) := by
      have ha := (hp (e,0)).1
      have hb := (hp (e,0)).2.1
      change bit (ξ (selected K (next K e,0))) + bit (ξ (unselected K (e,0))) = 1 at hb
      rw [hx (e,0)] at ha
      rw [hx (next K e,0)] at hb
      apply bit_injective
      dsimp only [Prod.fst] at ha hb
      omega
    let v : Fin n → Bool := fun j => if h : 0 < K j then ξ (shared K ⟨j,⟨0,h⟩⟩) else false
    have hv (e : Edge K) : ξ (shared K e) = v e.1 := by
      rcases e with ⟨j,k⟩
      have hk : 0 < K j := Nat.zero_lt_of_lt k.isLt
      dsimp [v]
      rw [dif_pos hk]
      apply rotation_constant (fun k => ξ (shared K ⟨j,k⟩))
      · intro k
        exact hn ⟨j,k⟩
    refine ⟨v, fun i => ?_⟩
    have he := ho i 0
    simpa only [hx, hv] using he
  · rintro ⟨v,hv⟩
    let ξ : Column K → Bool := Sum.elim (fun p => v p.1.1)
      (Sum.elim (fun p => !(v p.1.1)) (fun e => v e.1))
    refine ⟨ξ, (covers_iff K row ξ).mpr ⟨?_, ?_⟩⟩
    · intro i r
      exact hv i
    · intro ⟨⟨j,k⟩,r⟩
      cases h : v j <;> simp [ξ, selected, unselected, shared, nextPort, next, h, bit]

def tripleTuple : Column K → Node (M := M) K × Node (M := M) K × Node (M := M) K
  | .inl p => (original K (row p.1) p.2, internal K p 0,
      internal K ((nextPort K).symm p) 1)
  | .inr (.inl p) => (internal K p 0, internal K p 1, internal K p 2)
  | .inr (.inr e) => (internal K (e,0) 2, internal K (e,1) 2, internal K (e,2) 2)

theorem tripleTuple_distinct (c : Column K) :
    (tripleTuple K row c).1 ≠ (tripleTuple K row c).2.1 ∧
    (tripleTuple K row c).1 ≠ (tripleTuple K row c).2.2 ∧
    (tripleTuple K row c).2.1 ≠ (tripleTuple K row c).2.2 := by
  rcases c with p | p | e <;> simp [tripleTuple, original, internal]

theorem tripleTuple_set (c : Column K) :
    ({(tripleTuple K row c).1, (tripleTuple K row c).2.1,
      (tripleTuple K row c).2.2} : Finset _) = triple K row c := by
  rcases c with p | p | e <;> rfl

def universeThird : ℕ := M + 3 * ∑ j, K j

theorem card_node : Fintype.card (Node (M := M) K) = 3 * universeThird (M := M) K := by
  simp only [Node, Port, Edge, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_sigma, Fintype.card_fin, universeThird]
  ring

end Hardness.ExactCoverGadget

namespace Hardness

/-- Encode a finite family of triples using explicit equivalences for its
universe and indexed columns. This is a semantic bridge, not a runtime claim. -/
noncomputable def finiteTripleList {U C : Type*} [Fintype C]
    {q : ℕ} (eu : U ≃ Fin (3*q)) (t : C → U × U × U) : X3CList :=
  (q, List.ofFn fun j : Fin (Fintype.card C) =>
    let c := (Fintype.equivFin C).symm j
    ((eu (t c).1).val, (eu (t c).2.1).val, (eu (t c).2.2).val))

theorem finiteTripleList_correct {U C : Type*} [Fintype C] [DecidableEq C]
    [DecidableEq U] {q : ℕ} (eu : U ≃ Fin (3*q)) (t : C → U × U × U)
    (ht : ∀ c, (t c).1 ≠ (t c).2.1 ∧ (t c).1 ≠ (t c).2.2 ∧
      (t c).2.1 ≠ (t c).2.2) :
    finiteTripleList eu t ∈ X3CLang ↔ ∃ ξ : C → Bool,
      ∀ u : U, (∑ c, if u ∈ ({(t c).1, (t c).2.1, (t c).2.2} : Finset U)
        then bit (ξ c) else 0) = 1 := by
  let ec := Fintype.equivFin C
  let ts := fun c => ((eu (t c).1).val, (eu (t c).2.1).val, (eu (t c).2.2).val)
  have hi (u : U) (c : C) : X3CList.incident (eu u).val (ts c) =
      decide (u ∈ ({(t c).1, (t c).2.1, (t c).2.2} : Finset U)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [X3CList.incident, decide_eq_true_eq, Finset.mem_insert,
      Finset.mem_singleton, ts, Fin.val_inj, EmbeddingLike.apply_eq_iff_eq]
  have hm (u : U) (c : C) (b : Bool) :
      bit (X3CList.incident (eu u).val (ts c)) * bit b =
        if u ∈ ({(t c).1, (t c).2.1, (t c).2.2} : Finset U) then bit b else 0 := by
    rw [hi]
    by_cases h : u ∈ ({(t c).1, (t c).2.1, (t c).2.2} : Finset U) <;> simp [h, bit]
  have hw : (finiteTripleList eu t).WellFormed := by
    intro z hz
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hz
    dsimp only
    refine ⟨(eu _).isLt, (eu _).isLt, (eu _).isLt, ?_, ?_, ?_⟩
    · exact fun h => (ht _).1 (eu.injective (Fin.ext h))
    · exact fun h => (ht _).2.1 (eu.injective (Fin.ext h))
    · exact fun h => (ht _).2.2 (eu.injective (Fin.ext h))
  rw [show (finiteTripleList eu t ∈ X3CLang) ↔
      (finiteTripleList eu t).HasExactCover from and_iff_right hw]
  change (∃ ξ : Fin (List.ofFn (fun j : Fin (Fintype.card C) => ts (ec.symm j))).length → Bool,
    ∀ u : Fin (3*q), (∑ j, bit (X3CList.incident u.val
      (List.ofFn (fun j : Fin (Fintype.card C) => ts (ec.symm j)))[j.val]) * bit (ξ j)) = 1) ↔ _
  let ecl : C ≃ Fin (List.ofFn (fun j : Fin (Fintype.card C) => ts (ec.symm j))).length :=
    ec.trans (finCongr List.length_ofFn.symm)
  have hget (c : C) :
      (List.ofFn (fun j : Fin (Fintype.card C) => ts (ec.symm j)))[(ecl c).val] = ts c := by
    simp [ecl]
  constructor
  · rintro ⟨ξ,hξ⟩
    refine ⟨fun c => ξ (ecl c), fun u => ?_⟩
    have he := hξ (eu u)
    rw [← ecl.sum_comp] at he
    simpa only [hget, hm] using he
  · rintro ⟨ξ,hξ⟩
    refine ⟨fun j => ξ (ecl.symm j), fun u => ?_⟩
    obtain ⟨v,rfl⟩ := eu.surjective u
    rw [← ecl.sum_comp]
    simpa only [hget, Equiv.symm_apply_apply, hm] using hξ v

end Hardness

namespace Hardness.ExactCoverGadget

variable {M n : ℕ} (K : Fin n → ℕ) (row : Edge K → Fin M)

/-- A semantic list encoding, using finite-type equivalences. No claim that
this choice-based enumeration has a certified runtime is made. -/
noncomputable def semanticList : X3CList :=
  finiteTripleList ((Fintype.equivFin (Node (M := M) K)).trans
    (finCongr (card_node K))) (tripleTuple K row)

theorem semanticList_correct : semanticList K row ∈ X3CLang ↔ Solvable K row := by
  rw [semanticList, finiteTripleList_correct _ _ (tripleTuple_distinct K row)]
  simp_rw [tripleTuple_set]
  exact correct K row

end Hardness.ExactCoverGadget
