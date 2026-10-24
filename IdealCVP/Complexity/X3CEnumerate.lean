import IdealCVP.Complexity.ExactCoverGadget

/-! # Explicit enumerations for the degree-three gadget -/
open scoped List

namespace IdealCVP.ExactCoverGadget

variable {M n : ℕ} (K : Fin n → ℕ)

def edgeEnum : List (Edge K) :=
  (List.finRange n).flatMap fun j => (List.finRange (K j)).map (Sigma.mk j)

theorem mem_edgeEnum (e : Edge K) : e ∈ edgeEnum K := by
  rcases e with ⟨j,k⟩
  simp [edgeEnum]

theorem nodup_edgeEnum : (edgeEnum K).Nodup := by
  rw [edgeEnum, List.nodup_flatMap]
  constructor
  · intro j _
    exact (List.nodup_finRange _).map (by intro a b h; cases h; rfl)
  · apply (List.nodup_finRange n).imp
    intro j k hjk
    apply List.disjoint_left.mpr
    intro e he hk
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp he
    obtain ⟨b,_,hb⟩ := List.mem_map.mp hk
    exact hjk (congrArg Sigma.fst hb).symm

def portEnum : List (Port K) := ((edgeEnum K) ×ˢ (List.finRange 3))

theorem nodup_portEnum : (portEnum K).Nodup :=
  (nodup_edgeEnum K).product (List.nodup_finRange 3)

theorem mem_portEnum (p : Port K) : p ∈ portEnum K := by
  rcases p with ⟨e,r⟩
  simp [portEnum, mem_edgeEnum]

def nodeEnum : List (Node (M := M) K) :=
  ((((List.finRange M) ×ˢ (List.finRange 3))).map Sum.inl) ++
    ((((portEnum K) ×ˢ (List.finRange 3))).map Sum.inr)

theorem nodup_nodeEnum : (nodeEnum (M := M) K).Nodup := by
  rw [nodeEnum, List.nodup_append]
  refine ⟨((List.nodup_finRange M).product (List.nodup_finRange 3)).map Sum.inl_injective,
    ((nodup_portEnum K).product (List.nodup_finRange 3)).map Sum.inr_injective, ?_⟩
  intro a ha b hb he
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp ha
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hb
  exact Sum.inl_ne_inr he

theorem mem_nodeEnum (u : Node (M := M) K) : u ∈ nodeEnum K := by
  rcases u with ⟨i,r⟩ | ⟨p,t⟩ <;> simp [nodeEnum, mem_portEnum]

def columnEnum : List (Column K) :=
  (portEnum K).map (selected K) ++ (portEnum K).map (unselected K) ++ (edgeEnum K).map (shared K)

theorem nodup_columnEnum : (columnEnum K).Nodup := by
  simp only [columnEnum, List.nodup_append]
  refine ⟨⟨(nodup_portEnum K).map Sum.inl_injective,
    (nodup_portEnum K).map (Sum.inr_injective.comp Sum.inl_injective), ?_⟩,
    (nodup_edgeEnum K).map (Sum.inr_injective.comp Sum.inr_injective), ?_⟩
  · intro a ha b hb he
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hb
    exact Sum.inl_ne_inr he
  · intro a ha b hb he
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hb
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨u,_,rfl⟩ := List.mem_map.mp ha
      exact Sum.inl_ne_inr he
    · obtain ⟨u,_,rfl⟩ := List.mem_map.mp ha
      exact Sum.inl_ne_inr (Sum.inr.inj he)

theorem mem_columnEnum (c : Column K) : c ∈ columnEnum K := by
  rcases c with p | p | e <;> simp [columnEnum, selected, unselected, shared,
    mem_portEnum, mem_edgeEnum]

theorem length_nodeEnum : (nodeEnum (M := M) K).length = 3 * (M + 3*(edgeEnum K).length) := by
  simp only [nodeEnum, portEnum, List.length_append, List.length_map,
    List.length_product, List.length_finRange]
  omega

end IdealCVP.ExactCoverGadget

namespace IdealCVP

theorem idxOf_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (l : List α) (a : α) :
    (l.map f).idxOf (f a) = l.idxOf a := by
  induction l with
  | nil => simp
  | cons b l ih =>
    by_cases h : b = a
    · subst b; simp
    · have h' : f b ≠ f a := fun he => h (hf he)
      simp [List.idxOf_cons, h, Ne.symm h, h', Ne.symm h', ih]

theorem enumeratedTripleList_correct {U C : Type*} [Fintype U] [Fintype C]
    [DecidableEq U] [DecidableEq C] (us : List U) (cs : List C)
    (hu : us.Nodup) (hc : cs.Nodup) (hau : ∀ u, u ∈ us) (hac : ∀ c, c ∈ cs)
    (q : ℕ) (hlen : us.length = 3*q) (t : C → U × U × U)
    (ht : ∀ c, (t c).1 ≠ (t c).2.1 ∧ (t c).1 ≠ (t c).2.2 ∧ (t c).2.1 ≠ (t c).2.2) :
    (q, cs.map (fun c => (us.idxOf (t c).1, us.idxOf (t c).2.1, us.idxOf (t c).2.2))) ∈ X3CLang ↔
    ∃ ξ : C → Bool, ∀ u : U,
      (∑ c, if u ∈ ({(t c).1, (t c).2.1, (t c).2.2} : Finset U) then bit (ξ c) else 0) = 1 := by
  let eu : U ≃ Fin (3*q) := (List.Nodup.getEquivOfForallMemList us hu hau).symm.trans (finCongr hlen)
  let ec : Fin cs.length ≃ C := List.Nodup.getEquivOfForallMemList cs hc hac
  have huv (u : U) : (eu u).val = us.idxOf u := rfl
  let ts := fun c => (us.idxOf (t c).1, us.idxOf (t c).2.1, us.idxOf (t c).2.2)
  have huinj : Function.Injective (fun u => us.idxOf u) := by
    intro a b h
    exact eu.injective (Fin.ext h)
  have hw : X3CList.WellFormed (q,cs.map ts) := by
    intro z hz
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hz
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · change us.idxOf _ < 3*q
      rw [← huv]; exact (eu _).isLt
    · change us.idxOf _ < 3*q
      rw [← huv]; exact (eu _).isLt
    · change us.idxOf _ < 3*q
      rw [← huv]; exact (eu _).isLt
    · exact fun h => (ht c).1 (huinj h)
    · exact fun h => (ht c).2.1 (huinj h)
    · exact fun h => (ht c).2.2 (huinj h)
  have hm (u : U) (c : C) (b : Bool) :
      bit (X3CList.incident (eu u).val (ts c)) * bit b =
        if u ∈ ({(t c).1, (t c).2.1, (t c).2.2} : Finset U) then bit b else 0 := by
    have hi : X3CList.incident (eu u).val (ts c) =
        decide (u ∈ ({(t c).1, (t c).2.1, (t c).2.2} : Finset U)) := by
      apply Bool.eq_iff_iff.mpr
      simp only [X3CList.incident, decide_eq_true_eq, huv, ts,
        huinj.eq_iff, Finset.mem_insert, Finset.mem_singleton]
    rw [hi]
    by_cases h : u ∈ ({(t c).1, (t c).2.1, (t c).2.2} : Finset U) <;> simp [h, bit]
  change (X3CList.WellFormed (q,cs.map ts) ∧ X3CList.HasExactCover (q,cs.map ts)) ↔ _
  rw [and_iff_right hw]
  change (∃ ξ : Fin (cs.map ts).length → Bool, ∀ u : Fin (3*q),
    (∑ j, bit (X3CList.incident u.val (cs.map ts)[j.val]) * bit (ξ j)) = 1) ↔ _
  let ecl : C ≃ Fin (cs.map ts).length := ec.symm.trans (finCongr (List.length_map ts).symm)
  have hget (c : C) : (cs.map ts)[(ecl c).val] = ts c := by
    change (cs.map ts)[(ec.symm c).val] = ts c
    simp only [List.getElem_map]
    congr 1
    exact ec.apply_symm_apply c
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

end IdealCVP
