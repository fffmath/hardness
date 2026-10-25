import IdealCVP.Fixed

/-! # Indexed X3C and the fixed family

Removing repeated triples preserves exact covers. An exact cover cannot use
both copies of a nonempty triple; in the other direction we select one index
for each triple of the cover.
-/
noncomputable section
namespace IdealCVP
namespace X3CInstance

/-- The indexed triple, with its certificate as a member of the universal family. -/
def asTriple (I : X3CInstance) (j : Fin I.n) : Fixed.Triple (3 * I.q) :=
  ⟨I.triples j, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, I.triple_card j⟩⟩

/-- Forget the indices, identifying repeated triples. -/
def toTripleSet (I : X3CInstance) : Finset (Fixed.Triple (3 * I.q)) :=
  Finset.univ.image I.asTriple

/-- Selected indices in an exact cover have distinct triples. -/
theorem IsExactCover.injOn_triples {I : X3CInstance} {s : Finset (Fin I.n)}
    (hs : I.IsExactCover s) : Set.InjOn I.asTriple s := by
  intro j hj k hk heq
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by rw [I.triple_card j]; omega)
  have hik : i ∈ I.triples k := by
    have hval := congrArg Subtype.val heq
    change I.triples j = I.triples k at hval
    rwa [← hval]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hs i)
  have hj' : j = a := Finset.mem_singleton.mp (ha ▸ Finset.mem_filter.mpr ⟨hj, hi⟩)
  have hk' : k = a := Finset.mem_singleton.mp (ha ▸ Finset.mem_filter.mpr ⟨hk, hik⟩)
  exact hj'.trans hk'.symm

/-- The set formulation is faithful even when the indexed input has repetitions. -/
theorem hasExactCover_iff_toTripleSet (I : X3CInstance) :
    I.HasExactCover ↔ Fixed.HasExactCover I.toTripleSet := by
  classical
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s.image I.asTriple, Finset.image_subset_image (Finset.subset_univ s), ?_⟩
    intro i
    have hf : (s.image I.asTriple).filter (fun t => i ∈ t.val) =
        (s.filter fun j => i ∈ I.triples j).image I.asTriple := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨j, hj, rfl⟩, hi⟩
        exact ⟨j, ⟨hj, hi⟩, rfl⟩
      · rintro ⟨j, ⟨hj, hi⟩, rfl⟩
        exact ⟨⟨j, hj, rfl⟩, hi⟩
    rw [hf, Finset.card_image_of_injOn]
    · exact hs i
    · exact hs.injOn_triples.mono (Finset.filter_subset _ _)
  · rintro ⟨s, hsub, hs⟩
    have hex (t : ↥s) : ∃ j, I.asTriple j = t.val := by
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hsub t.property)
      exact ⟨j, hj⟩
    choose f hf using hex
    have hinj : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      exact (hf a).symm.trans ((congrArg I.asTriple h).trans (hf b))
    refine ⟨Finset.univ.image f, ?_⟩
    intro i
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp (hs i)
    have htmem : t ∈ s ∧ i ∈ t.val :=
      Finset.mem_filter.mp (ht.symm ▸ Finset.mem_singleton_self t)
    apply Finset.card_eq_one.mpr
    refine ⟨f ⟨t, htmem.1⟩, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨a, rfl⟩, hi⟩
      have hai : i ∈ a.val.val := by
        change i ∈ (I.asTriple (f a)).val at hi
        rwa [hf a] at hi
      have hat : a.val = t := Finset.mem_singleton.mp
        (ht ▸ Finset.mem_filter.mpr ⟨a.property, hai⟩)
      exact congrArg f (Subtype.ext hat)
    · rintro rfl
      refine ⟨⟨⟨t, htmem.1⟩, rfl⟩, ?_⟩
      change i ∈ (I.asTriple (f ⟨t, htmem.1⟩)).val
      rw [hf]
      exact htmem.2

/-- The fixed-family construction applies to every indexed X3C input. -/
theorem fixed_universe_ge_three (I : X3CInstance) : 3 ≤ 3 * I.q := by
  have := I.q_pos
  omega

end X3CInstance

/-- Indexed version of paper `thm:fixed-family`. -/
theorem fixed_family_correct_indexed (I : X3CInstance) :
    I.HasExactCover ↔ CVPYes (Fixed.lattice (3 * I.q) I.fixed_universe_ge_three)
      (Fixed.target (3 * I.q) I.fixed_universe_ge_three I.toTripleSet)
      (Fixed.threshold (3 * I.q) I.fixed_universe_ge_three I.toTripleSet) :=
  I.hasExactCover_iff_toTripleSet.trans (Fixed.fixed_family_correct _ _ _)

/-- An indexed exact cover attains the fixed-family squared-distance threshold. -/
theorem fixed_family_yes_indexed (I : X3CInstance) (hy : I.HasExactCover) :
    MinimumSquaredDistance (Fixed.lattice (3 * I.q) I.fixed_universe_ge_three)
      (Fixed.target (3 * I.q) I.fixed_universe_ge_three I.toTripleSet)
      (Fixed.threshold (3 * I.q) I.fixed_universe_ge_three I.toTripleSet) :=
  Fixed.fixed_family_yes _ _ _ (I.hasExactCover_iff_toTripleSet.mp hy)

/-- Without an indexed exact cover, every fixed-family lattice vector has the strict gap. -/
theorem fixed_family_no_indexed (I : X3CInstance) (hn : ¬ I.HasExactCover) :
    ∀ v ∈ Fixed.lattice (3 * I.q) I.fixed_universe_ge_three,
      Fixed.threshold (3 * I.q) I.fixed_universe_ge_three I.toTripleSet + 4 ≤
        sqNorm (v - Fixed.target (3 * I.q) I.fixed_universe_ge_three I.toTripleSet) :=
  Fixed.fixed_family_no _ _ _ (hn ∘ I.hasExactCover_iff_toTripleSet.mpr)

end IdealCVP
