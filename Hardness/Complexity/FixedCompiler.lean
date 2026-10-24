import Hardness.Complexity.SatToX3C

/-! # A cubic compiler for one fixed ideal per universe size

All ordered triples are columns. The incidence matrix and right-hand side
depend only on the universe size; a collection changes only the Boolean mask.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Hardness
open Turing.MultiTapeTM Cslib.Complexity
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Boolean equations with rhs one are exact-cover cardinality equations. -/
theorem masked_hasSolution_iff_cover {M n : ℕ} (S : MaskedSystem M n)
    (hb : ∀ i, S.b i = true) : S.HasSolution ↔
    ∃ s : Finset (Fin n), (∀ j ∈ s, S.μ j = true) ∧
      ∀ i, (s.filter fun j => S.A i j = true).card = 1 := by
  classical
  have hsum (s : Finset (Fin n)) (i : Fin M) :
      (∑ j, bit (S.A i j) * bit (decide (j ∈ s))) =
        ((s.filter fun j => S.A i j = true).card : ℤ) := by
    simp only [bit, decide_eq_true_eq, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    simp
  constructor
  · rintro ⟨ξ,hμ,he⟩
    let s := Finset.univ.filter fun j => ξ j = true
    have hs (j : Fin n) : decide (j ∈ s) = ξ j := by
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
      cases ξ j <;> rfl
    refine ⟨s, fun j hj => hμ j (by simpa [s] using hj), fun i => ?_⟩
    have hi := congrFun he i
    change (∑ j, bit (S.A i j) * bit (ξ j)) - bit (S.b i) = 0 at hi
    simp only [← hs, hsum, hb, bit_true] at hi
    omega
  · rintro ⟨s,hμ,he⟩
    refine ⟨(fun j => decide (j ∈ s)), ?_, ?_⟩
    · intro j hj; exact hμ j (of_decide_eq_true hj)
    · funext i
      simp [MaskedSystem.residual, hb, hsum, he]

/-- Identifying repeated nonempty columns preserves exact covers. -/
theorem cover_image_iff {U C D : Type*} [Fintype C] [DecidableEq C]
    [DecidableEq D] (r : U → D → Prop) [∀ u d, Decidable (r u d)]
    (f : C → D) (allowed : Finset C) (hne : ∀ c ∈ allowed, ∃ u, r u (f c)) :
    (∃ s : Finset C, s ⊆ allowed ∧ ∀ u, (s.filter fun c => r u (f c)).card = 1) ↔
    ∃ s : Finset D, s ⊆ allowed.image f ∧ ∀ u, (s.filter (r u)).card = 1 := by
  classical
  constructor
  · rintro ⟨s,hsub,hs⟩
    have hinj : Set.InjOn f s := by
      intro c hc e he hce
      obtain ⟨u,hu⟩ := hne c (hsub hc)
      obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (hs u)
      have hc' : c = a := Finset.mem_singleton.mp (ha ▸ Finset.mem_filter.mpr ⟨hc,hu⟩)
      have he' : e = a := Finset.mem_singleton.mp
        (ha ▸ Finset.mem_filter.mpr ⟨he,by rwa [← hce]⟩)
      exact hc'.trans he'.symm
    refine ⟨s.image f, Finset.image_subset_image hsub, fun u => ?_⟩
    have hf : (s.image f).filter (r u) = (s.filter fun c => r u (f c)).image f := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨c,hc,rfl⟩,hu⟩; exact ⟨c,⟨hc,hu⟩,rfl⟩
      · rintro ⟨c,⟨hc,hu⟩,rfl⟩; exact ⟨⟨c,hc,rfl⟩,hu⟩
    rw [hf, Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))]
    exact hs u
  · rintro ⟨s,hsub,hs⟩
    have hex (d : ↥s) : ∃ c ∈ allowed, f c = d.val := Finset.mem_image.mp (hsub d.property)
    choose g hg hf using hex
    refine ⟨Finset.univ.image g, ?_, fun u => ?_⟩
    · rintro c hc
      obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hc
      exact hg d
    · obtain ⟨d,hd⟩ := Finset.card_eq_one.mp (hs u)
      have hdm : d ∈ s ∧ r u d :=
        Finset.mem_filter.mp (hd.symm ▸ Finset.mem_singleton_self d)
      apply Finset.card_eq_one.mpr
      refine ⟨g ⟨d,hdm.1⟩, ?_⟩
      ext c
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨a,rfl⟩,hu⟩
        have hau : r u a.val := by rwa [hf a] at hu
        have had : a.val = d := Finset.mem_singleton.mp
          (hd ▸ Finset.mem_filter.mpr ⟨a.property,hau⟩)
        exact congrArg g (Subtype.ext had)
      · rintro rfl
        exact ⟨⟨⟨d,hdm.1⟩,rfl⟩,by simpa [hf] using hdm.2⟩

/-- The image formulation for a masked family of nonempty columns. -/
theorem masked_image_cover_iff {M n : ℕ} {D : Type*} [DecidableEq D]
    (S : MaskedSystem M n) (hb : ∀ i, S.b i = true)
    (f : Fin n → D) (r : Fin M → D → Prop) [∀ u d, Decidable (r u d)]
    (hA : ∀ i j, S.A i j = true ↔ r i (f j))
    (hne : ∀ j, S.μ j = true → ∃ u, r u (f j)) :
    S.HasSolution ↔ ∃ s : Finset D,
      s ⊆ (Finset.univ.filter fun j => S.μ j = true).image f ∧
        ∀ u, (s.filter (r u)).card = 1 := by
  classical
  rw [masked_hasSolution_iff_cover S hb]
  simp_rw [hA]
  have hsub (s : Finset (Fin n)) :
      (∀ j ∈ s, S.μ j = true) ↔ s ⊆ Finset.univ.filter (fun j => S.μ j = true) := by
    constructor
    · intro h j hj; exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,h j hj⟩
    · intro h j hj; exact (Finset.mem_filter.mp (h hj)).2
  simp_rw [hsub]
  exact cover_image_iff r f _ (fun j hj => hne j (Finset.mem_filter.mp hj).2)

/-- A list family with an arbitrary collection mask, used in the bridge. -/
def tripleSystem (m : ℕ) (l cs : List X3CTriple) : MaskedSystem m l.length where
  A i j := X3CList.incident i.val l[j.val]
  b _ := true
  μ j := decide (l[j.val] ∈ cs)

theorem tripleSystem_correct (m : ℕ) (l cs : List X3CTriple)
    (hcs : ∀ t ∈ cs, t ∈ l) (hne : ∀ t ∈ cs, ∃ u : Fin m, X3CList.incident u.val t = true) :
    (tripleSystem m l cs).HasSolution ↔ ∃ s : Finset X3CTriple, s ⊆ cs.toFinset ∧
      ∀ u : Fin m, (s.filter fun t => X3CList.incident u.val t = true).card = 1 := by
  classical
  have he : (Finset.univ.filter fun j : Fin l.length =>
      (tripleSystem m l cs).μ j = true).image (fun j => l[j.val]) = cs.toFinset := by
    ext t
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      tripleSystem, decide_eq_true_eq, List.mem_toFinset]
    constructor
    · rintro ⟨j,hj,rfl⟩; exact hj
    · intro ht
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (hcs t ht)
      exact ⟨⟨i,hi⟩, by simpa [he] using ht, he⟩
  rw [masked_image_cover_iff (tripleSystem m l cs) (by intro i; rfl)
    (fun j => l[j.val]) (fun u t => X3CList.incident u.val t = true)
    (by intro i j; rfl) (by intro j hj; exact hne _ (of_decide_eq_true hj)), he]

namespace FixedFast

def triples (m : ℕ) : List X3CTriple :=
  (List.range m).flatMap fun a =>
    (List.range m).flatMap fun b => (List.range m).map fun c => (a,b,c)

@[simp] theorem mem_triples (m : ℕ) (t : X3CTriple) : t ∈ triples m ↔
    t.1 < m ∧ t.2.1 < m ∧ t.2.2 < m := by
  rcases t with ⟨a,b,c⟩
  simp [triples, List.mem_flatMap, List.mem_map, Prod.mk.injEq]

def system (m : ℕ) (ts : List X3CTriple) : MaskedSys :=
  ((triples m).length,
    (List.range m).map (fun u => (triples m).map (X3CList.incident u)),
    List.replicate m true,
    (triples m).map fun t => decide (t ∈ ts))

theorem system_wellFormed (m : ℕ) (ts : List X3CTriple) :
    (system m ts).WellFormed := by
  simp [system, MaskedSys.WellFormed, MaskedSys.cols, MaskedSys.rows,
    MaskedSys.rhs, MaskedSys.mask]

theorem system_hasSolution_iff (m : ℕ) (ts : List X3CTriple) :
    (system m ts).toSystem.HasSolution ↔ (tripleSystem m (triples m) ts).HasSolution := by
  have hlen : (system m ts).rows.length = m := by simp [system, MaskedSys.rows]
  have hA (i : Fin (system m ts).rows.length) (j : Fin (triples m).length) :
      (system m ts).toSystem.A i j = X3CList.incident i.val (triples m)[j.val] := by
    have hi : i.val < m := by simpa [hlen] using i.isLt
    simp [MaskedSys.toSystem, system, MaskedSys.rows, List.getD_eq_getElem?_getD,
      hi, j.isLt]
  have hb (i : Fin (system m ts).rows.length) : (system m ts).toSystem.b i = true := by
    have hi : i.val < m := by simpa [hlen] using i.isLt
    simp [MaskedSys.toSystem, system, MaskedSys.rhs, List.getD_eq_getElem?_getD,
      List.getElem?_replicate, hi]
  have hmu (j : Fin (triples m).length) :
      (system m ts).toSystem.μ j = decide ((triples m)[j.val] ∈ ts) := by
    simp [MaskedSys.toSystem, system, MaskedSys.mask, List.getD_eq_getElem?_getD, j.isLt]
  constructor
  · rintro ⟨ξ,hμ,he⟩
    refine ⟨ξ, ?_, ?_⟩
    · intro j hj; simpa only [hmu, tripleSystem] using hμ j hj
    · funext i
      have hh := congrFun he ⟨i.val, by exact i.isLt.trans_eq hlen.symm⟩
      simp only [MaskedSystem.residual, tripleSystem, hA, hb, bit_true, Pi.zero_apply] at hh ⊢
      simpa only [MaskedSys.cols, system] using hh
  · rintro ⟨ξ,hμ,he⟩
    refine ⟨ξ, ?_, ?_⟩
    · intro j hj; rw [hmu]; exact hμ j hj
    · funext i
      have hh := congrFun he ⟨i.val, by exact i.isLt.trans_eq hlen⟩
      simp only [MaskedSystem.residual, tripleSystem, hA, hb, bit_true, Pi.zero_apply] at hh ⊢
      simpa only [MaskedSys.cols, system] using hh

theorem system_correct (x : X3CList) (hw : x.WellFormed) :
    (system (3*x.1) x.2).Feasible ↔ x.HasExactCover := by
  classical
  have hcs : ∀ t ∈ x.2, t ∈ triples (3*x.1) := by
    intro t ht
    have hv := hw t ht
    exact (mem_triples _ _).mpr ⟨hv.1,hv.2.1,hv.2.2.1⟩
  have hne : ∀ t ∈ x.2, ∃ u : Fin (3*x.1), X3CList.incident u.val t = true := by
    intro t ht
    exact ⟨⟨t.1,(hw t ht).1⟩,by simp [X3CList.incident]⟩
  have hs := tripleSystem_correct (3*x.1) x.2 x.2 (fun _ h => h) hne
  have ht := tripleSystem_correct (3*x.1) (triples (3*x.1)) x.2 hcs hne
  rw [MaskedSys.Feasible, and_iff_right (system_wellFormed _ _), system_hasSolution_iff, ht,
    ← hs]
  unfold tripleSystem MaskedSystem.HasSolution MaskedSystem.Feasible
    MaskedSystem.Allowed MaskedSystem.residual
  simp only [List.getElem_mem, decide_true, implies_true, forall_const, true_and,
    bit_true, funext_iff, Pi.zero_apply, sub_eq_zero]
  rfl

/-- This base system, hence its generator, has no collection argument. -/
def base (m : ℕ) : MaskedSys := system m []

def gen (m : ℕ) : List ℤ := (Fast.compile (base m)).2.1

def dimension (m : ℕ) : ℕ := (Fast.compile (base m)).1

theorem data_withMask (m : ℕ) (ts : List X3CTriple) :
    (system m ts).reductionDataCubic = (base m).reductionDataCubic.withMask
      (system m ts).paddedSystem.μ := rfl

theorem dimension_independent (m : ℕ) (ts : List X3CTriple) :
    (Fast.compile (system m ts)).1 = dimension m := rfl

/-- The cubic compiler's generator really is independent of the presence mask. -/
theorem generator_independent (m : ℕ) (ts : List X3CTriple) :
    (Fast.compile (system m ts)).2.1 = gen m := by
  rw [Fast.compile_eq]
  unfold gen
  rw [Fast.compile_eq]
  change toList (system m ts).reductionDataCubic.g = toList (base m).reductionDataCubic.g
  rw [data_withMask]
  exact congrArg toList ((base m).reductionDataCubic.generator_mask_independent _)

section Runtime
attribute [local irreducible] List.getD system Fast.compile

@[fun_prop] theorem poly_triples : ComputableTidilyInPolyTime triples encUnary
    (encList encX3CTriple) := by
  unfold triples
  apply flatMapWithInput (encA := encUnary) (by fun_prop)
  apply flatMapWithInput (encA := encUnary) (by fun_prop)
  apply mapWithInput (encA := encUnary) (by fun_prop)
  unfold encX3CTriple
  fun_prop

@[fun_prop] theorem poly_presence : ComputableTidilyInPolyTime
    (fun p : List X3CTriple × X3CTriple => decide (p.2 ∈ p.1))
    (encPair (encList encX3CTriple) encX3CTriple) encBool := by
  have he : (fun p : List X3CTriple × X3CTriple => decide (p.2 ∈ p.1)) =
      (fun p => p.1.any fun t => decide (t = p.2)) := by
    funext p
    apply Bool.eq_iff_iff.mpr
    simp [List.any_eq_true]
  rw [he]
  apply anyWithInput (encA := encX3CTriple) (by fun_prop)
  exact decide_eq' (snd _ _) (fst _ _).snd'

@[fun_prop] theorem poly_system : ComputableTidilyInPolyTime
    (fun p : ℕ × List X3CTriple => system p.1 p.2)
    (encPair encUnary (encList encX3CTriple)) encMasked := by
  have hrow : ComputableTidilyInPolyTime
      (fun p : (ℕ × List X3CTriple) × ℕ => (triples p.1.1).map (X3CList.incident p.2))
      (encPair (encPair encUnary (encList encX3CTriple)) encUnary) (encList encBool) := by
    apply mapWithInput (encA := encX3CTriple) (by fun_prop)
    exact X3CList.poly_incident.comp
      ((unary_to_binary.comp (fst _ _).snd').prod (snd _ _))
  have hmask : ComputableTidilyInPolyTime
      (fun p : ℕ × List X3CTriple => (triples p.1).map fun t => decide (t ∈ p.2))
      (encPair encUnary (encList encX3CTriple)) (encList encBool) := by
    apply mapWithInput (encA := encX3CTriple) (by fun_prop)
    exact poly_presence.comp ((fst _ _).snd'.prod (snd _ _))
  have ht := poly_triples.comp (fst encUnary (encList encX3CTriple))
  have hn := (length encX3CTriple).comp ht
  have hr : ComputableTidilyInPolyTime
      (fun p : ℕ × List X3CTriple =>
        (List.range p.1).map fun u => (triples p.1).map (X3CList.incident u))
      (encPair encUnary (encList encX3CTriple)) (encList (encList encBool)) :=
    mapWithInput (encA := encUnary)
      (range.comp (fst encUnary (encList encX3CTriple))) hrow
  have hb : ComputableTidilyInPolyTime
      (fun p : ℕ × List X3CTriple => List.replicate p.1 true)
      (encPair encUnary (encList encX3CTriple)) (encList encBool) := by fun_prop
  unfold system encMasked
  exact hn.prod (hr.prod (hb.prod hmask))

end Runtime
end FixedFast

abbrev FixedCVPPInput := ℕ × (List ℤ × ℤ)

def encFixedCVPP : FixedCVPPInput ↪ List Bool :=
  encPair encUnary (encPair (encList encIntBin) encIntBin)

abbrev fixedGen := FixedFast.gen

theorem fixed_dimension_power_two (m : ℕ) : ∃ k, FixedFast.dimension m = 2 ^ k := by
  change ∃ k, (FixedFast.base m).reductionDataCubic.d = 2 ^ k
  exact (FixedFast.base m).reductionDataCubic.d_power_two

theorem fixedGen_ne_zero (m : ℕ) :
    ofList (d := FixedFast.dimension m) (fixedGen m) ≠ 0 := by
  unfold fixedGen FixedFast.gen
  rw [Fast.compile_eq]
  change ofList (d := (FixedFast.base m).reductionDataCubic.d)
    (toList (FixedFast.base m).reductionDataCubic.g) ≠ 0
  exact fun h => (FixedFast.base m).reductionDataCubic.g_ne_zero
    ((ofList_toList _).symm.trans h)

/-- Exact distance to one principal ideal for each unary universe size. -/
def FixedCVPP : Set FixedCVPPInput := {x | x.2.1.length = FixedFast.dimension x.1 ∧
  CVPYes (Cyclotomic.principalIdealLattice
    (ofList (d := FixedFast.dimension x.1) (fixedGen x.1))) (ofList x.2.1) x.2.2}

def fixedNoInput : FixedCVPPInput := (0, [], -1)

theorem fixedNoInput_not_mem : fixedNoInput ∉ FixedCVPP := by
  rintro ⟨_,v,_,hv⟩
  have := sqNorm_nonneg (v - ofList fixedNoInput.2.1)
  change _ ≤ (-1 : ℤ) at hv
  omega

def x3cToFixedCVPP (x : X3CList) : FixedCVPPInput :=
  if X3CList.wellFormedCheck x then
    let C := Fast.compile (FixedFast.system (3*x.1) x.2)
    (3*x.1, C.2.2.1, C.2.2.2)
  else fixedNoInput

theorem fixed_compile_correct (m : ℕ) (ts : List X3CTriple) :
    (FixedFast.system m ts).Feasible ↔
      (m, (Fast.compile (FixedFast.system m ts)).2.2) ∈ FixedCVPP := by
  let S := FixedFast.system m ts
  have hc := compileFast_correct S
  rw [compileFast_eq S (FixedFast.system_wellFormed _ _)] at hc
  rw [← Fast.compile_eq S] at hc
  rw [principalCVP_iff] at hc
  have hw : (Fast.compile S).WellFormed := by
    rw [Fast.compile_eq]
    simp [CVPInput.WellFormed, toCVPInput, ReductionData.toPrincipalCVPInstance,
      S.reductionDataCubic.d_power_two]
  rw [and_iff_right hw] at hc
  have hd := FixedFast.dimension_independent m ts
  have hg := FixedFast.generator_independent m ts
  have ht : (Fast.compile S).2.2.1.length = FixedFast.dimension m := by
    rw [hw.2.2, hd]
  change _ ↔ _ ∧ _
  rw [and_iff_right ht]
  simpa only [S, hd, hg, fixedGen] using hc

theorem x3cToFixedCVPP_correct (x : X3CList) :
    x ∈ X3CLang ↔ x3cToFixedCVPP x ∈ FixedCVPP := by
  by_cases hw : x.WellFormed
  · rw [x3cToFixedCVPP, ite_eq_left ((X3CList.wellFormedCheck_eq x).mpr hw)]
    exact (and_iff_right hw).trans
      ((FixedFast.system_correct x hw).symm.trans (fixed_compile_correct _ _))
  · have hc : X3CList.wellFormedCheck x ≠ true :=
      fun h => hw ((X3CList.wellFormedCheck_eq x).mp h)
    simp [x3cToFixedCVPP, hc, X3CLang, hw, fixedNoInput_not_mem]

attribute [local irreducible] FixedFast.system Fast.compile

theorem poly_x3cToFixedCVPP : ComputableTidilyInPolyTime
    x3cToFixedCVPP encX3C encFixedCVPP := by
  have hm : ComputableTidilyInPolyTime (fun x : X3CList => 3*x.1) encX3C encUnary :=
    unary_mul.comp ((const 3).prod (fst encUnary (encList encX3CTriple)))
  have hs : ComputableTidilyInPolyTime (fun x : X3CList => FixedFast.system (3*x.1) x.2)
      encX3C encMasked := FixedFast.poly_system.comp
        (hm.prod (snd encUnary (encList encX3CTriple)))
  have hc : ComputableTidilyInPolyTime
      (fun x : X3CList => Fast.compile (FixedFast.system (3*x.1) x.2)) encX3C encCVP :=
    Fast.poly_compile.comp hs
  unfold x3cToFixedCVPP
  exact X3CList.poly_wellFormedCheck.ite' (hm.prod hc.snd'.snd') (const fixedNoInput)

theorem polyTimeReducible_X3C_FixedCVPP :
    PolyTimeReducible encX3C encFixedCVPP X3CLang FixedCVPP :=
  ⟨x3cToFixedCVPP, poly_x3cToFixedCVPP, x3cToFixedCVPP_correct⟩

theorem fixedCVPP_npHard : NPHard encFixedCVPP FixedCVPP :=
  x3c_npHard.trans polyTimeReducible_X3C_FixedCVPP

end Hardness
