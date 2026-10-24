module

public import Power2ModuleSVP.SeedGeometry
public import Mathlib.Order.Interval.Set.OrdConnectedComponent
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
Closed polynomial sublevel components for `lem:seed-intervals`. The proof
counts arbitrary finite selections of distinct order-connected components
using strict outside separators, then deduces that the component section is
finite. Compact real components supply their closed interval endpoints.
No squarefreeness, numerical root isolation, or open-threshold convention is
assumed; isolated tangencies remain components.
-/

@[expose] public section

namespace Power2ModuleSVP

open Polynomial Set

noncomputable section

private theorem polynomial_separated_sublevel_points_bound
    (p : ℝ[X]) {τ : ℝ} (hτ : 0 ≤ τ)
    (ha : τ < |p.eval (-1)|) (hb : τ < |p.eval 1|)
    {k : ℕ} (x : Fin k → ℝ)
    (hx : ∀ i, -1 < x i ∧ x i < 1 ∧ |p.eval (x i)| ≤ τ)
    (hgaps : ∀ i : Fin (k - 1), ∃ y : ℝ,
      x ⟨i.val, by omega⟩ < y ∧ y < x ⟨i.val + 1, by omega⟩ ∧ τ < |p.eval y|) :
    k ≤ p.natDegree := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ n =>
    have hgap : ∀ i : Fin n, ∃ y : ℝ,
        x i.castSucc < y ∧ y < x i.succ ∧ τ < |p.eval y| := by
      intro i
      obtain ⟨y, h₁, h₂, h₃⟩ := hgaps ⟨i.val, by simpa only [Nat.add_sub_cancel] using i.isLt⟩
      exact ⟨y, h₁, h₂, h₃⟩
    choose gap hgl hgr hgv using hgap
    let outer : Fin (n + 2) → ℝ := Fin.cons (-1) (Fin.snoc gap 1)
    have hl : ∀ i, outer i.castSucc < x i := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [outer] using (hx 0).1
      · simpa [outer, Fin.cons, Fin.snoc] using hgr j
    have hr : ∀ i, x i < outer i.succ := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [outer] using (hx (Fin.last n)).2.1
      · simpa [outer] using hgl j
    have ho : ∀ i, τ < |p.eval (outer i)| := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [outer] using ha
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa [outer] using hb
        · simpa [outer] using hgv j
    exact polynomial_sublevel_islands_bound p hτ (n + 1) x outer
      (Fin.strictMono_iff_lt_succ.mpr fun i => (hl i).trans (hr i))
      hl hr (fun i => (hx i).2.2) ho

/-- Order-connected components of a closed subset of the real line are closed. -/
theorem seed_isClosed_ordConnectedComponent {s : Set ℝ} (hs : IsClosed s) (x : ℝ) :
    IsClosed (ordConnectedComponent s x) := by
  by_cases hx : x ∈ s
  · have hc : IsPreconnected (ordConnectedComponent s x) :=
      Set.OrdConnected.isPreconnected inferInstance
    let : Set.OrdConnected (closure (ordConnectedComponent s x)) := hc.closure.ordConnected
    have hsub : closure (ordConnectedComponent s x) ⊆ s :=
      closure_minimal ordConnectedComponent_subset hs
    have hself : x ∈ closure (ordConnectedComponent s x) :=
      subset_closure (self_mem_ordConnectedComponent.mpr hx)
    exact closure_eq_iff_isClosed.mp
      ((subset_ordConnectedComponent hself hsub).antisymm subset_closure)
  · rw [ordConnectedComponent_eq_empty.mpr hx]
    exact isClosed_empty

/-- The closed sublevel set has a finite order-connected section, with at
most one representative for each degree of the polynomial. -/
theorem polynomial_sublevel_section_finite (p : ℝ[X]) {τ : ℝ} (hτ : 0 ≤ τ)
    (ha : τ < |p.eval (-1)|) (hb : τ < |p.eval 1|) :
    let K := Set.Icc (-1 : ℝ) 1 ∩ {x : ℝ | |p.eval x| ≤ τ}
    K.ordConnectedSection.Finite ∧ K.ordConnectedSection.ncard ≤ p.natDegree := by
  classical
  intro K
  have hxmem {x : ℝ} (hx : x ∈ K.ordConnectedSection) :
      -1 < x ∧ x < 1 ∧ |p.eval x| ≤ τ := by
    have hxK := ordConnectedSection_subset hx
    have hl : -1 < x := by
      apply lt_of_le_of_ne hxK.1.1
      intro he
      have hv := hxK.2
      rw [← he] at hv
      change |p.eval (-1)| ≤ τ at hv
      linarith
    have hr : x < 1 := by
      apply lt_of_le_of_ne hxK.1.2
      intro he
      have hv := hxK.2
      rw [he] at hv
      change |p.eval 1| ≤ τ at hv
      linarith
    exact ⟨hl, hr, hxK.2⟩
  have hfinset : ∀ t : Finset ℝ, (↑t : Set ℝ) ⊆ K.ordConnectedSection →
      t.card ≤ p.natDegree := by
    intro t ht
    let x := t.orderEmbOfFin rfl
    have hx : ∀ i, -1 < x i ∧ x i < 1 ∧ |p.eval (x i)| ≤ τ :=
      fun i => hxmem (ht (t.orderEmbOfFin_mem rfl i))
    apply polynomial_separated_sublevel_points_bound p hτ ha hb x hx
    intro i
    let j : Fin t.card := ⟨i.val, by omega⟩
    let l : Fin t.card := ⟨i.val + 1, by omega⟩
    have hj : x j ∈ K.ordConnectedSection := ht (t.orderEmbOfFin_mem rfl j)
    have hl : x l ∈ K.ordConnectedSection := ht (t.orderEmbOfFin_mem rfl l)
    have hjl : x j < x l := x.strictMono (by simp [j, l])
    have hnot : ¬ Set.uIcc (x j) (x l) ⊆ K := by
      intro hsub
      exact hjl.ne (eq_of_mem_ordConnectedSection_of_uIcc_subset hj hl hsub)
    obtain ⟨y, hy, hyK⟩ := Set.not_subset.mp hnot
    rw [Set.uIcc_of_le hjl.le] at hy
    have hyl : x j < y := by
      apply lt_of_le_of_ne hy.1
      intro he
      apply hyK
      rw [← he]
      exact ordConnectedSection_subset hj
    have hyr : y < x l := by
      apply lt_of_le_of_ne hy.2
      intro he
      apply hyK
      rw [he]
      exact ordConnectedSection_subset hl
    have hybound : y ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨((hx j).1.trans hyl).le, (hyr.trans (hx l).2.1).le⟩
    have hv : τ < |p.eval y| := by
      by_contra h
      exact hyK ⟨hybound, le_of_not_gt h⟩
    exact ⟨y, hyl, hyr, hv⟩
  have hfinite : K.ordConnectedSection.Finite := by
    by_contra h
    have hinf : K.ordConnectedSection.Infinite := h
    obtain ⟨t, ht, hcard⟩ := hinf.exists_subset_card_eq (p.natDegree + 1)
    have hc := hfinset t ht
    omega
  refine ⟨hfinite, ?_⟩
  have hc := hfinset hfinite.toFinset (by simp)
  simpa [← Set.ncard_eq_toFinset_card] using hc


/-- Closed polynomial sublevel sets have at most degree-many disjoint
closed interval components. Singleton components are retained. -/
theorem polynomialSublevelComponentsHypothesis_holds :
    PolynomialSublevelComponentsHypothesis := by
  classical
  constructor
  intro p τ hτ ha hb
  let K := Set.Icc (-1 : ℝ) 1 ∩ {x : ℝ | |p.eval x| ≤ τ}
  have hsection := polynomial_sublevel_section_finite p hτ.le ha hb
  change K.ordConnectedSection.Finite ∧ K.ordConnectedSection.ncard ≤ p.natDegree at hsection
  let t : Finset ℝ := hsection.1.toFinset
  let x := t.orderEmbOfFin rfl
  have hxsection (i : Fin t.card) : x i ∈ K.ordConnectedSection := by
    have hxmem : x i ∈ t := t.orderEmbOfFin_mem rfl i
    exact hsection.1.mem_toFinset.mp hxmem
  have hxK (i : Fin t.card) : x i ∈ K := ordConnectedSection_subset (hxsection i)
  have hKclosed : IsClosed K :=
    isClosed_Icc.inter (isClosed_le p.continuous.abs continuous_const)
  have hstrict {z : ℝ} (hz : z ∈ K) : -1 < z ∧ z < 1 := by
    constructor
    · apply lt_of_le_of_ne hz.1.1
      intro he
      have hv : |p.eval z| ≤ τ := hz.2
      rw [← he] at hv
      linarith
    · apply lt_of_le_of_ne hz.1.2
      intro he
      have hv : |p.eval z| ≤ τ := hz.2
      rw [he] at hv
      linarith
  let component (i : Fin t.card) := ordConnectedComponent K (x i)
  have hsub (i : Fin t.card) : component i ⊆ K := ordConnectedComponent_subset
  have hself (i : Fin t.card) : x i ∈ component i :=
    self_mem_ordConnectedComponent.mpr (hxK i)
  have hnonempty (i : Fin t.card) : (component i).Nonempty := ⟨x i, hself i⟩
  have hbelow (i : Fin t.card) : BddBelow (component i) :=
    ⟨-1, fun _ hz => (hsub i hz).1.1⟩
  have habove (i : Fin t.card) : BddAbove (component i) :=
    ⟨1, fun _ hz => (hsub i hz).1.2⟩
  have hclosed (i : Fin t.card) : IsClosed (component i) :=
    seed_isClosed_ordConnectedComponent hKclosed (x i)
  let left (i : Fin t.card) : ℝ := sInf (component i)
  let right (i : Fin t.card) : ℝ := sSup (component i)
  have hmin (i : Fin t.card) : left i ∈ component i :=
    (hclosed i).csInf_mem (hnonempty i) (hbelow i)
  have hmax (i : Fin t.card) : right i ∈ component i :=
    (hclosed i).csSup_mem (hnonempty i) (habove i)
  have hlr (i : Fin t.card) : left i ≤ right i := csInf_le (hbelow i) (hmax i)
  have heq (i : Fin t.card) : component i = Set.Icc (left i) (right i) :=
    eq_Icc_csInf_csSup_of_connected_bdd_closed
      ⟨hnonempty i, Set.OrdConnected.isPreconnected inferInstance⟩
      (hbelow i) (habove i) (hclosed i)
  refine ⟨t.card, left, right, ?_, ?_, ?_, ?_⟩
  · simpa [t, ← Set.ncard_eq_toFinset_card] using hsection.2
  · intro i
    exact ⟨(hstrict (hsub i (hmin i))).1, hlr i, (hstrict (hsub i (hmax i))).2⟩
  · have hsep (i j : Fin t.card) (hij : i < j) : right i < left j := by
      by_contra h
      have hcross : left j ≤ right i := le_of_not_gt h
      have hxi : x i ∈ Set.Icc (left i) (right i) := by rw [← heq]; exact hself i
      have hxj : x j ∈ Set.Icc (left j) (right j) := by rw [← heq]; exact hself j
      have hxij : x i < x j := x.strictMono hij
      let z : ℝ := max (left i) (left j)
      have hzi : z ∈ component i := by
        rw [heq]
        exact ⟨le_max_left _ _, max_le (hlr i) hcross⟩
      have hzj : z ∈ component j := by
        rw [heq]
        exact ⟨le_max_right _ _, max_le (hxi.1.trans (hxij.le.trans hxj.2)) (hlr j)⟩
      have hxy : Set.uIcc (x i) (x j) ⊆ K :=
        mem_ordConnectedComponent_trans hzi (mem_ordConnectedComponent_comm.mpr hzj)
      exact hxij.ne (eq_of_mem_ordConnectedSection_of_uIcc_subset (hxsection i) (hxsection j) hxy)
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact Or.inl (hsep i j h)
    · exact Or.inr (hsep j i h)
  · intro z hz
    constructor
    · intro hpz
      have hzK : z ∈ K := ⟨hz, hpz⟩
      let rep := ordConnectedProj K ⟨z, hzK⟩
      have hrep : rep ∈ t := by
        have : rep ∈ K.ordConnectedSection := ⟨⟨z, hzK⟩, rfl⟩
        simpa [t] using this
      have hrange : rep ∈ Set.range x := by
        rw [Finset.range_orderEmbOfFin]
        exact hrep
      obtain ⟨i, hi⟩ := hrange
      refine ⟨i, ?_⟩
      rw [← heq]
      change z ∈ ordConnectedComponent K (x i)
      rw [hi]
      exact mem_ordConnectedComponent_ordConnectedProj K ⟨z, hzK⟩
    · rintro ⟨i, hi⟩
      have hzc : z ∈ component i := by rw [heq]; exact hi
      exact (hsub i hzc).2

end

end Power2ModuleSVP
