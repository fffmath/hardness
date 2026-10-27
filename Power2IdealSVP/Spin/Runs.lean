import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# Integer runs of the sparse support

A finite integer support with no isolated point and no pair at distance three is a disjoint
union of dimers and trimers. This file contains the local run statements independently of the
negacyclic cut and local-field arguments.

Paper: `paper/power2-ideal-svp.txt`, Section 1.3; audit Section 7.
-/

namespace Power2IdealSVP.Spin

/-- Every occupied integer has an occupied nearest neighbour. -/
def NoIsolated (W : Finset ℤ) : Prop :=
  ∀ x ∈ W, x - 1 ∈ W ∨ x + 1 ∈ W

/-- No two occupied integers are three apart. -/
def NoDistanceThree (W : Finset ℤ) : Prop :=
  ∀ x ∈ W, x + 3 ∉ W

/-- Starts of maximal consecutive blocks in a finite integer support. -/
def runStarts (W : Finset ℤ) : Finset ℤ := W.filter fun p => p - 1 ∉ W

/-- The block starting at `p`: two points, and the third if it is occupied. -/
def runBlock (W : Finset ℤ) (p : ℤ) : Finset ℤ :=
  if p + 2 ∈ W then {p, p + 1, p + 2} else {p, p + 1}

@[simp] theorem mem_runStarts {W : Finset ℤ} {p : ℤ} :
    p ∈ runStarts W ↔ p ∈ W ∧ p - 1 ∉ W := by
  simp [runStarts]

/-- A run start has a second occupied point because isolated points are excluded. -/
theorem runStart_succ_mem {W : Finset ℤ} (hW : NoIsolated W) {p : ℤ}
    (hp : p ∈ runStarts W) : p + 1 ∈ W := by
  obtain ⟨hp, hp'⟩ := mem_runStarts.mp hp
  exact (hW p hp).resolve_left hp'

/-- A block has exactly two or three occupied points and is contained in the support. -/
theorem runBlock_subset {W : Finset ℤ} (hW : NoIsolated W) {p : ℤ}
    (hp : p ∈ runStarts W) : runBlock W p ⊆ W := by
  have hp0 := (mem_runStarts.mp hp).1
  have hp1 := runStart_succ_mem hW hp
  unfold runBlock
  split_ifs with hp2 <;> simp_all only [Finset.insert_subset_iff,
    Finset.singleton_subset_iff, and_self]

/-- The third successor of a run start is empty. -/
theorem runStart_add_three_not_mem {W : Finset ℤ} (hW : NoDistanceThree W) {p : ℤ}
    (hp : p ∈ runStarts W) : p + 3 ∉ W := hW p (mem_runStarts.mp hp).1

/-- Every occupied point lies in a block whose start is at most two positions to its left. -/
theorem exists_runStart {W : Finset ℤ} (_hW : NoIsolated W)
    (h3 : NoDistanceThree W) {x : ℤ} (hx : x ∈ W) :
    ∃ p ∈ runStarts W, x ∈ runBlock W p := by
  by_cases hm1 : x - 1 ∈ W
  · by_cases hm2 : x - 2 ∈ W
    · have hm3 : x - 3 ∉ W := by
        intro hm3
        have := h3 (x - 3) hm3
        apply this
        convert hx using 1; ring
      refine ⟨x - 2, mem_runStarts.mpr ⟨hm2, ?_⟩, ?_⟩
      · simpa only [show x - 2 - 1 = x - 3 by omega] using hm3
      · have he : x - 2 + 2 = x := by ring
        simp [runBlock, he, hx]
    · refine ⟨x - 1, mem_runStarts.mpr ⟨hm1, ?_⟩, ?_⟩
      · simpa only [show x - 1 - 1 = x - 2 by omega] using hm2
      · have he : x - 1 + 1 = x := by ring
        simp only [runBlock]
        split_ifs <;> simp [he]
  · refine ⟨x, mem_runStarts.mpr ⟨hx, hm1⟩, ?_⟩
    simp only [runBlock]
    split_ifs <;> simp

/-- Membership in a run block gives the three possible integer positions. -/
theorem mem_runBlock_cases {W : Finset ℤ} {p x : ℤ} (hx : x ∈ runBlock W p) :
    x = p ∨ x = p + 1 ∨ x = p + 2 := by
  unfold runBlock at hx
  split_ifs at hx <;> simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  · exact hx
  · exact hx.elim Or.inl (fun h => Or.inr (Or.inl h))

/-- Different run starts are separated by at least five integer steps. -/
theorem runStarts_separated {W : Finset ℤ} (hW : NoIsolated W)
    (h3 : NoDistanceThree W) {p q : ℤ} (hp : p ∈ runStarts W)
    (hq : q ∈ runStarts W) (hpq : p < q) : p + 5 ≤ q := by
  have hp0 := (mem_runStarts.mp hp).1
  have hp1 := runStart_succ_mem hW hp
  obtain ⟨hq0, hqprev⟩ := mem_runStarts.mp hq
  have hq1 := runStart_succ_mem hW (mem_runStarts.mpr ⟨hq0, hqprev⟩)
  have hn1 : q ≠ p + 1 := by
    intro he
    apply hqprev
    simpa only [show q - 1 = p by omega] using hp0
  have hn2 : q ≠ p + 2 := by
    intro he
    apply hqprev
    simpa only [show q - 1 = p + 1 by omega] using hp1
  have hn3 : q ≠ p + 3 := by
    intro he
    exact h3 p hp0 (he ▸ hq0)
  have hn4 : q ≠ p + 4 := by
    intro he
    apply h3 (p + 1) hp1
    convert hq0 using 1; omega
  omega

/-- A trimer forces the following run to start at least six steps later. -/
theorem trimer_next_separated {W : Finset ℤ} (hW : NoIsolated W)
    (h3 : NoDistanceThree W) {p q : ℤ} (hp : p ∈ runStarts W)
    (hq : q ∈ runStarts W) (hpq : p < q) (hp2 : p + 2 ∈ W) : p + 6 ≤ q := by
  have hsep := runStarts_separated hW h3 hp hq hpq
  have hn : q ≠ p + 5 := by
    intro he
    apply h3 (p + 2) hp2
    convert (mem_runStarts.mp hq).1 using 1; omega
  omega

/-- Blocks at different starts do not overlap. -/
theorem runBlocks_disjoint {W : Finset ℤ} (hW : NoIsolated W)
    (h3 : NoDistanceThree W) {p q : ℤ} (hp : p ∈ runStarts W)
    (hq : q ∈ runStarts W) (hpq : p ≠ q) :
    Disjoint (runBlock W p) (runBlock W q) := by
  apply Finset.disjoint_left.mpr
  intro x hxp hxq
  have hxp := mem_runBlock_cases hxp
  have hxq := mem_runBlock_cases hxq
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · have := runStarts_separated hW h3 hp hq hlt
    rcases hxp with rfl | rfl | rfl <;> omega
  · have := runStarts_separated hW h3 hq hp hgt
    rcases hxp with rfl | rfl | rfl <;> omega

/-- The run blocks partition the entire integer support. -/
theorem biUnion_runBlocks {W : Finset ℤ} (hW : NoIsolated W)
    (h3 : NoDistanceThree W) :
    (runStarts W).biUnion (runBlock W) = W := by
  ext x
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨p, hp, hxp⟩
    exact runBlock_subset hW hp hxp
  · exact exists_runStart hW h3

/-- The size of a block distinguishes dimers and trimers. -/
theorem card_runBlock (W : Finset ℤ) (p : ℤ) :
    (runBlock W p).card = if p + 2 ∈ W then 3 else 2 := by
  unfold runBlock
  split_ifs <;> simp [show p ≠ p + 1 by omega, show p ≠ p + 2 by omega,
    show p + 1 ≠ p + 2 by omega]

/-- The run partition computes the support cardinality by summing block sizes. -/
theorem card_eq_sum_runBlocks {W : Finset ℤ} (hW : NoIsolated W)
    (h3 : NoDistanceThree W) : W.card = ∑ p ∈ runStarts W, (runBlock W p).card := by
  calc
    W.card = ((runStarts W).biUnion (runBlock W)).card := by
      rw [biUnion_runBlocks hW h3]
    _ = _ := Finset.card_biUnion (fun p hp q hq hpq =>
      runBlocks_disjoint hW h3 hp hq hpq)

/-- An odd support with no isolated points has at least one trimer. -/
theorem exists_trimer {W : Finset ℤ} (hW : NoIsolated W)
    (h3 : NoDistanceThree W) (hodd : Odd W.card) :
    ∃ t ∈ runStarts W, t + 2 ∈ W := by
  by_contra h
  push Not at h
  have heven : W.card = 2 * (runStarts W).card := by
    rw [card_eq_sum_runBlocks hW h3]
    calc
      _ = ∑ _p ∈ runStarts W, 2 := Finset.sum_congr rfl (fun p hp => by
        rw [card_runBlock, ite_eq_right (h p hp)])
      _ = _ := by simp [Nat.mul_comm]
  obtain ⟨k, hk⟩ := hodd
  omega

end Power2IdealSVP.Spin
