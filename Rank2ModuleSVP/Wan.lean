import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Wan power-sum estimates

The explicit external point-count hypothesis from paper v2 Proposition 2.3,
with finite union bounds for collision-free power-sum solutions.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Rank2ModuleSVP
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The indices `1 ≤ j < k`, avoiding a spurious zeroth power-sum equation. -/
abbrev PositiveMoment (k : ℕ) := {j : Fin k // 0 < j.val}

/-- Ordered solutions of the prescribed positive power sums. -/
def powerSumSolutions (q k m : ℕ) [NeZero q]
    (b : PositiveMoment k → ZMod q) : Finset (Fin m → ZMod q) :=
  Finset.univ.filter fun z => ∀ j, ∑ i, z i ^ j.val.val = b j

/-- Wan's estimates, exactly parts (i), (ii), and (iii) of
`prop:wan-power-sum-estimates`. In particular half-integer exponents are real
exponents, rather than truncated natural-number division. This is a proposition
passed explicitly to subsequent results, not an axiom or an instance. -/
def WanPowerSumEstimates : Prop :=
  ∀ (q : ℕ) (hq : q.Prime),
    letI : NeZero q := ⟨hq.ne_zero⟩
    ∀ k m : ℕ, 2 ≤ k → k ≤ m - 2 → m - 2 < q - 2 →
    ∀ b : PositiveMoment k → ZMod q,
      |((powerSumSolutions q k m b).card : ℝ) - (q : ℝ) ^ (m - k + 1)| ≤
          (1 / 2 : ℝ) * (2 * k : ℝ) ^ m * (q : ℝ) ^ (((m - k + 2 : ℕ) : ℝ) / 2) ∧
      (∀ i l : Fin m, i ≠ l →
        |(((powerSumSolutions q k m b).filter fun z => z i = z l).card : ℝ) -
            (q : ℝ) ^ (m - k)| ≤
          (1 / 2 : ℝ) * (2 * k : ℝ) ^ (m - 1) * (q : ℝ) ^ (((m - k + 2 : ℕ) : ℝ) / 2)) ∧
      (∀ (i : Fin m) (a : ZMod q),
        |(((powerSumSolutions q k m b).filter fun z => z i = a).card : ℝ) -
            (q : ℝ) ^ (m - k)| ≤
          (1 / 2 : ℝ) * (2 * k : ℝ) ^ (m - 1) * (q : ℝ) ^ (((m - k + 1 : ℕ) : ℝ) / 2))

/-- Finite union bound, retaining an explicit index set for the error budget. -/
theorem card_filter_exists_le {α ι : Type*} (S : Finset α) (I : Finset ι) (bad : ι → α → Prop) :
    (S.filter fun x => ∃ i ∈ I, bad i x).card ≤
      ∑ i ∈ I, (S.filter (bad i)).card := by
  classical
  have he : (S.filter fun x => ∃ i ∈ I, bad i x) =
      I.biUnion (fun i => S.filter (bad i)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    aesop
  rw [he]
  exact Finset.card_biUnion_le

/-- If the finite union has smaller cardinality than the sample space, a
sample avoiding every event exists. -/
theorem exists_avoiding_of_sum_lt {α ι : Type*} (S : Finset α) (I : Finset ι) (bad : ι → α → Prop)
    (hbudget : (∑ i ∈ I, (S.filter (bad i)).card) < S.card) :
    ∃ x ∈ S, ∀ i ∈ I, ¬ bad i x := by
  classical
  have hlt : (S.filter fun x => ∃ i ∈ I, bad i x).card < S.card :=
    (card_filter_exists_le S I bad).trans_lt hbudget
  have hnot : ¬ S ⊆ S.filter (fun x => ∃ i ∈ I, bad i x) := by
    intro hh
    exact (not_lt_of_ge (Finset.card_le_card hh)) hlt
  obtain ⟨x, hx, hgood⟩ := Finset.not_subset.mp hnot
  refine ⟨x, hx, ?_⟩
  intro i hi hbad
  exact hgood (Finset.mem_filter.mpr ⟨hx, i, hi, hbad⟩)

/-- A lower bound on the retained set, before making any estimate on errors. -/
theorem card_le_good_add_errors {α ι : Type*} (S : Finset α) (I : Finset ι) (bad : ι → α → Prop) :
    S.card ≤ (S.filter fun x => ∀ i ∈ I, ¬ bad i x).card +
      ∑ i ∈ I, (S.filter (bad i)).card := by
  classical
  have he : S = (S.filter fun x => ∀ i ∈ I, ¬ bad i x) ∪
      (S.filter fun x => ∃ i ∈ I, bad i x) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      by_cases hh : ∃ i ∈ I, bad i x
      · exact Or.inr ⟨hx, hh⟩
      · exact Or.inl ⟨hx, by simpa using hh⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  calc
    S.card = ((S.filter fun x => ∀ i ∈ I, ¬ bad i x) ∪
        (S.filter fun x => ∃ i ∈ I, bad i x)).card := congrArg Finset.card he
    _ ≤ _ := (Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (card_filter_exists_le S I bad) _)

/-- Tuples with neither collisions nor an entry in the prescribed position set. -/
def goodPowerSumSolutions (q k m : ℕ) [NeZero q]
    (b : PositiveMoment k → ZMod q) (P : Finset (ZMod q)) :
    Finset (Fin m → ZMod q) :=
  (powerSumSolutions q k m b).filter fun z =>
    Function.Injective z ∧ ∀ i, z i ∉ P

/-- Exact exclusion bound. The collision sum uses ordered pairs; this harmless
factor of two avoids making a choice of ordering on the tuple indices. -/
theorem card_powerSumSolutions_le_good_add (q k m : ℕ) [NeZero q]
    (b : PositiveMoment k → ZMod q) (P : Finset (ZMod q)) :
    (powerSumSolutions q k m b).card ≤ (goodPowerSumSolutions q k m b P).card +
      (∑ p ∈ (Finset.univ.filter fun p : Fin m × Fin m => p.1 ≠ p.2),
        ((powerSumSolutions q k m b).filter fun z => z p.1 = z p.2).card) +
      ∑ p ∈ (Finset.univ : Finset (Fin m)).product P,
        ((powerSumSolutions q k m b).filter fun z => z p.1 = p.2).card := by
  classical
  let S := powerSumSolutions q k m b
  let I := (Finset.univ.filter fun p : Fin m × Fin m => p.1 ≠ p.2)
  let J := (Finset.univ : Finset (Fin m)).product P
  let bad : (Fin m × Fin m) ⊕ (Fin m × ZMod q) → (Fin m → ZMod q) → Prop :=
    fun e z => match e with
    | .inl p => z p.1 = z p.2
    | .inr p => z p.1 = p.2
  have hh := card_le_good_add_errors S (I.disjSum J) bad
  have he : (S.filter fun z => ∀ e ∈ I.disjSum J, ¬bad e z) =
      goodPowerSumSolutions q k m b P := by
    ext z
    simp only [Finset.mem_filter, goodPowerSumSolutions]
    constructor
    · rintro ⟨hz, hh⟩
      refine ⟨hz, ?_, ?_⟩
      · intro i l hil
        by_contra hne
        exact hh (.inl (i, l)) (by simp [I, hne]) hil
      · intro i hi
        exact hh (.inr (i, z i)) (by simp [J, hi]) rfl
    · rintro ⟨hz, hinj, hav⟩
      refine ⟨hz, ?_⟩
      intro e he
      cases e with
      | inl p =>
        have hp : p.1 ≠ p.2 := by simpa [I] using he
        exact fun hh => hp (hinj hh)
      | inr p =>
        have hp : p.2 ∈ P := by simpa [J] using he
        exact fun hh => hav p.1 (hh ▸ hp)
  rw [← he]
  simpa [S, I, J, bad, Finset.sum_disjSum, add_assoc] using hh

/-- Main term and explicit errors; real exponents include the half powers. -/
def wanMain (q k m : ℕ) : ℝ := (q : ℝ) ^ (m - k + 1)
/-- Error term for the unrestricted power-sum count in Proposition 2.3(i). -/
def wanError (q k m : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (2 * k : ℝ) ^ m * (q : ℝ) ^ (((m - k + 2 : ℕ) : ℝ) / 2)
/-- Error term for a prescribed collision in Proposition 2.3(ii). -/
def wanCollisionError (q k m : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (2 * k : ℝ) ^ (m - 1) * (q : ℝ) ^ (((m - k + 2 : ℕ) : ℝ) / 2)
/-- Error term for a prescribed coordinate in Proposition 2.3(iii). -/
def wanCoordinateError (q k m : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (2 * k : ℝ) ^ (m - 1) * (q : ℝ) ^ (((m - k + 1 : ℕ) : ℝ) / 2)

/-- Explicit, uniform finite version of the counting argument in
`uniform-completions`, prior to estimating the errors asymptotically. -/
theorem wan_good_count_bounds (hWan : WanPowerSumEstimates)
    (q : ℕ) (hq : q.Prime) (k m : ℕ) (hk : 2 ≤ k)
    (hkm : k ≤ m - 2) (hmq : m - 2 < q - 2) :
    letI : NeZero q := ⟨hq.ne_zero⟩
    ∀ (b : PositiveMoment k → ZMod q) (P : Finset (ZMod q)),
    wanMain q k m - wanError q k m -
        ((m : ℝ) ^ 2 * ((q : ℝ) ^ (m - k) + wanCollisionError q k m) +
         (m : ℝ) * P.card * ((q : ℝ) ^ (m - k) + wanCoordinateError q k m)) ≤
        (goodPowerSumSolutions q k m b P).card ∧
    ((goodPowerSumSolutions q k m b P).card : ℝ) ≤
        wanMain q k m + wanError q k m := by
  let : NeZero q := ⟨hq.ne_zero⟩
  intro b P
  obtain ⟨hA, hC, hE⟩ := hWan q hq k m hk hkm hmq b
  let S := powerSumSolutions q k m b
  let I := Finset.univ.filter fun p : Fin m × Fin m => p.1 ≠ p.2
  let J := (Finset.univ : Finset (Fin m)).product P
  have hC' (p : Fin m × Fin m) (hp : p ∈ I) :
      (((S.filter fun z => z p.1 = z p.2).card : ℕ) : ℝ) ≤
        (q : ℝ) ^ (m - k) + wanCollisionError q k m := by
    have hh := (abs_le.mp (hC p.1 p.2 (Finset.mem_filter.mp hp).2)).2
    change _ ≤ _ + (1 / 2 : ℝ) * (2 * k : ℝ) ^ (m - 1) *
      (q : ℝ) ^ (((m - k + 2 : ℕ) : ℝ) / 2)
    linarith
  have hE' (p : Fin m × ZMod q) :
      (((S.filter fun z => z p.1 = p.2).card : ℕ) : ℝ) ≤
        (q : ℝ) ^ (m - k) + wanCoordinateError q k m := by
    have hh := (abs_le.mp (hE p.1 p.2)).2
    change _ ≤ _ + (1 / 2 : ℝ) * (2 * k : ℝ) ^ (m - 1) *
      (q : ℝ) ^ (((m - k + 1 : ℕ) : ℝ) / 2)
    linarith
  have hCI : (I.card : ℝ) ≤ (m : ℝ) ^ 2 := by
    have hh := Finset.card_filter_le (Finset.univ : Finset (Fin m × Fin m))
      (fun p => p.1 ≠ p.2)
    have hn : I.card ≤ m ^ 2 := by simpa [I, pow_two] using hh
    exact_mod_cast hn
  have hcol : ((∑ p ∈ I, (S.filter fun z => z p.1 = z p.2).card : ℕ) : ℝ) ≤
      (m : ℝ) ^ 2 * ((q : ℝ) ^ (m - k) + wanCollisionError q k m) := by
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ _ ∈ I, ((q : ℝ) ^ (m - k) + wanCollisionError q k m) :=
        Finset.sum_le_sum hC'
      _ = (I.card : ℝ) * ((q : ℝ) ^ (m - k) + wanCollisionError q k m) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hCI (by unfold wanCollisionError; positivity)
  have hJ : J.card = m * P.card := by
    exact (Finset.card_product (Finset.univ : Finset (Fin m)) P).trans (by simp)
  have hent : ((∑ p ∈ J, (S.filter fun z => z p.1 = p.2).card : ℕ) : ℝ) ≤
      (m : ℝ) * P.card * ((q : ℝ) ^ (m - k) + wanCoordinateError q k m) := by
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ _ ∈ J, ((q : ℝ) ^ (m - k) + wanCoordinateError q k m) :=
        Finset.sum_le_sum (fun p _ => hE' p)
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [hJ, Nat.cast_mul]
  have hsplit := card_powerSumSolutions_le_good_add q k m b P
  have hsplit' : (S.card : ℝ) ≤ (goodPowerSumSolutions q k m b P).card +
      ((∑ p ∈ I, (S.filter fun z => z p.1 = z p.2).card : ℕ) : ℝ) +
      ((∑ p ∈ J, (S.filter fun z => z p.1 = p.2).card : ℕ) : ℝ) := by
    exact_mod_cast hsplit
  have hA' : wanMain q k m - wanError q k m ≤ (S.card : ℝ) ∧
      (S.card : ℝ) ≤ wanMain q k m + wanError q k m := by
    obtain ⟨hl, hu⟩ := abs_le.mp hA
    constructor <;> dsimp [wanMain, wanError, S] <;> linarith
  have hsub : ((goodPowerSumSolutions q k m b P).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_filter_le S
      (fun z => Function.Injective z ∧ ∀ i, z i ∉ P)
  constructor <;> linarith

end
end Rank2ModuleSVP
