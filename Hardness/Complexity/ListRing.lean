import Hardness.Complexity.Problem
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-! # List-level negacyclic multiplication and certificate checking -/
namespace Hardness
open Turing.MultiTapeTM

/-- The coefficient at `r`, computed by two finite list loops. -/
def negacyclicCoeff (d : ℕ) (g q : List ℤ) (r : ℕ) : ℤ :=
  ((List.range d).map fun i => ((List.range d).map fun j =>
    if (i + j) % d = r then
      (if i + j < d then 1 else -1) * g.getD i 0 * q.getD j 0 else 0).sum).sum

def negacyclicMul (d : ℕ) (g q : List ℤ) : List ℤ :=
  (List.range d).map (negacyclicCoeff d g q)

@[simp] theorem length_negacyclicMul (d : ℕ) (g q : List ℤ) :
    (negacyclicMul d g q).length = d := by simp [negacyclicMul]

theorem list_sum_range (d : ℕ) (f : ℕ → ℤ) :
    ((List.range d).map f).sum = ∑ i ∈ Finset.range d, f i := by
  rw [← List.sum_toFinset f List.nodup_range, List.toFinset_range]

theorem negacyclicCoeff_eq (d : ℕ) (g q : List ℤ) (r : Fin d) :
    negacyclicCoeff d g q r.val = Cyclotomic.mul (ofList g) (ofList q) r := by
  unfold negacyclicCoeff Cyclotomic.mul ofList
  simp only [list_sum_range, Finset.sum_range]

/-- The executable list program is the existing cyclotomic multiplication. -/
theorem ofList_negacyclicMul (d : ℕ) (g q : List ℤ) :
    ofList (d := d) (negacyclicMul d g q) = Cyclotomic.mul (ofList g) (ofList q) := by
  funext r
  simp only [ofList, negacyclicMul, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range, r.isLt, ↓reduceIte, Option.map_some, Option.getD_some]
  exact negacyclicCoeff_eq d g q r

def listSqDistance (d : ℕ) (v t : List ℤ) : ℤ :=
  ((List.range d).map fun i => (v.getD i 0 - t.getD i 0)^2).sum

theorem listSqDistance_eq (d : ℕ) (v t : List ℤ) :
    listSqDistance d v t = sqNorm (ofList (d := d) v - ofList t) := by
  unfold listSqDistance sqNorm ofList
  simp only [list_sum_range, Pi.sub_apply, Finset.sum_range]

/-- A bounded unary search tests whether the dimension is a power of two. -/
def cvpWellFormedCheck (x : CVPInput) : Bool :=
  ((List.range (x.1 + 1)).any fun k => decide (x.1 = 2^k)) &&
    decide (x.2.1.length = x.1) && decide (x.2.2.1.length = x.1)

theorem cvpWellFormedCheck_eq (x : CVPInput) :
    cvpWellFormedCheck x = true ↔ x.WellFormed := by
  simp only [cvpWellFormedCheck, Bool.and_eq_true, List.any_eq_true,
    List.mem_range, decide_eq_true_eq, CVPInput.WellFormed]
  constructor
  · rintro ⟨⟨⟨k, _, hk⟩, hg⟩, ht⟩
    exact ⟨⟨k, hk⟩, hg, ht⟩
  · rintro ⟨⟨k, hk⟩, hg, ht⟩
    refine ⟨⟨⟨k, ?_, hk⟩, hg⟩, ht⟩
    have := Nat.lt_two_pow_self (n := k)
    omega

/-- A total checker; certificates contain exactly `d` signed binary integers. -/
def cvpCheck (p : CVPInput × List ℤ) : Bool :=
  cvpWellFormedCheck p.1 && decide (p.2.length = p.1.1) &&
    decide (listSqDistance p.1.1 (negacyclicMul p.1.1 p.1.2.1 p.2) p.1.2.2.1 ≤ p.1.2.2.2)

theorem cvpCheck_eq (x : CVPInput) (q : List ℤ) : cvpCheck (x, q) = true ↔
    x.WellFormed ∧ q.length = x.1 ∧
      sqNorm (Cyclotomic.mul (ofList (d := x.1) x.2.1) (ofList q) - ofList x.2.2.1) ≤ x.2.2.2 := by
  simp only [cvpCheck, Bool.and_eq_true, cvpWellFormedCheck_eq, decide_eq_true_eq,
    listSqDistance_eq, ofList_negacyclicMul, and_assoc]

theorem principalCVP_iff_exists_check (x : CVPInput) :
    x ∈ PrincipalCVP ↔ ∃ q : List ℤ, cvpCheck (x, q) = true := by
  constructor
  · rintro ⟨hw, q, hq⟩
    exact ⟨toList q, (cvpCheck_eq x _).mpr ⟨hw, length_toList q, by simpa using hq⟩⟩
  · rintro ⟨q, hq⟩
    obtain ⟨hw, _, hq⟩ := (cvpCheck_eq x q).mp hq
    exact ⟨hw, ofList q, hq⟩

end Hardness
