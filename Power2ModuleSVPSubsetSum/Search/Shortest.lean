import Power2ModuleSVPSubsetSum.Reduction.Correctness

/-! # Mathematical content of the shortest-vector oracle reduction

Paper: `paper/power2svp-subsetsum.pdf`, Corollary 4.4.

`positiveReduce_search` proves, for every source instance and every shortest nonzero vector
of the paper's gadget, that the source is YES exactly when its norm is at most `M`, and that
the oracle answer has norm at most `2M`. Thus all its integer coefficients are bounded by `2M`.
`reduce_search_correct` also covers the total decision reduction's constant outputs.
For that map the correct universal bound is `max 1 (2M)`: its fixed NO instance has radius
zero and shortest norm one. The paper's `2M` bound applies to the gadget, whose `M` is positive.

Infrastructure survey: complexitylib DOES contain `Cslib.Complexity.WordQueryComp`,
`ComputableInPolyTimeWithOracle`, and `PWithOracle` in
`Complexity/Computability/Complexity/Classes/Oracle.lean`, and `FNP`, `FPSearch`, `TFNP`,
`SearchReducible`, and `SearchHard` in `Classes/TFNP.lean`. The latter reductions are between
search relations, not the decision-to-total-search Turing reduction in this corollary.
There is no declaration named `TuringReducible` in the surveyed checkout.

This file formalises the mathematical one-query correctness and coefficient bounds. It does
NOT claim polynomial-time Turing hardness in complexitylib: the gadget construction's
polynomial-time TM certificate is not yet available in this project, and neither the oracle
answer encoding/parser nor the oracle program's runtime is certified here. In particular the
coefficient bound alone is not a formal polynomial bound in the source encoding length.
No new oracle-machine framework is introduced.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Power2ModuleSVPSubsetSum.Search
open Power2ModuleSVP IdealCVP.Cyclotomic Reduction

/-- A shortest nonzero vector of the module, including membership and attainment. -/
def IsShortest {n : ℕ} (A B : Coeff n × Coeff n) (v : Coeff n × Coeff n) : Prop :=
  v ≠ 0 ∧ (∃ a b, moduleVector A B a b = v) ∧
    ∀ a b, moduleVector A B a b ≠ 0 → pairSup v ≤ pairSup (moduleVector A B a b)

/-- A shortest vector realizes the existing first-minimum predicate. -/
theorem IsShortest.firstMinimum {n : ℕ} {A B v : Coeff n × Coeff n}
    (hv : IsShortest A B v) : FirstMinimum A B (pairSup v) := by
  obtain ⟨a, b, hab⟩ := hv.2.1
  exact ⟨⟨a, b, hab.symm ▸ hv.1, congrArg pairSup hab⟩, hv.2.2⟩

/-- An attained first minimum supplies a shortest nonzero vector. -/
theorem exists_isShortest_of_firstMinimum {n r : ℕ} {A B : Coeff n × Coeff n}
    (hr : FirstMinimum A B r) : ∃ v, IsShortest A B v := by
  obtain ⟨a, b, hne, hn⟩ := hr.1
  exact ⟨moduleVector A B a b, hne, ⟨a, b, rfl⟩, hn.symm ▸ hr.2⟩

/-- Comparing any shortest vector to a radius decides whether there is a short vector. -/
theorem moduleYes_iff_shortest_le {n : ℕ} {A B v : Coeff n × Coeff n}
    (hv : IsShortest A B v) (M : ℕ) : ModuleYes A B M ↔ pairSup v ≤ M := by
  constructor
  · rintro ⟨a, b, hne, hn⟩
    exact (hv.2.2 a b hne).trans hn
  · intro hn
    obtain ⟨a, b, hab⟩ := hv.2.1
    exact ⟨a, b, hab.symm ▸ hv.1, hab.symm ▸ hn⟩

/-- Every source gadget admits a shortest nonzero vector. -/
theorem gadget_shortest_exists (w : List ℕ) (B : ℕ) :
    ∃ v, IsShortest (gadgetA w B) (gadgetB w B) v := by
  obtain ⟨r, hr, _⟩ := gadget_firstMinimum_exists_le_two_M w B
  exact exists_isShortest_of_firstMinimum hr

/-- Corollary 4.4's threshold test and answer bound, uniformly for every shortest answer. -/
theorem gadget_search (x : List ℕ × ℕ)
    (v : Coeff (degree x.1.length) × Coeff (degree x.1.length))
    (hv : IsShortest (gadgetA x.1 x.2) (gadgetB x.1 x.2) v) :
    (x ∈ Cslib.Complexity.SubsetSum ↔ pairSup v ≤ (gadget x.1 x.2).M) ∧
      pairSup v ≤ 2 * (gadget x.1 x.2).M := by
  exact ⟨(gadget_correct x.1 x.2).trans (moduleYes_iff_shortest_le hv _),
    gadget_firstMinimum_le_two_M x.1 x.2 _ hv.firstMinimum⟩

/-- The same one-query theorem for the actual stored output of `positiveReduce`. -/
theorem positiveReduce_search (x : List ℕ × ℕ)
    (v : Coeff (positiveReduce x.1 x.2).1.1 × Coeff (positiveReduce x.1 x.2).1.1)
    (hv : IsShortest (inputA (positiveReduce x.1 x.2))
      (inputB (positiveReduce x.1 x.2)) v) :
    (x ∈ Cslib.Complexity.SubsetSum ↔ pairSup v ≤ (positiveReduce x.1 x.2).2) ∧
      pairSup v ≤ 2 * (positiveReduce x.1 x.2).2 := by
  obtain ⟨hA, hB⟩ := positiveReduce_interpretation x.1 x.2
  change IsShortest _ _ v at hv
  change (IdealCVP.ofList _, IdealCVP.ofList _) = _ at hA hB
  rw [show inputA (positiveReduce x.1 x.2) = gadgetA x.1 x.2 from hA,
    show inputB (positiveReduce x.1 x.2) = gadgetB x.1 x.2 from hB] at hv
  exact gadget_search x v hv

/-- Each coefficient of any shortest oracle answer is bounded by `2M`. -/
theorem gadget_shortest_coeff_bound (x : List ℕ × ℕ)
    (v : Coeff (degree x.1.length) × Coeff (degree x.1.length))
    (hv : IsShortest (gadgetA x.1 x.2) (gadgetB x.1 x.2) v)
    (i : Fin (degree x.1.length)) :
    (v.1 i).natAbs ≤ 2 * (gadget x.1 x.2).M ∧
      (v.2 i).natAbs ≤ 2 * (gadget x.1 x.2).M := by
  have hn := (gadget_search x v hv).2
  exact ⟨(natAbs_le_coeffSup v.1 i).trans ((le_max_left _ _).trans hn),
    (natAbs_le_coeffSup v.2 i).trans ((le_max_right _ _).trans hn)⟩

/-- The threshold test remains correct for every output of the total decision reduction. -/
theorem reduce_search_correct (x : List ℕ × ℕ)
    (v : Coeff (reduce x).1.1 × Coeff (reduce x).1.1)
    (hv : IsShortest (inputA (reduce x)) (inputB (reduce x)) v) :
    x ∈ Cslib.Complexity.SubsetSum ↔ pairSup v ≤ (reduce x).2 := by
  rw [reduce_correct x]
  exact (and_iff_right (reduce_wellFormed x)).trans (moduleYes_iff_shortest_le hv _)

/-- For the constant identity outputs, shortest vectors have norm at most one. -/
private theorem identity_shortest_le_one
    (v : Coeff 1 × Coeff 1) (hv : IsShortest (inputA noInstance) (inputB noInstance) v) :
    pairSup v ≤ 1 := by
  have hne : moduleVector (inputA noInstance) (inputB noInstance) (fun _ => 1) 0 ≠ 0 := by
    decide
  have hn : pairSup (moduleVector (inputA noInstance) (inputB noInstance)
      (fun _ => 1) 0) = 1 := by decide
  exact (hv.2.2 _ _ hne).trans_eq hn

/-- The total reduction's bound includes its radius-zero constant NO case. -/
theorem reduce_shortest_bound (x : List ℕ × ℕ)
    (v : Coeff (reduce x).1.1 × Coeff (reduce x).1.1)
    (hv : IsShortest (inputA (reduce x)) (inputB (reduce x)) v) :
    pairSup v ≤ max 1 (2 * (reduce x).2) := by
  by_cases hw : positiveWeights x.1 = []
  · revert v
    by_cases hB : x.2 = 0
    · have hr : reduce x = yesInstance := by simp [reduce, hw, hB]
      rw [hr]
      intro v hv
      exact (identity_shortest_le_one v hv).trans (le_max_left _ _)
    · have hr : reduce x = noInstance := by simp [reduce, hw, hB]
      rw [hr]
      intro v hv
      exact (identity_shortest_le_one v hv).trans (le_max_left _ _)
  · revert v
    rw [reduce_of_nonempty x hw]
    intro v hv
    exact (positiveReduce_search (positiveWeights x.1, x.2) v hv).2.trans (le_max_right _ _)

/-- The total map's radius-zero NO output really violates the uncorrected `2M` bound. -/
theorem reduce_two_M_counterexample :
    ∃ v : Coeff (reduce ([], 1)).1.1 × Coeff (reduce ([], 1)).1.1,
      IsShortest (inputA (reduce ([], 1))) (inputB (reduce ([], 1))) v ∧
        2 * (reduce ([], 1)).2 < pairSup v := by
  refine ⟨moduleVector (inputA noInstance) (inputB noInstance) (fun _ => 1) 0, ?_, ?_⟩
  · refine ⟨by decide, ⟨(fun _ => 1), 0, rfl⟩, ?_⟩
    intro a b hne
    exact one_le_pairSup_of_ne_zero _ hne
  · decide

end Power2ModuleSVPSubsetSum.Search
