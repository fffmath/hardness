import Power2ModuleSVPSubsetSum.Problem

/-! # Fixed outputs for empty normalized sources

The degree-one identity basis gives a fixed YES instance at radius one and a fixed NO
instance at radius zero. Both satisfy every input validity condition.

Paper: `paper/power2svp-subsetsum.pdf`, Section 4.1; `AUDIT_A.md`, edge cases.
-/

namespace Power2ModuleSVPSubsetSum
open Power2ModuleSVP (Coeff coeffSup pairSup moduleVector)

/-- A fixed well-formed YES input, using the identity basis in degree one. -/
def yesInstance : SVPInput := ((1, ([1], [0]), ([0], [1])), 1)

/-- The same full-rank basis at radius zero is a fixed NO input. -/
def noInstance : SVPInput := ((1, ([1], [0]), ([0], [1])), 0)

/-- The fixed YES output is a valid input. -/
theorem yesInstance_wellFormed : yesInstance.WellFormed := by
  refine ⟨⟨0, rfl⟩, rfl, rfl, rfl, rfl, ?_⟩
  decide

/-- The fixed NO output is also a valid input. -/
theorem noInstance_wellFormed : noInstance.WellFormed := yesInstance_wellFormed

/-- Radius zero contains no nonzero coefficient pair, in any degree. -/
theorem not_moduleYes_zero {d : ℕ} (a b : Coeff d × Coeff d) :
    ¬ ModuleYes a b 0 := by
  rintro ⟨u, v, hne, hbound⟩
  apply hne
  apply Prod.ext <;> funext i
  · have hi : ((moduleVector a b u v).1 i).natAbs ≤ 0 :=
      (Finset.le_sup (Finset.mem_univ i)).trans ((le_max_left _ _).trans hbound)
    exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hi)
  · have hi : ((moduleVector a b u v).2 i).natAbs ≤ 0 :=
      (Finset.le_sup (Finset.mem_univ i)).trans ((le_max_right _ _).trans hbound)
    exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hi)

/-- The fixed YES output belongs to the decision language. -/
theorem yesInstance_mem : yesInstance ∈ ModuleSVPLang := by
  refine ⟨yesInstance_wellFormed, (fun _ => 1), 0, ?_, ?_⟩
  · decide
  · decide

/-- The fixed NO output does not belong to the decision language. -/
theorem noInstance_not_mem : noInstance ∉ ModuleSVPLang := by
  rintro ⟨_, h⟩
  exact not_moduleYes_zero _ _ h

end Power2ModuleSVPSubsetSum
