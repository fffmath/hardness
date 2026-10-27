import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-!
# Families of pairs in one row or column

The elementary finite-relation argument used in difference-clique extraction.
Paper: `paper/power2-ideal-svp.pdf`, Section 1.1, Lemma 1.
-/

namespace Power2IdealSVP.Source

/-- A nonempty family of ordered pairs whose members share a coordinate is contained in
one row or one column. No lower bound on the family size is needed. -/
theorem exists_row_or_column {ι α β : Type*} [Nonempty ι] (p : ι → α × β)
    (h : ∀ x y, (p x).1 = (p y).1 ∨ (p x).2 = (p y).2) :
    (∃ a, ∀ x, (p x).1 = a) ∨ (∃ b, ∀ x, (p x).2 = b) := by
  classical
  let x := Classical.arbitrary ι
  by_cases hr : ∀ y, (p y).1 = (p x).1
  · exact Or.inl ⟨(p x).1, hr⟩
  · obtain ⟨y, hy⟩ := not_forall.mp hr
    have hy' : (p y).2 = (p x).2 := (h y x).resolve_left hy
    refine Or.inr ⟨(p x).2, fun z => ?_⟩
    rcases h z x with hz | hz
    · rcases h z y with hz' | hz'
      · exact False.elim (hy (hz'.symm.trans hz))
      · exact hz'.trans hy'
    · exact hz

end Power2IdealSVP.Source
