import Power2IdealSVP.Glue.Source
import Power2IdealSVP.Spin.Geometry

/-!
# Natural and integer source distances

The runtime difference list supplies the positive natural distances used by the Spin layer.
Its integer interpretation is exactly the source layer's positive-difference interface.

Paper: `paper/power2-ideal-svp.txt`, Sections 1.1–1.4.
-/

namespace Power2IdealSVP.Glue

open Cslib.Complexity

/-- The executable difference list as a finite set of natural distances. -/
def spinDistances (x : Graph × ℕ) : Finset ℕ := (Runtime.diffSet x).toFinset

/-- Every runtime distance is positive and bounded by the largest source label. -/
theorem spinDistances_valid (x : Graph × ℕ) :
    Spin.DValid (spinDistances x) (Runtime.maxLabel x) := by
  intro d hd
  have hd' : d ∈ Runtime.diffSet x := by simpa [spinDistances] using hd
  have hb := (Runtime.mem_diffSet x d).mp hd'
  exact ⟨hb.2.1, hb.1⟩

/-- Casting natural distances identifies the two positive-difference predicates. -/
theorem positiveDifferences_iff (x : Graph × ℕ) (P : Finset ℤ) :
    Spin.PositiveDifferences (spinDistances x) P ↔
      Source.PositiveDifferences P (differenceSet x) := by
  constructor
  · intro h a ha b hb hab
    apply (mem_differenceSet x (b - a)).mpr
    refine ⟨(b - a).toNat, ?_, Int.toNat_of_nonneg (by omega)⟩
    simpa [spinDistances] using h a ha b hb hab
  · intro h a ha b hb hab
    obtain ⟨d, hd, he⟩ := (mem_differenceSet x (b - a)).mp (h a ha b hb hab)
    have he' : (b - a).toNat = d := by omega
    simpa [spinDistances, he'] using hd

end Power2IdealSVP.Glue
