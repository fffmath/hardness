import Power2ModuleSVP.Seed.Specification
import Power2ModuleSVP.Coloring.Partial.Specification

/-!
# The two-coloring seed program

A total list program builds the flat seed from a rational frontend and a full-coloring program.
Output normalization guarantees shape and signs. The concrete frontend and native composition
are certified in FlatFrontend and Runtime/Seed.

Paper: `paper/power2svp.pdf`, Appendix A (Theorem 5, the deterministic flat seed).
-/
namespace Power2ModuleSVP

/-- The finite rational preprocessing interface. The first call prepares the
interval-sign problem; the second uses those signs to prepare derivative
rounding. `background` holds the even Laurent coefficients and the four
fixed coefficients, in their final shifted positions. -/
structure FlatSeedFrontend where
  background : ℕ → List ℤ
  intervalInput : ℕ → PartialColoringInput
  coefficientInput : ℕ × List ℚ → PartialColoringInput

def seedN (d : ℕ) : ℕ := d / 4 - 1

def seedIntegerSign (z : ℤ) : ℤ := if z < 0 then -1 else 1

def seedRationalSign (q : ℚ) : ℤ := seedIntegerSign q.num

theorem seedIntegerSign_sign (z : ℤ) :
    seedIntegerSign z = -1 ∨ seedIntegerSign z = 1 := by
  unfold seedIntegerSign
  split <;> simp

theorem seedRationalSign_cast {q : ℚ} (hq : q = -1 ∨ q = 1) :
    (seedRationalSign q : ℚ) = q := by
  rcases hq with rfl | rfl <;> norm_num [seedRationalSign, seedIntegerSign]

/-- Positions of the odd Laurent frequencies after the shift by `2N`.
The last three appended coefficients are excluded. -/
def seedOddPosition (N i : ℕ) : Prop := i < 4 * N + 1 ∧ i % 2 = 1

instance (N i : ℕ) : Decidable (seedOddPosition N i) :=
  inferInstanceAs (Decidable (i < 4 * N + 1 ∧ i % 2 = 1))

def seedOddIndex (N i : ℕ) : ℕ :=
  if i < 2 * N then (2 * N - i - 1) / 2 else (i - 2 * N - 1) / 2

/-- Assembly is linear in the explicit degree apart from list lookups.
Negative odd frequencies have the opposite sign to positive ones. -/
def seedAssemble (d : ℕ) (background : List ℤ) (odd : List ℚ) : List ℤ :=
  (List.range d).map fun i =>
    if seedOddPosition (seedN d) i then
      let a := seedRationalSign (odd.getD (seedOddIndex (seedN d) i) 1)
      if i < 2 * seedN d then -a else a
    else seedIntegerSign (background.getD i 1)

/-- The requested computable program, with a supplied rational coloring
routine. There is no real comparison, choice operator, or seed search here. -/
def seed (A : FlatSeedFrontend) (F : PartialColoringInput → List ℚ) (d : ℕ) : List ℤ :=
  let α := F (A.intervalInput d)
  let ε := F (A.coefficientInput (d, α))
  seedAssemble d (A.background d) ε

@[simp] theorem seedAssemble_length (d : ℕ) (b : List ℤ) (ε : List ℚ) :
    (seedAssemble d b ε).length = d := by simp [seedAssemble]

@[simp] theorem seed_length (A : FlatSeedFrontend) (F : PartialColoringInput → List ℚ)
    (d : ℕ) : (seed A F d).length = d := by simp [seed]

theorem seedAssemble_signs (d : ℕ) (b : List ℤ) (ε : List ℚ) :
    Signs (IdealCVP.ofList (d := d) (seedAssemble d b ε)) := by
  intro i
  simp only [IdealCVP.ofList, seedAssemble, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range i.isLt, Option.map_some, Option.getD_some]
  split_ifs
  · rcases seedIntegerSign_sign (ε.getD (seedOddIndex (seedN d) i) 1).num with h | h <;>
      simp only [List.getD_eq_getElem?_getD] at h <;> simp [seedRationalSign, h]
  · exact seedIntegerSign_sign _
  · exact seedIntegerSign_sign _

theorem seed_signs (A : FlatSeedFrontend) (F : PartialColoringInput → List ℚ) (d : ℕ) :
    Signs (IdealCVP.ofList (d := d) (seed A F d)) := seedAssemble_signs _ _ _

/-- Both halves of each odd-frequency pair address an actual rounding
coordinate. The proof retains closed endpoints of the shifted support. -/
theorem seedOddIndex_lt {N i : ℕ} (hi : seedOddPosition N i) :
    seedOddIndex N i < N := by
  unfold seedOddPosition at hi
  unfold seedOddIndex
  split_ifs <;> omega

end Power2ModuleSVP
