module

public import Power2ModuleSVP.Coloring.Full
public import Power2ModuleSVP.Runtime.Coloring.Denominators

/-!
# Output Bounds

Unconditional size facts for full coloring. Threshold shifts preserve their
canonical denominators, restrictions preserve a common coordinate
denominator, and the final word has linear size for every partial program.
These are size lemmas, not a native certificate for the complete recursion.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP.ColoringNative

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Even malformed partial-program outputs are converted to a sign word. -/
theorem fullColorCore_signs (F : PartialColoringInput → List ℚ) (r m : ℕ)
    (V : Fin m → Fin r → ℚ) (x : Fin r → ℚ) (c : Fin m → ℚ) :
    ∀ j, Coloring.fullColorCore F r m V x c j = -1 ∨
      Coloring.fullColorCore F r m V x c j = 1 := by
  induction r using Nat.strong_induction_on generalizing c with
  | h r ih =>
    by_cases hsmall : r ≤ 64
    · rw [Coloring.fullColorCore, ite_eq_left hsmall]
      exact fun j => nearestRationalSign_isSign _
    · rw [Coloring.fullColorCore, ite_eq_right hsmall]
      dsimp only
      split_ifs with hprogress
      · apply Coloring.extend_signs
        exact ih _ hprogress _ _ _
      · exact fun j => nearestRationalSign_isSign _

theorem fullColor_signs (F : PartialColoringInput → List ℚ) (input : PartialColoringInput)
    (q : ℚ) (hq : q ∈ fullColor F input) : q = -1 ∨ q = 1 := by
  unfold fullColor at hq
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
  exact fullColorCore_signs F _ _ _ _ _ j

private theorem sign_encoding_length (q : ℚ) (hq : q = -1 ∨ q = 1) :
    (encColoringRational q).length = 6 := by
  rcases hq with rfl | rfl <;>
    norm_num [encColoringRational, length_encPair, length_encIntBin, encNat_apply,
      Nat.size_eq_bits_len]

/-- A full output has thirteen encoded bits per sign, independently of
correctness, entropy promises, and intermediate coordinate denominators. -/
theorem fullColor_encoding_length_le (F : PartialColoringInput → List ℚ)
    (input : PartialColoringInput) :
    (encList encColoringRational (fullColor F input)).length ≤ 13 * input.2.1.length := by
  have h := length_encList_le encColoringRational (fullColor F input)
    (fun q hq => (sign_encoding_length q (fullColor_signs F input q hq)).le)
  rw [fullColor_length] at h
  simpa only [Nat.mul_comm] using h

theorem fullColor_output_polyBounded (F : PartialColoringInput → List ℚ) :
    PolyBounded (fun input => (encPartialColoring input).length)
      (fun input => (encList encColoringRational (fullColor F input)).length) := by
  apply PolyBounded.of_forall_le 13 1
  intro input
  have hs := fullColor_encoding_length_le F input
  have hx := length_le_length_encList encColoringRational input.2.1
  have hp := length_le_encPair_left (encList encColoringRational)
    (encList encColoringRational) input.2
  have hi := length_le_encPair_right (encList (encList encColoringRational))
    (encPair (encList encColoringRational) (encList encColoringRational)) input
  change _ ≤ 13 * ((encPartialColoring input).length + 1) ^ 1
  change (encList encColoringRational input.2.1).length ≤
    (encPair (encList encColoringRational) (encList encColoringRational) input.2).length at hp
  change (encPair (encList encColoringRational) (encList encColoringRational) input.2).length ≤
    (encPartialColoring input).length at hi
  nlinarith

/-- Restricting to the next active dimension adds no denominator factor. -/
theorem commonDen_restrict {r s D : ℕ} (x : Fin r → ℚ) (e : Fin s → Fin r)
    (hx : CommonDen D x) : CommonDen D (fun j => x (e j)) := fun j => hx (e j)

theorem threshold_iterate (q : ℚ) (k : ℕ) :
    (fun t : ℚ => t + 4)^[k] q = q + 4 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    push_cast
    ring

/-- Threshold denominators remain the original input denominators at every
recursive level, rather than multiplying between levels. -/
theorem threshold_iterate_den (q : ℚ) (k : ℕ) :
    ((fun t : ℚ => t + 4)^[k] q).den = q.den := by
  rw [threshold_iterate]
  have he : (4 : ℚ) * k = ((4 * (k : ℤ) : ℤ) : ℚ) := by push_cast; rfl
  rw [he, Rat.add_intCast_den]

end Power2ModuleSVP.ColoringNative
