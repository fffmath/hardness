import Power2ModuleSVP.Runtime.Repair.Parameters
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration

/-!
# Arithmetic

Exact fraction list arithmetic for repair. A common denominator reduces a
list sum to certified binary integer products, division, and a sum. Thus the
integer product certificates account for intermediate bit sizes, including
when denominators are not reduced. No promise on the runtime input is used.

Paper: `paper/power2svp.pdf`, Section 5 (Theorems 3–4 and deterministic anchor repair).
-/
namespace Power2ModuleSVP.AnchorRepairRuntime
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] List.getD

/-- Absolute value of the product of all fraction denominators. -/
def fractionDen (xs : List Fraction) : ℕ := ((xs.map Prod.snd).prod : ℤ).natAbs

/-- Sum fractions using the product of their denominators. -/
def fractionSum (xs : List Fraction) : Fraction :=
  ((xs.map fun a => a.1 * ((fractionDen xs / a.2.natAbs : ℕ) : ℤ)).sum,
    (fractionDen xs : ℤ))

/-- Multiply all numerators and all denominators separately. -/
def fractionProd (xs : List Fraction) : Fraction :=
  ((xs.map Prod.fst).prod, (xs.map Prod.snd).prod)

/-- The `fractionDen` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem fractionDen_polytime :
    ComputableTidilyInPolyTime fractionDen (encList encFraction) encNat := by
  unfold fractionDen encFraction
  fun_prop

/-- The `fractionSum` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem fractionSum_polytime :
    ComputableTidilyInPolyTime fractionSum (encList encFraction) encFraction := by
  unfold fractionSum
  apply ComputableTidilyInPolyTime.prod
  · apply intBin_sum.comp
    apply mapWithInput (encA := encFraction)
    · exact id'
    · unfold encFraction
      fun_prop
  · fun_prop

/-- The `fractionProd` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem fractionProd_polytime :
    ComputableTidilyInPolyTime fractionProd (encList encFraction) encFraction := by
  unfold fractionProd encFraction
  fun_prop

/-- A product of positive fraction denominators remains positive. -/
theorem fractionDen_pos (xs : List Fraction) (h : ∀ a ∈ xs, 0 < a.2) :
    0 < fractionDen xs := by
  unfold fractionDen
  apply Int.natAbs_pos.mpr
  apply ne_of_gt
  apply List.prod_pos
  intro n hn
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
  exact h a ha

/-- The list sum preserves positive denominators and has the expected rational value. -/
theorem fractionSum_spec (xs : List Fraction) (h : ∀ a ∈ xs, 0 < a.2) :
    0 < (fractionSum xs).2 ∧
      fractionValue (fractionSum xs) = (xs.map fractionValue).sum := by
  have hD := fractionDen_pos xs h
  have hDq : (fractionDen xs : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  refine ⟨by change (0 : ℤ) < (fractionDen xs : ℤ); exact_mod_cast hD, ?_⟩
  unfold fractionSum fractionValue
  simp only [Int.cast_list_sum, List.map_map, Function.comp_def,
    Int.cast_mul, Int.cast_natCast]
  rw [show ∀ l : List ℚ, l.sum / (fractionDen xs : ℚ) =
      (l.map (fun q => q / (fractionDen xs : ℚ))).sum by
    intro l; induction l with
    | nil => simp
    | cons q l ih => simp [add_div, ih]]
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hdvd : a.2.natAbs ∣ fractionDen xs :=
    Int.natAbs_dvd_natAbs.mpr (List.dvd_prod (List.mem_map.mpr ⟨a, ha, rfl⟩))
  have hden : (a.2.natAbs : ℚ) = (a.2 : ℚ) := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_pos (h a ha)]
  rw [Nat.cast_div_charZero hdvd, hden]
  field_simp

/-- The list product preserves positive denominators and has the expected rational value. -/
theorem fractionProd_spec (xs : List Fraction) (h : ∀ a ∈ xs, 0 < a.2) :
    0 < (fractionProd xs).2 ∧
      fractionValue (fractionProd xs) = (xs.map fractionValue).prod := by
  refine ⟨?_, ?_⟩
  · apply List.prod_pos
    intro n hn
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
    exact h a ha
  · unfold fractionProd fractionValue
    simp only [Int.cast_list_prod]
    induction xs with
    | nil => simp
    | cons a xs ih =>
      simp only [List.map_cons, List.prod_cons, List.map_map] at *
      rw [← div_mul_div_comm, ih (fun b hb => h b (by simp [hb]))]

/-- Both component bit lengths are charged by the framed fraction encoding. -/
def fractionBits (a : Fraction) : ℕ := max a.1.natAbs.size a.2.natAbs.size

/-- The fraction encoding length bounds both component bit lengths. -/
theorem fractionBits_le_length (a : Fraction) :
    fractionBits a ≤ (encFraction a).length := by
  simp only [fractionBits, encFraction, length_encPair, length_encIntBin]
  omega

/-- Native polynomial-time certificates bound numerator and denominator bits,
not merely the number of arithmetic operations. -/
theorem fractionBits_polyBounded_of {α : Type} {enc : α ↪ List Bool}
    {f : α → Fraction} (hf : ComputableTidilyInPolyTime f enc encFraction) :
    PolyBounded (fun a => (enc a).length) (fun a => fractionBits (f a)) :=
  hf.polyBounded_length.mono (fun a => fractionBits_le_length (f a))

/-- Both components of the list sum have polynomially bounded bit lengths. -/
theorem fractionSum_bits_polyBounded :
    PolyBounded (fun xs => (encList encFraction xs).length)
      (fun xs => fractionBits (fractionSum xs)) :=
  fractionBits_polyBounded_of fractionSum_polytime

/-- Both components of the list product have polynomially bounded bit lengths. -/
theorem fractionProd_bits_polyBounded :
    PolyBounded (fun xs => (encList encFraction xs).length)
      (fun xs => fractionBits (fractionProd xs)) :=
  fractionBits_polyBounded_of fractionProd_polytime

end Power2ModuleSVP.AnchorRepairRuntime
