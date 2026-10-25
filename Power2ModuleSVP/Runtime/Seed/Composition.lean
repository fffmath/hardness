import Power2ModuleSVP.Seed.Algorithm
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# Composition

Native machine composition for the explicit two-coloring seed program.

Paper: `paper/power2svp.pdf`, Appendix A (Theorem 5, the deterministic flat seed).
-/
namespace Power2ModuleSVP
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
attribute [local irreducible] List.getD

/-- Encoding of the degree and rational second-stage coloring. -/
abbrev encSeedSecondInput := encPair encUnary (encList encColoringRational)
/-- Degree, integer first-stage coloring, and rational second-stage coloring. -/
abbrev SeedAssemblyInput := ℕ × (List ℤ × List ℚ)
/-- Encoding of the inputs used to assemble the seed coefficients. -/
abbrev encSeedAssembly := encPair encUnary (encPair (encList encIntBin)
  (encList encColoringRational))

/-- The runtime obligations concern only rational preprocessing, on every
raw input. They do not assume a time bound for `seed` itself. -/
structure FlatSeedFrontendRuntimeHypothesis (A : FlatSeedFrontend) : Prop where
  background : ComputableTidilyInPolyTime A.background encUnary (encList encIntBin)
  intervals : ComputableTidilyInPolyTime A.intervalInput encUnary encPartialColoring
  coefficients : ComputableTidilyInPolyTime A.coefficientInput
    encSeedSecondInput encPartialColoring

/-- The `seedN` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem seedN_polytime :
    ComputableTidilyInPolyTime seedN encUnary encUnary := by
  unfold seedN
  fun_prop

/-- The `seedIntegerSign` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem seedIntegerSign_polytime :
    ComputableTidilyInPolyTime seedIntegerSign encIntBin encIntBin := by
  unfold seedIntegerSign
  simpa only [decide_eq_true_eq] using intBin_isNeg.ite'
    (const (-1) : ComputableTidilyInPolyTime (fun _ : ℤ => (-1 : ℤ)) encIntBin encIntBin)
    (const (1 : ℤ))

/-- The `seedRationalSign` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem seedRationalSign_polytime :
    ComputableTidilyInPolyTime seedRationalSign encColoringRational encIntBin := by
  have hc : ComputableTidilyInPolyTime (fun q : ℚ => (q.num, q.den))
      encColoringRational (encPair encIntBin encNat) :=
    ComputableTidilyInPolyTime.of_eq (fun _ => rfl)
  exact seedIntegerSign_polytime.comp hc.fst'

/-- The `seedOddPosition` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem seedOddPosition_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × ℕ => decide (seedOddPosition a.1 a.2))
    (encPair encUnary encUnary) encBool := by
  unfold seedOddPosition
  fun_prop

/-- The `seedOddIndex` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem seedOddIndex_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × ℕ => seedOddIndex a.1 a.2)
    (encPair encUnary encUnary) encUnary := by
  unfold seedOddIndex
  fun_prop

/-- Assemble one integer seed coefficient from the two coloring stages. -/
def seedAssemblyEntry (a : SeedAssemblyInput × ℕ) : ℤ :=
  if seedOddPosition (seedN a.1.1) a.2 then
    let z := seedRationalSign (a.1.2.2.getD (seedOddIndex (seedN a.1.1) a.2) 1)
    if a.2 < 2 * seedN a.1.1 then -z else z
  else seedIntegerSign (a.1.2.1.getD a.2 1)

set_option maxHeartbeats 1000000 in
-- Nested list lookup and both conditional branches expand several encoding compositions.
/-- The `seedAssemblyEntry` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem seedAssemblyEntry_polytime : ComputableTidilyInPolyTime
    seedAssemblyEntry (encPair encSeedAssembly encUnary) encIntBin := by
  unfold seedAssemblyEntry
  have hodd : ComputableTidilyInPolyTime
      (fun a : SeedAssemblyInput × ℕ => decide (seedOddPosition (seedN a.1.1) a.2))
      (encPair encSeedAssembly encUnary) encBool := by
    apply seedOddPosition_polytime.comp (g := fun a : SeedAssemblyInput × ℕ =>
      (seedN a.1.1, a.2))
    unfold encSeedAssembly
    fun_prop
  apply ComputableTidilyInPolyTime.of_enc_eq
    (encB := encIntBin)
    (f := fun a : SeedAssemblyInput × ℕ =>
      if decide (seedOddPosition (seedN a.1.1) a.2) then
        let z := seedRationalSign (a.1.2.2.getD (seedOddIndex (seedN a.1.1) a.2) 1)
        if a.2 < 2 * seedN a.1.1 then -z else z
      else seedIntegerSign (a.1.2.1.getD a.2 1))
  swap
  · intro a; simp only [decide_eq_true_eq]
  apply hodd.ite'
  · have hz : ComputableTidilyInPolyTime
        (fun a : SeedAssemblyInput × ℕ =>
          seedRationalSign (a.1.2.2.getD (seedOddIndex (seedN a.1.1) a.2) 1))
        (encPair encSeedAssembly encUnary) encIntBin := by
      apply seedRationalSign_polytime.comp
      apply (listGetD (encA := encColoringRational)
        (encL := encList encColoringRational) (1 : ℚ)).comp
        (g := fun a : SeedAssemblyInput × ℕ =>
          (a.1.2.2, seedOddIndex (seedN a.1.1) a.2))
      apply ComputableTidilyInPolyTime.prod
      · unfold encSeedAssembly; fun_prop
      · apply seedOddIndex_polytime.comp (g := fun a : SeedAssemblyInput × ℕ =>
          (seedN a.1.1, a.2))
        unfold encSeedAssembly
        fun_prop
    have hneg : ComputableTidilyInPolyTime
        (fun a : SeedAssemblyInput × ℕ => decide (a.2 < 2 * seedN a.1.1))
        (encPair encSeedAssembly encUnary) encBool := by
      unfold encSeedAssembly
      fun_prop
    simpa only [decide_eq_true_eq, Function.comp_def] using hneg.ite' (intBin_neg.comp hz) hz
  · apply seedIntegerSign_polytime.comp
    apply (listGetD (encA := encIntBin) (encL := encList encIntBin) (1 : ℤ)).comp
      (g := fun a : SeedAssemblyInput × ℕ => (a.1.2.1, a.2))
    unfold encSeedAssembly
    fun_prop

/-- The `seedAssemble` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem seedAssemble_polytime : ComputableTidilyInPolyTime
    (fun a : SeedAssemblyInput => seedAssemble a.1 a.2.1 a.2.2)
    encSeedAssembly (encList encIntBin) := by
  unfold seedAssemble
  apply mapWithInput (encA := encUnary)
  · unfold encSeedAssembly; fun_prop
  · exact seedAssemblyEntry_polytime

/-- Two calls to the supplied uniform coloring machine, followed by the
certified list assembly. The statement includes malformed and small degrees. -/
theorem seed_polytime (A : FlatSeedFrontend) (hA : FlatSeedFrontendRuntimeHypothesis A)
    (F : PartialColoringInput → List ℚ)
    (hF : ComputableTidilyInPolyTime F encPartialColoring (encList encColoringRational)) :
    ComputableTidilyInPolyTime (seed A F) encUnary (encList encIntBin) := by
  have hfirst := hF.comp hA.intervals
  have hsecond := hF.comp (hA.coefficients.comp (id'.prod hfirst))
  exact seedAssemble_polytime.comp (id'.prod (hA.background.prod hsecond))

/-- The assembled seed output length is polynomially bounded in the unary degree. -/
theorem seed_encoded_length_polyBounded (A : FlatSeedFrontend)
    (hA : FlatSeedFrontendRuntimeHypothesis A) (F : PartialColoringInput → List ℚ)
    (hF : ComputableTidilyInPolyTime F encPartialColoring (encList encColoringRational)) :
    PolyBounded (fun d => (encUnary d).length)
      (fun d => (encList encIntBin (seed A F d)).length) :=
  (seed_polytime A hA F hF).polyBounded_length

end Power2ModuleSVP
