import Power2ModuleSVP.Runtime.Coloring.PartialDenominators
import Power2ModuleSVP.Runtime.Coloring.Recursion.Growth

/-!
# Partial Call Growth

The canonicalized partial call used by full recursion inherits the
row-dependent additive denominator bound, including malformed inputs.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime
open PartialColoringAlg
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] List.getD

/-- Truncate or zero-pad preparation rows and thresholds to their intended lengths. -/
def canonicalPreparation (p : PreparationInput) : PreparationInput :=
  (p.1, (p.2.1.map (fun row => trimRow (p.1, row)),
    (List.range p.2.1.length).map fun i => p.2.2.getD i 0))

/-- Native polynomial-time certificate for `canonicalPreparation`. -/
theorem canonicalPreparation_polytime :
    ComputableTidilyInPolyTime canonicalPreparation encPreparation encPreparation := by
  let eL := encList encColoringRational
  let eV := encList eL
  let eStatic := encPair eV eL
  let hR := fst encUnary eStatic
  let hStatic := snd encUnary eStatic
  let hV := (fst eV eL).comp hStatic
  let hC := (snd eV eL).comp hStatic
  let hR' := hR.comp (fst encPreparation eL)
  let hTrim := trimRow_polytime.comp (hR'.prod (snd encPreparation eL))
  have hv := mapWithInput (f := fun p : PreparationInput => fun row => trimRow (p.1, row)) hV hTrim
  let hM := (length_list eL).comp hV
  let hCi := (listGetD (encA := encColoringRational) 0).comp
    ((hC.comp (fst encPreparation encUnary)).prod (snd encPreparation encUnary))
  have hc := mapWithInput (f := fun p : PreparationInput => fun i => p.2.2.getD i 0)
    (range.comp hM) hCi
  have hp := hR.prod (hv.prod hc)
  exact hp.of_enc_eq fun p => congrArg encPreparation (by rfl)

theorem canonicalPreparation_spec (p : PartialColoringInput) :
    canonicalPreparation (p.2.1.length, (p.1, p.2.2)) =
      ((canonicalColoringInput p).2.1.length,
        ((canonicalColoringInput p).1, (canonicalColoringInput p).2.2)) := rfl

/-- The actual local growth contract used by the full list evaluator. -/
theorem partialDenominatorGrowth_of_projector (h : CanonicalProjectorDenominatorHypothesis) :
    PartialDenominatorGrowthHypothesis partialColor := by
  obtain ⟨c₀, d₀, hg⟩ := partialColor_commonDen_increment h
  obtain ⟨cp, dp, hp⟩ := canonicalPreparation_polytime.polyBounded_length.exists_le
  let B (n : ℕ) := c₀ * (cp * (n + 1) ^ dp + 1) ^ d₀
  have hB : PolyBounded id B := ⟨B, by unfold B; fun_prop, fun _ => le_rfl⟩
  obtain ⟨c, d, hb⟩ := hB.exists_le
  refine ⟨⟨c, d, fun p D hD hden => ?_⟩⟩
  obtain ⟨E, hE, hOut, hsize⟩ := hg (canonicalColoringInput p) D hD hden
  refine ⟨E, hE, hOut, hsize.trans (Nat.add_le_add_left ?_ D.size)⟩
  have hcanon := hp (p.2.1.length, (p.1, p.2.2))
  rw [canonicalPreparation_spec] at hcanon
  exact (Nat.mul_le_mul_left c₀ (Nat.pow_le_pow_left
    (Nat.add_le_add_right hcanon 1) d₀)).trans (hb _)

end Power2ModuleSVP.ColoringRuntime
