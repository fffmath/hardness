import Hardness.Complexity.FixedCompiler
import Hardness.Complexity.PPolyReduction

/-! # The CVPP Karp–Lipton corollary

The preprocessing advice is indexed by the universe size. A length-n circuit
hardwires advice for every universe size at most n, since m is encoded in unary.
-/
namespace Hardness
open Cslib Cslib.Complexity Cslib.Circuits.Boolean Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Polynomial circuits for the one fixed ideal per universe size imply NP ⊆ P/poly. -/
theorem np_subset_ppoly_of_fixedCVPP
    (h : ∃ L ∈ PPoly, ∀ x, x ∈ FixedCVPP ↔ encFixedCVPP x ∈ L) :
    ∀ {β : Type} (encB : β ↪ List Bool), ∀ B ∈ NP encB,
      ∃ L ∈ PPoly, ∀ b, b ∈ B ↔ encB b ∈ L := by
  intro β encB B hB
  exact PPoly.of_polyTimeReducible (fixedCVPP_npHard encB B hB) h

/-- Karp–Lipton for exact CVP with the fixed principal-ideal family. -/
theorem PH_eq_SigmaP_two_of_fixedCVPP {α : Type} (enc : α ↪ List Bool)
    (h : ∃ L ∈ PPoly, ∀ x, x ∈ FixedCVPP ↔ encFixedCVPP x ∈ L) :
    PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_two_of_NP_subset_PPoly (np_subset_ppoly_of_fixedCVPP h)

/-- Hardwire length-indexed advice for a problem with any encoding. -/
theorem exists_ppoly_of_encoded_advice {α : Type} (enc : α ↪ List Bool) (A : Set α)
    (a : ℕ → List Bool) (ha : PolynomiallyBounded fun n => (a n).length)
    (V : List Bool × α → Bool)
    (hV : ComputableTidilyInPolyTime V (encPair encBits enc) encBool)
    (h : ∀ x, x ∈ A ↔ V (a (enc x).length, x) = true) :
    ∃ L ∈ PPoly, ∀ x, x ∈ A ↔ enc x ∈ L := by
  obtain ⟨M,hM,hVM⟩ := PPoly.exists_of_polyTime hV
  let L : Language Bool := {w | frame (a w.length) ++ w ∈ M}
  refine ⟨L, PPoly.of_advice hM a ha (fun _ => Iff.rfl), fun x => ?_⟩
  exact (h x).trans ((hVM (a (enc x).length,x)).trans (by
    simp only [encPair_apply, encBits_apply]
    rfl))

/-- A table contains all universe-indexed advice that a length-n input can use. -/
def cvppAdviceTable (a : ℕ → List Bool) (n : ℕ) : List Bool :=
  encList encBits ((List.range (n+1)).map a)

theorem cvppAdviceTable_polyBounded (a : ℕ → List Bool)
    (ha : PolynomiallyBounded fun m => (a m).length) :
    PolynomiallyBounded fun n => (cvppAdviceTable a n).length := by
  obtain ⟨c,d,hcd⟩ := polynomiallyBounded_iff_le.mp ha
  apply PolynomiallyBounded.mono_of_le
    (g := fun n => (n+1) * (2 * (c * (n+1)^d) + 1)) (by fun_prop)
  intro n
  unfold cvppAdviceTable
  have he := length_encList_le encBits ((List.range (n+1)).map a)
    (b := c * (n+1)^d) (by
      intro w hw
      obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hw
      have hm' := List.mem_range.mp hm
      exact (hcd m).trans
        (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d)))
  simpa using he

attribute [local irreducible] List.getD

/-- Polynomial preprocessing advice and a uniform polynomial-time query decider
supply the circuit-family hypothesis. Preprocessing itself can be uncomputable. -/
theorem fixedCVPP_ppoly_of_preprocessing
    (a : ℕ → List Bool) (ha : PolynomiallyBounded fun m => (a m).length)
    (D : List Bool × (List ℤ × ℤ) → Bool)
    (hD : ComputableTidilyInPolyTime D
      (encPair encBits (encPair (encList encIntBin) encIntBin)) encBool)
    (hspec : ∀ m t Δ, D (a m,t,Δ) = true ↔ (m,t,Δ) ∈ FixedCVPP) :
    ∃ L ∈ PPoly, ∀ x, x ∈ FixedCVPP ↔ encFixedCVPP x ∈ L := by
  let V : List Bool × FixedCVPPInput → Bool := fun p =>
    D (((Decoder.bits.list).decode p.1).getD p.2.1 [],p.2.2)
  have hV : ComputableTidilyInPolyTime V (encPair encBits encFixedCVPP) encBool := by
    have hdec : ComputableTidilyInPolyTime (Decoder.bits.list).decode encBits
        (encList encBits) := (Decoder.bits.list).computableTidilyInPolyTime
    have htable := hdec.comp (fst encBits encFixedCVPP)
    have hm : ComputableTidilyInPolyTime (fun p : List Bool × FixedCVPPInput => p.2.1)
        (encPair encBits encFixedCVPP) encUnary := (snd encBits encFixedCVPP).fst'
    have hget := (listGetD (encA := encBits) (encL := encList encBits) []).comp
      (htable.prod hm)
    exact hD.comp (hget.prod (snd encBits encFixedCVPP).snd')
  apply exists_ppoly_of_encoded_advice encFixedCVPP FixedCVPP
    (cvppAdviceTable a) (cvppAdviceTable_polyBounded a ha) V hV
  intro x
  have hm : x.1 < (encFixedCVPP x).length + 1 := by
    simp only [encFixedCVPP, length_encPair, encUnary_apply, List.length_replicate]
    omega
  have he : V (cvppAdviceTable a (encFixedCVPP x).length,x) = D (a x.1,x.2) := by
    simp [V, cvppAdviceTable, Decoder.decode_enc, List.getD_eq_getElem?_getD, hm]
  rw [he]
  exact (hspec x.1 x.2.1 x.2.2).symm

/-- Karp–Lipton in the usual universe-indexed preprocessing formulation. -/
theorem PH_eq_SigmaP_two_of_polyCVPP {α : Type} (enc : α ↪ List Bool)
    (a : ℕ → List Bool) (ha : PolynomiallyBounded fun m => (a m).length)
    (D : List Bool × (List ℤ × ℤ) → Bool)
    (hD : ComputableTidilyInPolyTime D
      (encPair encBits (encPair (encList encIntBin) encIntBin)) encBool)
    (hspec : ∀ m t Δ, D (a m,t,Δ) = true ↔ (m,t,Δ) ∈ FixedCVPP) :
    PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_two_of_fixedCVPP enc (fixedCVPP_ppoly_of_preprocessing a ha D hD hspec)

end Hardness
