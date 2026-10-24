import Complexity.Computability.Complexity.Classes.PH.KarpLipton
import Complexity.Computability.Circuit.Boolean.Advice

/-! # P/poly is closed under polynomial-time reductions

An advice word packages the target circuits for every output length up to the
reduction's polynomial output bound. Its evaluator is uniform polynomial time.
Hardwiring this advice works even when source encodings have no efficient decoder.
-/
namespace Cslib.Circuits.Boolean
open Cslib Cslib.Complexity Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Closure for arbitrary encoded problems, including variable output lengths. -/
theorem PPoly.of_polyTimeReducible {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (h : PolyTimeReducible encA encB A B)
    (hB : ∃ L ∈ PPoly, ∀ b, b ∈ B ↔ encB b ∈ L) :
    ∃ L' ∈ PPoly, ∀ a, a ∈ A ↔ encA a ∈ L' := by
  classical
  obtain ⟨f,hf,hfAB⟩ := h
  obtain ⟨L,hL,hBL⟩ := hB
  obtain ⟨C,s,hs,hC⟩ := mem_PPoly_iff_exists_circuits.mp hL
  obtain ⟨c,d,hcd⟩ := polynomiallyBounded_iff_le.mp hs
  obtain ⟨c',d',hfd⟩ := hf.polyBounded_length.exists_le
  let N : ℕ → ℕ := fun n => c' * (n+1)^d'
  let S : ℕ → ℕ := fun n => c * (N n + 1)^d
  let W : ℕ → ℕ := fun n => certLength (N n) (S n)
  let advice : ℕ → List Bool := fun n => familyAdvice (N n) (S n) C
  have hsize (n : ℕ) : ∀ m ≤ N n, (C m).size ≤ S n := by
    intro m hm
    exact ((hC m).1.trans (hcd m)).trans
      (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d))
  have hadvice : PolynomiallyBounded (fun n => (advice n).length) := by
    have he (n : ℕ) : (advice n).length = (N n + 1) * certLength (N n) (S n) :=
      length_familyAdvice (hsize n)
    simp_rw [he]
    unfold certLength S N
    fun_prop
  let V : List Bool × α → Bool := fun p =>
    evalAdvice (S (encA p.2).length) (W (encA p.2).length) p.1 (encB (f p.2))
  have hV : ComputableTidilyInPolyTime V (encPair encBits encA) encBool := by
    have hn : ComputableTidilyInPolyTime (fun p : List Bool × α => (encA p.2).length)
        (encPair encBits encA) encUnary := (encoding_length encA).comp (snd _ _)
    have hout : ComputableTidilyInPolyTime (fun p : List Bool × α => encB (f p.2))
        (encPair encBits encA) encBits := hf.encoded.comp (snd _ _)
    apply computableTidilyInPolyTime_evalAdvice (hw := fst _ _) (hx := hout)
    · dsimp [S,N]
      fun_prop
    · dsimp [W,certLength,S,N]
      fun_prop
  obtain ⟨M,hM,hVM⟩ := PPoly.exists_of_polyTime hV
  let L' : Language Bool := {w | frame (advice w.length) ++ w ∈ M}
  refine ⟨L', PPoly.of_advice hM advice hadvice (fun _ => Iff.rfl), fun a => ?_⟩
  have he : V (advice (encA a).length, a) =
      (C (encB (f a)).length).eval interpretation (fun i => (encB (f a))[i]) 0 :=
    evalAdvice_familyAdvice (hsize (encA a).length) (hfd a)
  have hv : V (advice (encA a).length, a) = true ↔ encB (f a) ∈ L := by
    rw [he, (hC _).2, single_apply, Language.slice_eq_true_iff]
    simp only [Fin.getElem_fin, List.ofFn_getElem]
  exact (hfAB a).trans ((hBL (f a)).trans
    (hv.symm.trans ((hVM (advice (encA a).length, a)).trans (by
      simp only [encPair_apply, encBits_apply]
      rfl))))

end Cslib.Circuits.Boolean
