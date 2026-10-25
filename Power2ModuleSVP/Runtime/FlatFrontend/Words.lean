import Power2ModuleSVP.Runtime.FlatFrontend.Taylor

/-!
# Words

Capped RS words: every intermediate word has at most the requested
number of entries. The cap also handles arbitrary, non-dyadic raw degrees.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP.FlatFrontend
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private theorem take_capped_append {α : Type} (m : ℕ) (xs ys : List α) :
    ((xs.take m) ++ (ys.take m)).take m = (xs ++ ys).take m := by
  by_cases h : m ≤ xs.length
  · simp [List.take_append, List.length_take, Nat.min_eq_left h, Nat.sub_eq_zero_of_le h]
  · have hm : xs.length ≤ m := by omega
    simp [List.take_append, List.length_take, Nat.min_eq_right hm,
      List.take_of_length_le hm, List.take_take, Nat.min_eq_left (show m - xs.length ≤ m by omega)]

private def wordStep (m : ℕ) (s : List ℤ × List ℤ) : List ℤ × List ℤ :=
  ((s.1 ++ s.2).take m, (s.1 ++ s.2.map Neg.neg).take m)

private def cappedWords (n m : ℕ) : List ℤ × List ℤ :=
  (wordStep m)^[n] (([1] : List ℤ).take m, ([1] : List ℤ).take m)

private theorem cappedWords_eq (n m : ℕ) : cappedWords n m =
    ((rsWords n).1.take m, (rsWords n).2.take m) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold cappedWords at *
    rw [Function.iterate_succ_apply', ih]
    simp only [wordStep, rsWords, List.map_take]
    rw [take_capped_append, take_capped_append]

private theorem rsWords_signs (n : ℕ) :
    (∀ z ∈ (rsWords n).1, z = -1 ∨ z = 1) ∧
    (∀ z ∈ (rsWords n).2, z = -1 ∨ z = 1) := by
  induction n with
  | zero => simp [rsWords]
  | succ n ih =>
    constructor
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact ih.1 z hz
      · exact ih.2 z hz
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact ih.1 z hz
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
        rcases ih.2 w hw with hw | hw <;> simp [hw]

private theorem cappedWord_length (n m : ℕ) :
    (encList encIntBin ((rsWords n).1.take m)).length ≤ 5 * m ∧
    (encList encIntBin ((rsWords n).2.take m)).length ≤ 5 * m := by
  have hb (xs : List ℤ) (hs : ∀ z ∈ xs, z = -1 ∨ z = 1) :
      (encList encIntBin (xs.take m)).length ≤ 5 * m := by
    have h := length_encList_le encIntBin (xs.take m) (b := 2) (by
      intro z hz
      rcases hs z (List.mem_of_mem_take hz) with rfl | rfl <;> decide)
    have hl : (xs.take m).length ≤ m := List.length_take_le m xs
    omega
  exact ⟨hb _ (rsWords_signs n).1, hb _ (rsWords_signs n).2⟩

@[fun_prop] private theorem cappedWords_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × ℕ => cappedWords a.1 a.2) (encPair encUnary encUnary)
    (encPair (encList encIntBin) (encList encIntBin)) := by
  unfold cappedWords
  apply iterateWith (encPar := encUnary) (snd _ _) (fst _ _) (by fun_prop)
    (show ComputableTidilyInPolyTime (fun a : ℕ × (List ℤ × List ℤ) => wordStep a.1 a.2)
      (encPair encUnary (encPair (encList encIntBin) (encList encIntBin)))
      (encPair (encList encIntBin) (encList encIntBin)) by unfold wordStep; fun_prop)
    (bound := fun a => 15 * a.2 + 2)
    (((PolyBounded.const 15).mul (snd encUnary encUnary).polyBounded).add (.const 2))
  intro a i hi
  change (encPair (encList encIntBin) (encList encIntBin) (cappedWords i a.2)).length ≤ _
  rw [cappedWords_eq, length_encPair]
  have h := cappedWord_length i a.2
  simp only [Prod.fst, Prod.snd]
  omega

@[fun_prop] theorem stablePrefix_polytime : ComputableTidilyInPolyTime stablePrefix
    encUnary (encList encIntBin) := by
  have h := cappedWords_polytime.fst'.comp
    (show ComputableTidilyInPolyTime (fun m : ℕ => (Nat.log2 m + 1, m)) encUnary
      (encPair encUnary encUnary) by fun_prop)
  exact h.of_enc_eq fun m => congrArg _ (by simp [stablePrefix, cappedWords_eq])

/-- Sampling the two words never materializes more than `j+1` entries. -/
@[fun_prop] theorem rsWordEntry_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × ℕ => ((rsWords a.1).1.getD a.2 0, (rsWords a.1).2.getD a.2 0))
    (encPair encUnary encUnary) (encPair encIntBin encIntBin) := by
  have hc := cappedWords_polytime.comp
    (show ComputableTidilyInPolyTime (fun a : ℕ × ℕ => (a.1, a.2 + 1))
      (encPair encUnary encUnary) (encPair encUnary encUnary) by fun_prop)
  have h : ComputableTidilyInPolyTime (fun a : ℕ × ℕ =>
      ((cappedWords a.1 (a.2 + 1)).1.getD a.2 0,
       (cappedWords a.1 (a.2 + 1)).2.getD a.2 0))
      (encPair encUnary encUnary) (encPair encIntBin encIntBin) := by
    apply ComputableTidilyInPolyTime.prod
    · exact (listGetD (encA := encIntBin) (0 : ℤ)).comp (hc.fst'.prod (snd _ _))
    · exact (listGetD (encA := encIntBin) (0 : ℤ)).comp (hc.snd'.prod (snd _ _))
  exact h.of_enc_eq fun a => congrArg _ (by
    simp [cappedWords_eq, List.getD_eq_getElem?_getD])

end Power2ModuleSVP.FlatFrontend
