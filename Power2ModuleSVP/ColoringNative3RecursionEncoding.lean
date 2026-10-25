import Power2ModuleSVP.ColoringNative3RecursionStatic

/-! Uniform encodings of the static matrix and thresholds in full recursion. -/
namespace Power2ModuleSVP.ColoringRuntime
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
set_option maxHeartbeats 600000

private theorem matrix_encoding_le_input (p : PartialColoringInput) :
    (encList (encList encColoringRational) p.1).length ≤ (encPartialColoring p).length :=
  length_le_encPair_left _ _ p

private theorem thresholds_encoding_le_input (p : PartialColoringInput) :
    (encList encColoringRational p.2.2).length ≤ (encPartialColoring p).length :=
  (length_le_encPair_right _ _ p.2).trans (length_le_encPair_right _ _ p)

private theorem point_encoding_le_input (p : PartialColoringInput) :
    (encList encColoringRational p.2.1).length ≤ (encPartialColoring p).length :=
  (length_le_encPair_left _ _ p.2).trans (length_le_encPair_right _ _ p)

private theorem dimensions_le_input (p : PartialColoringInput) :
    p.2.1.length ≤ (encPartialColoring p).length ∧
    p.1.length ≤ (encPartialColoring p).length ∧
    p.2.2.length ≤ (encPartialColoring p).length :=
  ⟨(length_le_length_encList _ _).trans (point_encoding_le_input p),
    (length_le_length_encList _ _).trans (matrix_encoding_le_input p),
    (length_le_length_encList _ _).trans (thresholds_encoding_le_input p)⟩

def thresholdShift (p : ℚ × ℕ) : ℚ := p.1 + 4 * (p.2 : ℚ)

@[fun_prop] theorem thresholdShift_polytime :
    ComputableTidilyInPolyTime thresholdShift (encPair encColoringRational encUnary)
      encColoringRational := by
  have hn := natCast_polytime.comp (unary_to_binary.comp (snd encColoringRational encUnary))
  unfold thresholdShift
  fun_prop

/-- Matrix restriction and integral threshold shifts have a uniform size
bound measured in the original input, at every recursive call. -/
 theorem recursive_static_encoding_polyBounded (F : PartialColoringInput → List ℚ) :
    ∃ c d : ℕ, ∀ (p : PartialColoringInput) (i : ℕ), i ≤ p.2.1.length →
      (encPair (encList (encList encColoringRational)) (encList encColoringRational)
        ((recursionInput F p i).1, (recursionInput F p i).2.2)).length ≤
          c * ((encPartialColoring p).length + 1) ^ d := by
  obtain ⟨cs, ds, hs⟩ := thresholdShift_polytime.polyBounded_length.exists_le
  let C := (encColoringRational 0).length
  let M := fun N => N * (2 * (N * (2 * (N + C) + 1)) + 1)
  let T := fun N => N * (2 * (cs * (3 * N + 2 * C + 2) ^ ds) + 1)
  have hpoly : PolyBounded id (fun N => 2 * M N + 1 + T N) := by
    refine ⟨fun N => 2 * M N + 1 + T N, ?_, fun _ => le_rfl⟩
    dsimp [M, T]
    fun_prop
  obtain ⟨c, d, hb⟩ := hpoly.exists_le
  refine ⟨c, d, fun p i hi => ?_⟩
  let N := (encPartialColoring p).length
  obtain ⟨hr, hm, hc⟩ := dimensions_le_input p
  have hq0 {q : ℚ} (hq : q = 0 ∨ ∃ row ∈ p.1, q ∈ row) :
      (encColoringRational q).length ≤ N + C := by
    rcases hq with rfl | ⟨row, hrow, hq⟩
    · exact Nat.le_add_left _ _
    · exact ((length_le_encList_of_mem _ hq).trans
        ((length_le_encList_of_mem _ hrow).trans (matrix_encoding_le_input p))).trans
          (Nat.le_add_right _ _)
  have hrow : ∀ row ∈ p.1, row.length ≤ N := by
    intro row hrow
    exact (length_le_length_encList _ row).trans
      ((length_le_encList_of_mem _ hrow).trans (matrix_encoding_le_input p))
  have hM : (encList (encList encColoringRational) (recursionInput F p i).1).length ≤ M N := by
    have hinner : ∀ row ∈ (recursionInput F p i).1,
        (encList encColoringRational row).length ≤ N * (2 * (N + C) + 1) := by
      intro row hrow'
      exact (length_encList_le _ _ (fun q hq => hq0 (descent_matrix_entries F p i row hrow' q hq))).trans
        (Nat.mul_le_mul_right _ (descent_matrix_row_length F p N hr hrow i row hrow'))
    have hout := length_encList_le _ _ hinner
    rw [descent_matrix_length] at hout
    exact hout.trans (Nat.mul_le_mul_right _ hm)
  have hT : (encList encColoringRational (recursionInput F p i).2.2).length ≤ T N := by
    have hentry : ∀ q ∈ (recursionInput F p i).2.2,
        (encColoringRational q).length ≤ cs * (3 * N + 2 * C + 2) ^ ds := by
      intro q hq
      obtain ⟨original, ho, k, hk, rfl⟩ := descent_threshold_entries F p i q hq
      have ho' : (encColoringRational original).length ≤ N + C := by
        rcases ho with ho | rfl
        · exact ((length_le_encList_of_mem _ ho).trans (thresholds_encoding_le_input p)).trans
            (Nat.le_add_right _ _)
        · exact Nat.le_add_left _ _
      apply (hs (original, k)).trans
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      have hkN : k ≤ N := hk.trans (hi.trans hr)
      omega
    have hout := length_encList_le _ _ hentry
    have hlen := descent_threshold_length F p i
    have hlenN : (recursionInput F p i).2.2.length ≤ N :=
      hlen.trans (max_le hc hm)
    exact hout.trans (Nat.mul_le_mul_right _ hlenN)
  apply le_trans (b := 2 * M N + 1 + T N)
  · simp only [length_encPair]
    omega
  · exact hb N

/-- Only the changing coordinate encoding remains once the static-data
invariant above has been proved. -/
 theorem recursiveInputEncoding_of_coordinate_encoding (F : PartialColoringInput → List ℚ)
    (hx : ∃ c d : ℕ, ∀ (p : PartialColoringInput) (i : ℕ), i ≤ p.2.1.length →
      (encList encColoringRational (recursionInput F p i).2.1).length ≤
        c * ((encPartialColoring p).length + 1) ^ d) : RecursiveInputEncodingHypothesis F := by
  obtain ⟨cs, ds, hs⟩ := recursive_static_encoding_polyBounded F
  obtain ⟨cx, dx, hx⟩ := hx
  have hp : PolyBounded id (fun N => cs * (N + 1) ^ ds + 2 * (cx * (N + 1) ^ dx) + 1) := by
    refine ⟨(fun N => cs * (N + 1) ^ ds + 2 * (cx * (N + 1) ^ dx) + 1), ?_, fun _ => le_rfl⟩
    fun_prop
  obtain ⟨c, d, hb⟩ := hp.exists_le
  refine ⟨⟨c, d, fun p i hi => ?_⟩⟩
  have hstatic := hs p i hi
  have hpoint := hx p i hi
  apply le_trans (b := cs * ((encPartialColoring p).length + 1) ^ ds +
      2 * (cx * ((encPartialColoring p).length + 1) ^ dx) + 1)
  · have he : (encPartialColoring (recursionInput F p i)).length =
        2 * (encList (encList encColoringRational) (recursionInput F p i).1).length + 1 +
          (2 * (encList encColoringRational (recursionInput F p i).2.1).length + 1 +
            (encList encColoringRational (recursionInput F p i).2.2).length) := by
      simp only [encPartialColoring, length_encPair]
    simp only [length_encPair] at hstatic
    rw [he]
    omega
  · exact hb _

end Power2ModuleSVP.ColoringRuntime
