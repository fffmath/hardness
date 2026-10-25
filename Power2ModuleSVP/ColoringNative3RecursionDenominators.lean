import Power2ModuleSVP.ColoringNative3RecursionEncoding

/-! Reduce the remaining recursive input bound to coordinate denominators. -/
namespace Power2ModuleSVP.ColoringRuntime
open Turing.MultiTapeTM
open PartialColoringAlg
set_option maxHeartbeats 600000

 theorem partialColor_output_cube (p : PartialColoringInput) :
    ∀ q ∈ partialColor p, |q| ≤ 1 := by
  intro q hq
  unfold partialColor at hq
  split_ifs at hq with hv
  · have hxbool : p.2.1.all (fun q => decide (|q| ≤ 1)) = true := by
      unfold validInput at hv
      exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).2
    have hx : RationalCube (fun j : Fin p.2.1.length => p.2.1.getD j 0) := by
      intro j
      have hj : p.2.1.getD j 0 ∈ p.2.1 := by
        simp [List.getD_eq_getElem?_getD, j.isLt]
      have hh := of_decide_eq_true ((List.all_eq_true.mp hxbool) _ hj)
      exact_mod_cast hh
    unfold partialColorCore at hq
    dsimp only at hq
    split_ifs at hq
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
      rcases nearestRationalSign_isSign (p.2.1.getD j 0) with h | h <;> rw [h] <;> norm_num
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
      have hr : 0 < p.2.1.length := Nat.zero_lt_of_lt j.isLt
      have hh := run_cube hr (prepareRows
        (fun i : Fin p.1.length => fun j : Fin p.2.1.length => (p.1.getD i []).getD j 0)
        (fun i => p.2.2.getD i 0)).get _ hx j
      exact_mod_cast hh
  · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hq
    rcases nearestRationalSign_isSign q with h | h <;> rw [h] <;> norm_num

 theorem descent_point_original_or_cube (F : PartialColoringInput → List ℚ)
    (hF : ∀ p, ∀ q ∈ F p, |q| ≤ 1) (p : PartialColoringInput) (i : ℕ) :
    recursionInput F p i = p ∨ ∀ q ∈ (recursionInput F p i).2.1, |q| ≤ 1 := by
  induction i with
  | zero => exact Or.inl rfl
  | succ i ih =>
    rw [recursionInput, Function.iterate_succ_apply']
    rw [descentStep_eq]
    split_ifs
    · right
      intro q hq
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
      rcases getD_mem_or_zero (recursivePoint F (recursionInput F p i)) j with hm | hz
      · exact hF _ _ hm
      · rw [hz]
        norm_num
    · exact ih

/-- The only remaining full-recursion arithmetic field: polynomially many
canonical denominator bits for coordinates of actual recursive calls. The
matrix, thresholds, stack, signs and all native programs are already bounded. -/
structure RecursiveCoordinateDenominatorHypothesis (F : PartialColoringInput → List ℚ) : Prop where
  denominator_bound : ∃ c d : ℕ, ∀ (p : PartialColoringInput) (i : ℕ), i ≤ p.2.1.length →
    ∀ q ∈ (recursionInput F p i).2.1,
      q.den.size ≤ c * ((encPartialColoring p).length + 1) ^ d

 theorem recursiveInputEncoding_of_coordinate_denominator (F : PartialColoringInput → List ℚ)
    (hF : ∀ p, ∀ q ∈ F p, |q| ≤ 1) (hden : RecursiveCoordinateDenominatorHypothesis F) :
    RecursiveInputEncodingHypothesis F := by
  obtain ⟨cd, dd, hd⟩ := hden.denominator_bound
  let B := fun N => N + N * (8 * (cd * (N + 1) ^ dd) + 7)
  have hp : PolyBounded id B := by
    refine ⟨B, ?_, fun _ => le_rfl⟩
    unfold B
    fun_prop
  obtain ⟨c, d, hb⟩ := hp.exists_le
  apply recursiveInputEncoding_of_coordinate_encoding F
  refine ⟨c, d, fun p i hi => ?_⟩
  let N := (encPartialColoring p).length
  have hx : (encList encColoringRational p.2.1).length ≤ N :=
    (length_le_encPair_left _ _ p.2).trans (length_le_encPair_right _ _ p)
  have hr : p.2.1.length ≤ N := (length_le_length_encList _ _).trans hx
  apply le_trans (b := B N)
  · rcases descent_point_original_or_cube F hF p i with he | hcube
    · rw [he]
      exact hx.trans (Nat.le_add_right _ _)
    · have henc := length_encList_le encColoringRational (recursionInput F p i).2.1
        (b := 4 * (cd * (N + 1) ^ dd) + 3) (fun q hq =>
          rational_encoding_le_of_den_bound q (hcube q hq) (hd p i hi q hq))
      have hlen := (descent_dimension_le F p i).trans hr
      apply henc.trans
      have hmul := Nat.mul_le_mul_right (8 * (cd * (N + 1) ^ dd) + 7) hlen
      unfold B
      nlinarith [hmul]
  · exact hb N

 theorem fullColor_partialColor_native_of_coordinate_denominator
    (hF : PartialColoringNativeHypothesis)
    (hden : RecursiveCoordinateDenominatorHypothesis partialColor) :
    FullColoringNativeHypothesis partialColor :=
  fullColor_partialColor_native_of_recursive_input_bound hF
    (recursiveInputEncoding_of_coordinate_denominator _ partialColor_output_cube hden)

end Power2ModuleSVP.ColoringRuntime
