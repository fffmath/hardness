import Power2ModuleSVP.ColoringNative3RecursionDenominators
import Power2ModuleSVP.ColoringNative3Program

/-! Additive one-call denominator growth closes the entire recursive bound. -/
namespace Power2ModuleSVP.ColoringRuntime
open Turing.MultiTapeTM
open ColoringNative
set_option maxHeartbeats 600000

/-- A local arithmetic interface for one selected partial call. Its cost
reads matrix, thresholds and dimension, never the current point encoding. -/
structure PartialDenominatorGrowthHypothesis (F : PartialColoringInput → List ℚ) : Prop where
  growth : ∃ c d : ℕ, ∀ (p : PartialColoringInput) (D : ℕ), 0 < D →
    (∀ q ∈ p.2.1, q.den ∣ D) →
    ∃ E : ℕ, 0 < E ∧ (∀ q ∈ recursivePoint F p, q.den ∣ E) ∧
      E.size ≤ D.size + c * ((encPreparation (p.2.1.length, (p.1, p.2.2))).length + 1) ^ d

 theorem recursive_preparation_encoding_polyBounded (F : PartialColoringInput → List ℚ) :
    ∃ c d : ℕ, ∀ (p : PartialColoringInput) (i : ℕ), i ≤ p.2.1.length →
      (encPreparation ((recursionInput F p i).2.1.length,
        ((recursionInput F p i).1, (recursionInput F p i).2.2))).length ≤
          c * ((encPartialColoring p).length + 1) ^ d := by
  obtain ⟨cs, ds, hs⟩ := recursive_static_encoding_polyBounded F
  have hp : PolyBounded id (fun N => 2 * N + 1 + cs * (N + 1) ^ ds) := by
    refine ⟨(fun N => 2 * N + 1 + cs * (N + 1) ^ ds), ?_, fun _ => le_rfl⟩
    fun_prop
  obtain ⟨c, d, hb⟩ := hp.exists_le
  refine ⟨c, d, fun p i hi => ?_⟩
  have hx : (encList encColoringRational p.2.1).length ≤ (encPartialColoring p).length :=
    (length_le_encPair_left _ _ p.2).trans (length_le_encPair_right _ _ p)
  have hr := (descent_dimension_le F p i).trans ((length_le_length_encList _ _).trans hx)
  have hh := hs p i hi
  simp only [length_encPair] at hh
  apply le_trans (b := 2 * (encPartialColoring p).length + 1 +
      cs * ((encPartialColoring p).length + 1) ^ ds)
  · simp only [encPreparation, length_encPair, encUnary_apply, List.length_replicate]
    exact Nat.add_le_add (by omega) hh
  · exact hb _

private def listDen (x : List ℚ) : ℕ := (x.map Rat.den).prod
private theorem listDen_pos (x : List ℚ) : 0 < listDen x := by
  apply List.prod_pos
  intro d hd
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hd
  exact q.den_pos

private theorem listDen_dvd (x : List ℚ) : ∀ q ∈ x, q.den ∣ listDen x := by
  intro q hq
  exact List.dvd_prod (List.mem_map.mpr ⟨q, hq, rfl⟩)

private theorem listDen_input_size (p : PartialColoringInput) :
    (listDen p.2.1).size ≤ 1 + (encPartialColoring p).length ^ 2 := by
  let N := (encPartialColoring p).length
  have hx : (encList encColoringRational p.2.1).length ≤ N :=
    (length_le_encPair_left _ _ p.2).trans (length_le_encPair_right _ _ p)
  have hr := (length_le_length_encList _ p.2.1).trans hx
  have h := product_denominator_size 1 (p.2.1.map Rat.den) (B := N) (by
    intro d hd
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
    have hqN := (length_le_encList_of_mem encColoringRational hq).trans hx
    have hdq : q.den.size ≤ (encColoringRational q).length := by
      simp only [encColoringRational, Function.Embedding.coeFn_mk, length_encPair,
        length_encIntBin, encNat_apply, Nat.size_eq_bits_len]
      omega
    exact hdq.trans hqN)
  simp only [Nat.one_mul, List.length_map, Nat.size_one] at h
  exact h.trans (by nlinarith [Nat.mul_le_mul_right N hr])

/-- A fixed polynomial contribution per call is added at most the original
dimension many times; it is never iterated as a polynomial in point size. -/
 theorem recursiveCoordinateDenominator_of_growth (F : PartialColoringInput → List ℚ)
    (hg : PartialDenominatorGrowthHypothesis F) : RecursiveCoordinateDenominatorHypothesis F := by
  obtain ⟨cg, dg, hg⟩ := hg.growth
  obtain ⟨cp, dp, hp⟩ := recursive_preparation_encoding_polyBounded F
  let A := fun N => cg * (cp * (N + 1) ^ dp + 1) ^ dg
  have hpoly : PolyBounded id (fun N => 1 + N ^ 2 + N * A N) := by
    refine ⟨(fun N => 1 + N ^ 2 + N * A N), ?_, fun _ => le_rfl⟩
    unfold A
    fun_prop
  obtain ⟨c, d, hb⟩ := hpoly.exists_le
  refine ⟨⟨c, d, fun p i hi q hq => ?_⟩⟩
  let N := (encPartialColoring p).length
  have htrace : ∀ j ≤ p.2.1.length, ∃ D : ℕ, 0 < D ∧
      (∀ q ∈ (recursionInput F p j).2.1, q.den ∣ D) ∧
      D.size ≤ (listDen p.2.1).size + j * A N := by
    intro j
    induction j with
    | zero =>
      intro hj
      exact ⟨listDen p.2.1, listDen_pos _, listDen_dvd _, by simp⟩
    | succ j ih =>
      intro hj
      obtain ⟨D, hD, hdiv, hsize⟩ := ih (by omega)
      rw [recursionInput, Function.iterate_succ_apply']
      rw [descentStep_eq]
      split_ifs
      · obtain ⟨E, hE, hden, hEsize⟩ := hg (recursionInput F p j) D hD hdiv
        refine ⟨E, hE, ?_, ?_⟩
        · intro q hq'
          obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq'
          rcases getD_mem_or_zero (recursivePoint F (recursionInput F p j)) k with hm | hz
          · exact hden _ hm
          · rw [hz]
            simp
        · have hpar := hp p j (by omega)
          have hcost : cg * ((encPreparation ((recursionInput F p j).2.1.length,
              ((recursionInput F p j).1, (recursionInput F p j).2.2))).length + 1) ^ dg ≤ A N := by
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_left (Nat.add_le_add_right hpar 1) dg
          nlinarith
      · exact ⟨D, hD, hdiv, hsize.trans (by nlinarith)⟩
  obtain ⟨D, hD, hdiv, hsize⟩ := htrace i hi
  have hqsize := Nat.size_le_size (Nat.le_of_dvd hD (hdiv q hq))
  have hD0 := listDen_input_size p
  have hx : (encList encColoringRational p.2.1).length ≤ N :=
    (length_le_encPair_left _ _ p.2).trans (length_le_encPair_right _ _ p)
  have hr := (length_le_length_encList _ p.2.1).trans hx
  apply hqsize.trans
  apply le_trans (b := 1 + N ^ 2 + N * A N)
  · have hiA := Nat.mul_le_mul_right (A N) (hi.trans hr)
    nlinarith [hiA]
  · exact hb N

 theorem fullColor_partialColor_native_of_denominator_growth
    (hF : PartialColoringAlg.PartialColoringNativeHypothesis)
    (hg : PartialDenominatorGrowthHypothesis PartialColoringAlg.partialColor) :
    FullColoringNativeHypothesis PartialColoringAlg.partialColor :=
  fullColor_partialColor_native_of_coordinate_denominator hF
    (recursiveCoordinateDenominator_of_growth _ hg)

end Power2ModuleSVP.ColoringRuntime
