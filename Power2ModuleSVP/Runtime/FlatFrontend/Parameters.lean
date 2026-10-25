import Power2ModuleSVP.Runtime.FlatFrontend.Taylor
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Parameters

Certificates for total parameter selection. Large powers are kept binary;
only polynomially bounded counters are converted to unary.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP.FlatFrontend
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
open ColoringRuntime
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

private theorem findGreatest_eq_findD (predicate : ℕ → Prop) [DecidablePred predicate]
    (bound : ℕ) : Nat.findGreatest predicate bound =
      (((List.range (bound + 1)).reverse).find? (fun i => decide (predicate i))).getD 0 := by
  induction bound with
  | zero => by_cases h : predicate 0 <;> simp [h]
  | succ bound ih =>
    rw [Nat.findGreatest_succ, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.find?_cons]
    split_ifs <;> simp_all

private theorem boundedSearch {α : Type} {input : α ↪ List Bool} {bound : α → ℕ}
    {predicate : α → ℕ → Prop} [∀ a, DecidablePred (predicate a)]
    (hbound : ComputableTidilyInPolyTime bound input encUnary)
    (hpredicate : ComputableTidilyInPolyTime (fun p : α × ℕ => decide (predicate p.1 p.2))
      (encPair input encUnary) encBool) :
    ComputableTidilyInPolyTime (fun a => Nat.findGreatest (predicate a) (bound a))
      input encUnary := by
  simp only [findGreatest_eq_findD]
  have hlist := listReverseWithInput (range.comp (unary_add.comp (hbound.prod (const 1))))
  exact (findWithInput hlist hpredicate).optionGetDWithInput (const 0)

@[fun_prop] theorem stageWidth_polytime : ComputableTidilyInPolyTime stageWidth
    encUnary encNat := by
  unfold stageWidth
  fun_prop

private theorem stagePredicateScale_polytime (C : ℕ) : ComputableTidilyInPolyTime
    (fun a : ℕ × ℕ => decide (stageWidth (2 * a.2 + 1) * C ≤ a.1))
    (encPair encUnary encUnary) encBool := by
  have hs := stageWidth_polytime.comp
    (show ComputableTidilyInPolyTime (fun a : ℕ × ℕ => 2 * a.2 + 1)
      (encPair encUnary encUnary) encUnary by fun_prop)
  exact binary_le.comp ((binary_mul.comp (hs.prod (const C))).prod
    (unary_to_binary.comp (fst _ _)))

private theorem stagePredicate_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × ℕ => decide (stageWidth (2 * a.2 + 1) * 2 ^ 66 ≤ a.1))
    (encPair encUnary encUnary) encBool := stagePredicateScale_polytime (2 ^ 66)

@[fun_prop] theorem stageIndex_polytime : ComputableTidilyInPolyTime stageIndex
    encUnary encUnary := by
  exact boundedSearch AnchorRepairRuntime.log2_polytime stagePredicate_polytime

@[fun_prop] theorem stage_polytime : ComputableTidilyInPolyTime stage encUnary encUnary := by
  unfold stage
  fun_prop

@[fun_prop] theorem blockShift_polytime : ComputableTidilyInPolyTime blockShift
    encUnary encNat := by
  unfold blockShift
  fun_prop

theorem blockShift_le_raw (N : ℕ) : blockShift N ≤ 2048 * (N + 1) ^ 2 := by
  have hr : stageIndex N ≤ Nat.log2 N := Nat.findGreatest_le _
  have hp : 2 ^ Nat.log2 N ≤ N + 1 := by
    by_cases hn : N = 0
    · subst N; decide
    · exact ((Nat.le_log2 hn).mp (le_refl _)).trans (by omega)
  have hq : 2 ^ stageIndex N ≤ N + 1 :=
    (Nat.pow_le_pow_right (by omega) hr).trans hp
  have he : stage N + 10 = stageIndex N * 2 + 11 := by unfold stage; omega
  unfold blockShift
  rw [he, pow_add, pow_mul]
  norm_num
  nlinarith [Nat.pow_le_pow_left hq 2]

@[fun_prop] theorem blockShift_unary_polytime : ComputableTidilyInPolyTime blockShift
    encUnary encUnary :=
  binary_to_unary_bounded blockShift_polytime
    (show ComputableTidilyInPolyTime (fun N : ℕ => 2048 * (N + 1) ^ 2)
      encUnary encUnary by fun_prop) blockShift_le_raw

@[fun_prop] theorem stagePower_unary_polytime : ComputableTidilyInPolyTime
    (fun N => 2 ^ stage N) encUnary encUnary := by
  apply binary_to_unary_bounded
    (show ComputableTidilyInPolyTime (fun N => 2 ^ stage N) encUnary encNat by fun_prop)
    blockShift_unary_polytime
  intro N
  unfold blockShift
  exact Nat.pow_le_pow_right (by omega) (by omega)

@[fun_prop] theorem height_polytime : ComputableTidilyInPolyTime height
    encUnary encColoringRational := by
  unfold height
  fun_prop

@[fun_prop] theorem gridRatio_binary_polytime : ComputableTidilyInPolyTime gridRatio
    encUnary encNat := by
  have hc : ComputableTidilyInPolyTime (fun N : ℕ =>
      (⌈64 * (N : ℚ) / height N⌉ : ℤ).toNat) encUnary encNat := by fun_prop
  exact (binary_mul.comp ((const 2).prod hc)).of_enc_eq fun N =>
    congrArg encNat (by simp [gridRatio, Int.ceil_toNat])

/-- A deliberately coarse raw-input bound; the constant is fixed, not input data. -/
theorem blockShift_lower {N : ℕ} (hN : 0 < N) :
    (N : ℚ) ≤ (blockShift N : ℚ) * 2 ^ 70 := by
  have hp : 2 ^ stage N ≤ blockShift N := by
    unfold blockShift
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hb : 0 < blockShift N := by unfold blockShift; positivity
  have hn := stage_next_inadmissible N
  rw [stageWidth_succ_two, stageWidth_block] at hn
  have hc : N ≤ blockShift N * 2 ^ 70 := by
    have he : (2 : ℕ) ^ 70 = 16 * 2 ^ 66 := by norm_num
    rw [he]
    have hw : 4 * (2 * blockShift N + 2 ^ stage N - 1) + 3 ≤ 16 * blockShift N := by omega
    have hh := Nat.mul_le_mul_right (2 ^ 66) hw
    nlinarith
  exact_mod_cast hc

set_option exponentiation.threshold 1024 in
theorem height_lower_raw {N : ℕ} (hN : 0 < N) :
    (1 : ℚ) / 2 ^ 212 ≤ height N := by
  have hn : (0 : ℚ) < N := by exact_mod_cast hN
  have hb : (0 : ℚ) ≤ blockShift N := by positivity
  have hr : (1 : ℚ) / 2 ^ 70 ≤ (blockShift N : ℚ) / N := by
    apply (le_div_iff₀ hn).mpr
    have h := blockShift_lower hN
    linarith
  have hp : (1 : ℚ) ≤ 2 ^ ((stage N + 1) / 2) := one_le_pow₀ (by norm_num)
  calc
    height N ≥ 30 * (1 : ℚ) / 128 * (2 * (1 / 2 ^ 70)) ^ 3 := by
      unfold height
      have he : 2 * (blockShift N : ℚ) / N = 2 * ((blockShift N : ℚ) / N) := by ring
      rw [he]
      gcongr
    _ ≥ 1 / 2 ^ 212 := by norm_num

set_option exponentiation.threshold 1024 in
theorem gridRatio_le_raw (N : ℕ) : gridRatio N ≤ 2 * (64 * N * 2 ^ 212 + 1) := by
  by_cases hn : N = 0
  · subst N
    norm_num [gridRatio, height]
  have hN : 0 < N := Nat.pos_of_ne_zero hn
  have hh := height_lower_raw hN
  have hp := height_positive hN
  have hmul : (1 : ℚ) ≤ 2 ^ 212 * height N := by linarith
  have hq : 64 * (N : ℚ) / height N ≤ 64 * N * 2 ^ 212 + 1 := by
    apply (div_le_iff₀ hp).mpr
    have h := mul_le_mul_of_nonneg_left hmul (show (0 : ℚ) ≤ 64 * N by positivity)
    nlinarith
  have hc : ⌈64 * (N : ℚ) / height N⌉₊ ≤ 64 * N * 2 ^ 212 + 1 := by
    apply Nat.ceil_le.mpr
    exact_mod_cast hq
  unfold gridRatio
  omega

private theorem gridBound_polytime (C : ℕ) : ComputableTidilyInPolyTime
    (fun N : ℕ => 2 * (64 * N * C + 1)) encUnary encUnary := by fun_prop

@[fun_prop] theorem gridRatio_polytime : ComputableTidilyInPolyTime gridRatio
    encUnary encUnary := by
  apply binary_to_unary_bounded gridRatio_binary_polytime
    (bound := fun N => 2 * (64 * N * 2 ^ 212 + 1))
    (gridBound_polytime (2 ^ 212)) gridRatio_le_raw

@[fun_prop] theorem firstThreshold_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × ℕ => firstThreshold a.1 a.2)
    (encPair encUnary encUnary) encColoringRational := by
  unfold firstThreshold
  have hl : ComputableTidilyInPolyTime (fun a : ℕ × ℕ =>
      Nat.log2 (64 * a.1 / a.2)) (encPair encUnary encUnary) encUnary := by fun_prop
  have hs := sqrt_polytime.comp (unary_to_binary.comp
    (show ComputableTidilyInPolyTime (fun a : ℕ × ℕ =>
      56 * (Nat.log2 (64 * a.1 / a.2) + 1) / 5)
      (encPair encUnary encUnary) encUnary by fun_prop))
  exact natCast_polytime.comp (binary_add.comp (hs.prod (const 1)))

end Power2ModuleSVP.FlatFrontend
