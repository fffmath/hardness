import Power2ModuleSVP.FlatSeedMain
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log

/-!
Executable parameter selection for the flat seed. All quantities in this
file are integers or rationals. The bounded search examines logarithmically
many candidate odd stages. References to the private manuscript are by label
only; the formulas below specify our implementation of `thm:spectral-seed`.
-/
namespace Power2ModuleSVP
namespace FlatFrontend

def stageWidth (t : ℕ) : ℕ := 2 ^ (t + 11) + 2 ^ t - 1

def stageIndex (N : ℕ) : ℕ :=
  Nat.findGreatest (fun r => stageWidth (2 * r + 1) * 2 ^ 66 ≤ N) (Nat.log2 N)

def stage (N : ℕ) : ℕ := 2 * stageIndex N + 1

def blockShift (N : ℕ) : ℕ := 2 ^ (stage N + 10)

def gamma (N : ℕ) : ℚ := (stageWidth (stage N) : ℚ) / N

def height (N : ℕ) : ℚ :=
  30 * (2 : ℚ) ^ ((stage N + 1) / 2) / 128 *
    (2 * (blockShift N : ℚ) / N) ^ 3

def gridRatio (N : ℕ) : ℕ := 2 * (⌈64 * (N : ℚ) / height N⌉₊)

def gridSize (N : ℕ) : ℕ := N * gridRatio N

def gridError (N : ℕ) : ℚ :=
  min (height N / (128 * (N : ℚ) ^ 3)) (1 / (4 * (gridSize N : ℚ) ^ 2))

theorem stage_odd (N : ℕ) : Odd (stage N) := ⟨stageIndex N, rfl⟩

theorem stage_positive (N : ℕ) : 0 < stage N := by unfold stage; omega

theorem stage_admissible {N : ℕ} (hN : stageWidth 1 * 2 ^ 66 ≤ N) :
    stageWidth (stage N) * 2 ^ 66 ≤ N := by
  exact Nat.findGreatest_spec (P := fun r => stageWidth (2 * r + 1) * 2 ^ 66 ≤ N)
    (m := 0) (Nat.zero_le _) (by simpa using hN)

theorem stageWidth_positive (t : ℕ) : 0 < stageWidth t := by
  have h : 2 ≤ 2 ^ (t + 11) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (t + 11) := Nat.pow_le_pow_right (by omega) (by omega)
  unfold stageWidth
  have : 0 < 2 ^ t := by positivity
  omega

theorem stageWidth_block (N : ℕ) :
    stageWidth (stage N) = 2 * blockShift N + 2 ^ stage N - 1 := by
  unfold stageWidth blockShift
  rw [show stage N + 11 = (stage N + 10) + 1 by omega, pow_succ]
  omega

theorem stageWidth_pow_le (t : ℕ) : 2 ^ t ≤ stageWidth t := by
  have : 0 < 2 ^ (t + 11) := by positivity
  unfold stageWidth
  omega

theorem admissible_index_le {N r : ℕ}
    (h : stageWidth (2 * r + 1) * 2 ^ 66 ≤ N) : r ≤ Nat.log2 N := by
  have hp : 2 ^ (2 * r + 1) ≤ N := by
    exact (stageWidth_pow_le _).trans
      ((Nat.le_mul_of_pos_right _ (by positivity)).trans h)
  have hN : N ≠ 0 := by
    have : 0 < 2 ^ (2 * r + 1) := by positivity
    omega
  have he : 2 * r + 1 ≤ Nat.log2 N := (Nat.le_log2 hN).mpr hp
  omega

theorem stage_maximal {N r : ℕ} (hr : stage N < 2 * r + 1) :
    ¬ stageWidth (2 * r + 1) * 2 ^ 66 ≤ N := by
  intro h
  have hbound := admissible_index_le h
  have hlt : stageIndex N < r := by unfold stage at hr; omega
  exact Nat.findGreatest_is_greatest hlt hbound h

theorem gamma_positive {N : ℕ} (hN : 0 < N) : 0 < gamma N := by
  unfold gamma
  exact div_pos (by exact_mod_cast stageWidth_positive (stage N)) (by exact_mod_cast hN)

theorem gamma_upper {N : ℕ} (hN : stageWidth 1 * 2 ^ 66 ≤ N) :
    gamma N ≤ 1 / 2 ^ 66 := by
  have hn : (0 : ℚ) < N := by
    have := stageWidth_positive 1
    have : 0 < stageWidth 1 * 2 ^ 66 := by positivity
    exact_mod_cast (lt_of_lt_of_le this hN)
  have ha : (stageWidth (stage N) : ℚ) * 2 ^ 66 ≤ N := by
    exact_mod_cast stage_admissible hN
  unfold gamma
  apply (div_le_iff₀ hn).mpr
  linarith

theorem height_positive {N : ℕ} (hN : 0 < N) : 0 < height N := by
  have hn : (0 : ℚ) < N := by exact_mod_cast hN
  have hb : (0 : ℚ) < blockShift N := by unfold blockShift; positivity
  unfold height
  positivity

theorem stageWidth_succ_two (t : ℕ) : stageWidth (t + 2) = 4 * stageWidth t + 3 := by
  have hp : 0 < 2 ^ (t + 11) := by positivity
  have hq : 0 < 2 ^ t := by positivity
  have he : 2 ^ (t + 2 + 11) = 4 * 2 ^ (t + 11) := by
    rw [show t + 2 + 11 = (t + 11) + 2 by omega, pow_add]
    norm_num
    omega
  have hf : 2 ^ (t + 2) = 4 * 2 ^ t := by rw [pow_add]; norm_num; omega
  unfold stageWidth
  rw [he, hf]
  omega

theorem stage_next_inadmissible (N : ℕ) :
    N < stageWidth (stage N + 2) * 2 ^ 66 := by
  have h := stage_maximal (N := N) (r := stageIndex N + 1)
    (by unfold stage; omega)
  have he : 2 * (stageIndex N + 1) + 1 = stage N + 2 := by unfold stage; omega
  rw [he] at h
  omega

theorem gamma_lower {N : ℕ} (hN : 0 < N) : 1 / 2 ^ 69 < gamma N := by
  have hw := stageWidth_positive (stage N)
  have hh := stage_next_inadmissible N
  rw [stageWidth_succ_two] at hh
  have hn : N < stageWidth (stage N) * 2 ^ 69 := by
    have hpow : 2 ^ 69 = 8 * 2 ^ 66 := by norm_num
    rw [hpow]
    nlinarith
  have hr : (N : ℚ) < (stageWidth (stage N) : ℚ) * 2 ^ 69 := by exact_mod_cast hn
  unfold gamma
  apply (lt_div_iff₀ (by exact_mod_cast hN : (0 : ℚ) < N)).mpr
  linarith

set_option exponentiation.threshold 1024 in
theorem stage_admissible_at_cutoff {d : ℕ} (hd : 2 ^ 512 ≤ d) :
    stageWidth (stage (seedN d)) * 2 ^ 66 ≤ seedN d := by
  apply stage_admissible
  unfold stageWidth seedN
  norm_num at hd ⊢
  omega

theorem block_fits {N : ℕ} (hN : stageWidth 1 * 2 ^ 66 ≤ N) :
    2 * blockShift N + 2 ^ stage N - 1 ≤ N := by
  rw [← stageWidth_block]
  exact (Nat.le_mul_of_pos_right _ (by positivity)).trans (stage_admissible hN)

theorem even_bound_parameters {N : ℕ} (hN : stageWidth 1 * 2 ^ 66 ≤ N) :
    4 ≤ N ∧ 64 * 2 ^ (stage N + 1) ≤ N := by
  have ha := stage_admissible hN
  have hp := stageWidth_pow_le (stage N)
  have hpow : 2 ^ (stage N + 1) = 2 ^ stage N * 2 := pow_succ _ _
  constructor
  · unfold stageWidth at hN
    norm_num at hN
    omega
  · rw [hpow]
    nlinarith

end FlatFrontend
end Power2ModuleSVP
