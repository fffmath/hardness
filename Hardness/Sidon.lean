import Hardness.Lattice
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.ZMod.Basic

/-! # Separated positions

The reduction uses the quadratic Erdős–Turán construction from paper Lemma
`lem:sidon`, including a deterministic prime search and a proof of uniqueness
of nonzero ordered differences. An elementary cubic construction is retained
as an alternative.
-/
namespace Hardness

structure SidonPositions (n : ℕ) where
  α : Fin n → ℕ
  c : ℕ
  bound : ∀ j, α j ≤ c
  strictMono : StrictMono α
  differences : ∀ j k j' k', j ≠ k → j' ≠ k' →
    (α k : ℤ) - α j = (α k' : ℤ) - α j' → j = j' ∧ k = k'

namespace SidonPositions
variable {n : ℕ}

def cubicAlpha (n j : ℕ) : ℕ := (2 * n ^ 2 + 1) * j + j ^ 2

theorem cubicAlpha_strictMono (n : ℕ) : StrictMono (cubicAlpha n) := by
  intro a b hab
  dsimp [cubicAlpha]
  nlinarith [sq_nonneg (b - a)]

theorem cubic_differences (j k j' k' : Fin n) (hjk : j ≠ k) (_hj'k' : j' ≠ k')
    (h : (cubicAlpha n k : ℤ) - cubicAlpha n j =
      (cubicAlpha n k' : ℤ) - cubicAlpha n j') : j = j' ∧ k = k' := by
  have hj : (j : ℤ) < n := by exact_mod_cast j.isLt
  have hk : (k : ℤ) < n := by exact_mod_cast k.isLt
  have hj' : (j' : ℤ) < n := by exact_mod_cast j'.isLt
  have hk' : (k' : ℤ) < n := by exact_mod_cast k'.isLt
  have j0 : (0 : ℤ) ≤ j := by positivity
  have k0 : (0 : ℤ) ≤ k := by positivity
  have j'0 : (0 : ℤ) ≤ j' := by positivity
  have k'0 : (0 : ℤ) ≤ k' := by positivity
  have n0 : (0 : ℤ) ≤ n := by positivity
  simp only [cubicAlpha, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_pow, Nat.cast_one] at h
  have hj2 : (j : ℤ)^2 ≤ (n : ℤ)^2 := by nlinarith
  have hk2 : (k : ℤ)^2 ≤ (n : ℤ)^2 := by nlinarith
  have hj'2 : (j' : ℤ)^2 ≤ (n : ℤ)^2 := by nlinarith
  have hk'2 : (k' : ℤ)^2 ≤ (n : ℤ)^2 := by nlinarith
  have hd : (k : ℤ) - j = (k' : ℤ) - j' := by
    by_contra he
    rcases lt_or_gt_of_ne he with hh | hh
    · have hg : (k : ℤ) - j + 1 ≤ (k' : ℤ) - j' := by omega
      have := mul_nonneg (by positivity : (0 : ℤ) ≤ 2 * (n : ℤ)^2 + 1)
        (show 0 ≤ (k' : ℤ) - j' - ((k : ℤ) - j) - 1 by omega)
      nlinarith [sq_nonneg (j : ℤ), sq_nonneg (k : ℤ),
        sq_nonneg (j' : ℤ), sq_nonneg (k' : ℤ)]
    · have hg : (k' : ℤ) - j' + 1 ≤ (k : ℤ) - j := by omega
      have := mul_nonneg (by positivity : (0 : ℤ) ≤ 2 * (n : ℤ)^2 + 1)
        (show 0 ≤ (k : ℤ) - j - ((k' : ℤ) - j') - 1 by omega)
      nlinarith [sq_nonneg (j : ℤ), sq_nonneg (k : ℤ),
        sq_nonneg (j' : ℤ), sq_nonneg (k' : ℤ)]
  have hd0 : (k : ℤ) - j ≠ 0 := by
    intro hz
    apply hjk
    apply Fin.ext
    exact_mod_cast (show (j : ℤ) = k by omega)
  have he : ((k : ℤ) - j) * ((k : ℤ) + j) =
      ((k : ℤ) - j) * ((k' : ℤ) + j') := by nlinarith [h, hd]
  have hs := mul_left_cancel₀ hd0 he
  constructor <;> apply Fin.ext <;> omega

/-- A fully proved, explicit polynomial-size alternative to Lemma `lem:sidon`. -/
def cubic (n : ℕ) : SidonPositions n where
  α j := cubicAlpha n j
  c := cubicAlpha n (n - 1)
  bound j := (cubicAlpha_strictMono n).monotone (by omega)
  strictMono := fun _ _ h => cubicAlpha_strictMono n h
  differences := cubic_differences

@[simp] theorem cubic_zero (n : ℕ) (hn : 0 < n) :
    (cubic n).α ⟨0, hn⟩ = 0 := by simp [cubic, cubicAlpha]

theorem cubic_size (n : ℕ) : (cubic n).c ≤ 3 * n ^ 3 + n := by
  dsimp [cubic, cubicAlpha]
  have h : n - 1 ≤ n := by omega
  have h2 : (n - 1)^2 ≤ n^2 := Nat.pow_le_pow_left h 2
  have hm := Nat.mul_le_mul_left (2 * n ^ 2 + 1) h
  by_cases hn : n = 0
  · subst n; simp
  · have hn1 : 1 ≤ n := by omega
    have hn2 : n ^ 2 ≤ n ^ 3 := by nlinarith [Nat.mul_le_mul_left (n^2) hn1]
    nlinarith

/-- The exact Erdős–Turán formula from the paper (zero-based). -/
def erdosTuranAlpha (p j : ℕ) : ℕ := 2 * p * j + j ^ 2 % p

theorem erdosTuran_zero (p : ℕ) : erdosTuranAlpha p 0 = 0 := by
  simp [erdosTuranAlpha]

theorem erdosTuran_strictMono {p : ℕ} (hp : 0 < p) : StrictMono (erdosTuranAlpha p) := by
  intro a b hab
  have ha := Nat.mod_lt (a ^ 2) hp
  have hb := Nat.mod_lt (b ^ 2) hp
  dsimp [erdosTuranAlpha]
  have hm := Nat.mul_le_mul_left (2 * p) (show a + 1 ≤ b by omega)
  rw [Nat.mul_add, Nat.mul_one] at hm
  omega

/-- Nonzero ordered differences in the Erdős–Turán construction are unique. -/
theorem erdosTuran_differences {p : ℕ} (hp : p.Prime) (hodd : 2 < p)
    (hn : n ≤ p) (j k j' k' : Fin n) (hjk : j ≠ k) (_hj'k' : j' ≠ k')
    (h : (erdosTuranAlpha p k : ℤ) - erdosTuranAlpha p j =
      (erdosTuranAlpha p k' : ℤ) - erdosTuranAlpha p j') : j = j' ∧ k = k' := by
  have hp0 : 0 < p := hp.pos
  have rem_bound (a : ℕ) : ((a ^ 2 % p : ℕ) : ℤ) < p := by
    exact_mod_cast Nat.mod_lt (a ^ 2) hp0
  have rem_nonneg (a : ℕ) : (0 : ℤ) ≤ (a ^ 2 % p : ℕ) := by positivity
  have he := h
  simp only [erdosTuranAlpha, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at he
  have hd : (k : ℤ) - j = (k' : ℤ) - j' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hh | hh
    · have hm := mul_nonneg (show (0 : ℤ) ≤ 2 * p by positivity)
        (show 0 ≤ (k' : ℤ) - j' - ((k : ℤ) - j) - 1 by omega)
      nlinarith [rem_bound k, rem_bound j, rem_bound k', rem_bound j',
        rem_nonneg k, rem_nonneg j, rem_nonneg k', rem_nonneg j']
    · have hm := mul_nonneg (show (0 : ℤ) ≤ 2 * p by positivity)
        (show 0 ≤ (k : ℤ) - j - ((k' : ℤ) - j') - 1 by omega)
      nlinarith [rem_bound k, rem_bound j, rem_bound k', rem_bound j',
        rem_nonneg k, rem_nonneg j, rem_nonneg k', rem_nonneg j']
  letI : Fact p.Prime := ⟨hp⟩
  have inj (a b : Fin n) (hab : (a.val : ZMod p) = b.val) : a = b := by
    apply Fin.ext
    have hv := congrArg ZMod.val hab
    simpa [ZMod.val_natCast_of_lt (lt_of_lt_of_le a.isLt hn),
      ZMod.val_natCast_of_lt (lt_of_lt_of_le b.isLt hn)] using hv
  have hd' : (k.val : ZMod p) - j.val = k'.val - j'.val := by
    have hz := congrArg (fun z : ℤ => (z : ZMod p)) hd
    simpa only [Int.cast_sub, Int.cast_natCast] using hz
  have hs : (k.val : ZMod p)^2 - (j.val : ZMod p)^2 =
      (k'.val : ZMod p)^2 - (j'.val : ZMod p)^2 := by
    have hz := congrArg (fun z : ℤ => (z : ZMod p)) h
    simpa [erdosTuranAlpha, ZMod.natCast_mod] using hz
  have hnon : (k.val : ZMod p) - j.val ≠ 0 := by
    intro hz
    exact hjk (inj k j (sub_eq_zero.mp hz)).symm
  have hprod : ((k.val : ZMod p) - j.val) * (k.val + j.val) =
      ((k.val : ZMod p) - j.val) * (k'.val + j'.val) := by
    calc
      _ = (k.val : ZMod p)^2 - (j.val : ZMod p)^2 := by ring
      _ = (k'.val : ZMod p)^2 - (j'.val : ZMod p)^2 := hs
      _ = ((k'.val : ZMod p) - j'.val) * (k'.val + j'.val) := by ring
      _ = _ := by rw [hd']
  have hsum := mul_left_cancel₀ hnon hprod
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hv := congrArg ZMod.val hz
    have ht := ZMod.val_natCast_of_lt hodd
    norm_num at ht
    simpa [ht] using hv
  have hj' : (j.val : ZMod p) = j'.val := by
    apply mul_left_cancel₀ htwo
    linear_combination hsum - hd'
  have hk' : (k.val : ZMod p) = k'.val := by
    rw [hj'] at hd'
    linear_combination hd'
  exact ⟨inj j j' hj', inj k k' hk'⟩

/-- Bertrand with the endpoints needed by the paper. The singleton case uses
p = 3, since there is no odd prime in [1,2). -/
theorem exists_erdosTuranPrime (n : ℕ) :
    ∃ p, p.Prime ∧ 2 < p ∧ n ≤ p ∧ p < 2 * max n 2 := by
  by_cases hn : n ≤ 2
  · exact ⟨3, by norm_num, by omega, by omega, by omega⟩
  · obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (n - 1) (by omega)
    exact ⟨p, hp, by omega, by omega, by omega⟩

/-- A deterministic finite prime search. -/
def erdosTuranPrime (n : ℕ) : ℕ := Nat.find (exists_erdosTuranPrime n)

theorem erdosTuranPrime_spec (n : ℕ) :
    (erdosTuranPrime n).Prime ∧ 2 < erdosTuranPrime n ∧
      n ≤ erdosTuranPrime n ∧ erdosTuranPrime n < 2 * max n 2 :=
  Nat.find_spec (exists_erdosTuranPrime n)

/-- The quadratic-size Sidon positions of paper Lemma `lem:sidon`. -/
def erdosTuran (n : ℕ) : SidonPositions n where
  α j := erdosTuranAlpha (erdosTuranPrime n) j
  c := erdosTuranAlpha (erdosTuranPrime n) (n - 1)
  bound j := (erdosTuran_strictMono (by have := (erdosTuranPrime_spec n).2.1; omega)).monotone
    (by omega)
  strictMono := fun _ _ h => erdosTuran_strictMono
    (by have := (erdosTuranPrime_spec n).2.1; omega) h
  differences := erdosTuran_differences (erdosTuranPrime_spec n).1
    (erdosTuranPrime_spec n).2.1 (erdosTuranPrime_spec n).2.2.1

@[simp] theorem erdosTuran_origin (n : ℕ) (hn : 0 < n) :
    (erdosTuran n).α ⟨0, hn⟩ = 0 := erdosTuran_zero _

theorem erdosTuran_size (n : ℕ) : (erdosTuran n).c ≤ 4 * n ^ 2 := by
  have hp := erdosTuranPrime_spec n
  by_cases hn : n ≤ 1
  · have hz : n - 1 = 0 := by omega
    simp [erdosTuran, hz, erdosTuran_zero]
  · have hb : erdosTuranPrime n < 2 * n := by omega
    have hr := Nat.mod_lt ((n - 1)^2) (show 0 < erdosTuranPrime n by omega)
    have hm := Nat.mul_le_mul_left (2 * erdosTuranPrime n) (show n - 1 + 1 = n by omega).le
    dsimp [erdosTuran, erdosTuranAlpha]
    nlinarith [Nat.mul_le_mul_right n (show erdosTuranPrime n ≤ 2 * n by omega)]

/-- For non-singleton inputs the chosen odd prime lies in [n,2n). -/
theorem erdosTuranPrime_interval (hn : 2 ≤ n) :
    n ≤ erdosTuranPrime n ∧ erdosTuranPrime n < 2 * n := by
  have hp := erdosTuranPrime_spec n
  exact ⟨hp.2.2.1, by omega⟩

/-- The matching quadratic lower bound in paper Lemma `lem:sidon`. -/
theorem erdosTuran_size_lower (n : ℕ) : 2 * n * (n - 1) ≤ (erdosTuran n).c := by
  have hp := (erdosTuranPrime_spec n).2.2.1
  have hm := Nat.mul_le_mul_right (n - 1) (Nat.mul_le_mul_left 2 hp)
  dsimp [erdosTuran, erdosTuranAlpha]
  omega

end SidonPositions
end Hardness
