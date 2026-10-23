import Hardness.Lattice

/-! # Separated positions

The coordinate proofs only use the `SidonPositions` interface. We also give an
explicit elementary cubic-size construction, avoiding a prime search. It uses
α_j = (2n²+1)j+j² for zero-based j. This replaces the paper's quadratic-size
Erdős–Turán construction; the dimension bound consequently becomes O(M n³),
which is still polynomial. No Sidon property is postulated as an axiom.
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

/-- The exact Erdős–Turán formula from the paper (zero-based). The reduction
below uses `cubic`, whose difference property is proved above. -/
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

end SidonPositions
end Hardness
