import Hardness.Sidon

/-! # Row and cross-term positions

The separation arguments in the proof of Lemma `lem:boolean-identity` and the
following unnumbered distinct-monomials lemma. All exponents are natural numbers;
bounds ensure that subtraction never truncates and that reduction modulo x^N+1
does not change the coefficients.
-/
namespace Hardness
namespace SidonPositions
variable {M n : ℕ} (p : SidonPositions n)

def L : ℕ := 2 * p.c + 1

def ρ (i : Fin M) : ℕ := p.c + i.val * p.L

def hExp (i : Fin M) (j : Fin n) : ℕ := p.ρ i - p.α j

def crossExp (i : Fin M) (j k : Fin n) : ℕ := p.hExp i j + p.α k

def N (M : ℕ) : ℕ := 2 ^ Nat.clog 2 (M * p.L)

theorem L_pos : 0 < p.L := by dsimp [L]; omega

theorem N_bound : M * p.L ≤ p.N M := by
  exact Nat.le_pow_clog (by decide) _

theorem N_pos : 0 < p.N M := by unfold N; positivity

theorem hExp_interval (i : Fin M) (j : Fin n) :
    i.val * p.L ≤ p.hExp i j ∧ p.hExp i j < (i.val + 1) * p.L := by
  have := p.bound j
  dsimp [hExp, ρ, L]
  simp only [Nat.add_mul, Nat.one_mul]
  constructor <;> omega

theorem crossExp_interval (i : Fin M) (j k : Fin n) :
    i.val * p.L ≤ p.crossExp i j k ∧ p.crossExp i j k < (i.val + 1) * p.L := by
  have := p.bound j
  have := p.bound k
  dsimp [crossExp, hExp, ρ, L]
  simp only [Nat.add_mul, Nat.one_mul]
  constructor <;> omega

theorem row_interval (i : Fin M) :
    i.val * p.L ≤ p.ρ i ∧ p.ρ i < (i.val + 1) * p.L := by
  dsimp [ρ, L]
  simp only [Nat.add_mul, Nat.one_mul]
  constructor <;> omega

/-- Disjoint intervals [iL,(i+1)L) identify the row. -/
theorem interval_unique {i i' : Fin M} {e : ℕ}
    (h : i.val * p.L ≤ e ∧ e < (i.val + 1) * p.L)
    (h' : i'.val * p.L ≤ e ∧ e < (i'.val + 1) * p.L) : i = i' := by
  apply Fin.ext
  by_contra hn
  rcases lt_or_gt_of_ne hn with hh | hh
  · have := Nat.mul_le_mul_right p.L (show i.val + 1 ≤ i'.val by omega)
    omega
  · have := Nat.mul_le_mul_right p.L (show i'.val + 1 ≤ i.val by omega)
    omega

theorem hExp_injective : Function.Injective (fun z : Fin M × Fin n => p.hExp z.1 z.2) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ he
  change p.hExp i j = p.hExp i' j' at he
  have hi : i = i' := p.interval_unique (p.hExp_interval i j) (he ▸ p.hExp_interval i' j')
  subst i'
  have hb := p.bound j
  have hb' := p.bound j'
  have hj : p.α j = p.α j' := by dsimp [hExp, ρ] at he; omega
  have := p.strictMono.injective hj
  simp_all

theorem crossExp_injective {i i' : Fin M} {j k j' k' : Fin n}
    (hjk : j ≠ k) (hjk' : j' ≠ k')
    (he : p.crossExp i j k = p.crossExp i' j' k') :
    i = i' ∧ j = j' ∧ k = k' := by
  have hi : i = i' := p.interval_unique (p.crossExp_interval i j k)
    (he ▸ p.crossExp_interval i' j' k')
  subst i'
  have hb := p.bound j
  have hb' := p.bound j'
  have hd : (p.α k : ℤ) - p.α j = (p.α k' : ℤ) - p.α j' := by
    dsimp [crossExp, hExp, ρ] at he
    omega
  exact ⟨rfl, p.differences j k j' k' hjk hjk' hd⟩

theorem row_ne_cross (i i' : Fin M) (j k : Fin n) (hjk : j ≠ k) :
    p.ρ i ≠ p.crossExp i' j k := by
  intro he
  have hi : i = i' := p.interval_unique (p.row_interval i)
    (he ▸ p.crossExp_interval i' j k)
  subst i'
  have hb := p.bound j
  have hjk' : p.α j ≠ p.α k := fun h => hjk (p.strictMono.injective h)
  dsimp [crossExp, hExp, ρ] at he
  omega

theorem row_injective : Function.Injective (p.ρ (M := M)) := by
  intro i i' h
  exact p.interval_unique (p.row_interval i) (h ▸ p.row_interval i')

theorem interval_lt_N (i : Fin M) {e : ℕ}
    (he : e < (i.val + 1) * p.L) : e < p.N M := by
  have h := Nat.mul_le_mul_right p.L (show i.val + 1 ≤ M by omega)
  have := p.N_bound (M := M)
  omega

theorem hExp_lt_N (i : Fin M) (j : Fin n) : p.hExp i j < p.N M :=
  p.interval_lt_N i (p.hExp_interval i j).2

theorem crossExp_lt_N (i : Fin M) (j k : Fin n) : p.crossExp i j k < p.N M :=
  p.interval_lt_N i (p.crossExp_interval i j k).2

theorem row_lt_N (i : Fin M) : p.ρ i < p.N M :=
  p.interval_lt_N i (p.row_interval i).2

theorem alpha_lt_N (hM : 0 < M) (j : Fin n) : p.α j < p.N M := by
  have hr := p.row_lt_N (⟨0, hM⟩ : Fin M)
  have hb := p.bound j
  have hc : p.c < p.N M := by simpa [ρ] using hr
  omega

end SidonPositions
end Hardness
