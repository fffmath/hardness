import IdealCVP.Sidon

/-!
# One-based quadratic Sidon positions

This reuses the proved quadratic construction in `IdealCVP.Sidon` and exposes
precisely the indexing needed for `prop:sidon-source`. No new number-theoretic
assumption is introduced. For the strict prime interval assume `2 ≤ v`; the
positive exactly-one gadget has at least four variables.
-/
namespace Power2ModuleSVP
namespace Sidon

/-- Paper positions, indexed by the integers `1,…,v` via `Fin v`. -/
def position (ell : ℕ) {v : ℕ} (i : Fin v) : ℕ :=
  IdealCVP.SidonPositions.erdosTuranAlpha ell (i.val + 1)

/-- A finite, deterministic search; the lower endpoint is strictly above `v`. -/
def prime (v : ℕ) : ℕ := IdealCVP.SidonPositions.erdosTuranPrime (v + 1)

theorem prime_spec (v : ℕ) :
    (prime v).Prime ∧ 2 < prime v ∧ v < prime v ∧
      prime v < 2 * max (v + 1) 2 := by
  unfold prime
  have h := IdealCVP.SidonPositions.erdosTuranPrime_spec (v + 1)
  exact ⟨h.1, h.2.1, by omega, h.2.2.2⟩

/-- A sharper strict interval, using Bertrand directly at `v`. -/
theorem exists_prime_interval {v : ℕ} (hv : 2 ≤ v) :
    ∃ ell, ell.Prime ∧ 2 < ell ∧ v < ell ∧ ell < 2 * v := by
  obtain ⟨ell, hp, hlo, hhi⟩ := Nat.bertrand v (by omega)
  have hne : ell ≠ 2 * v := by
    intro he
    have hd : 2 ∣ ell := he ▸ dvd_mul_right 2 v
    have := (Nat.dvd_prime hp).mp hd
    rcases this with h | h
    · omega
    · omega
  exact ⟨ell, hp, by omega, hlo, by omega⟩

/-- Upper endpoint of the positions, also meaningful for the empty instance. -/
def bound (ell v : ℕ) : ℕ :=
  IdealCVP.SidonPositions.erdosTuranAlpha ell v

theorem strictMono {ell v : ℕ} (hell : 0 < ell) :
    StrictMono (position ell : Fin v → ℕ) := by
  intro i j hij
  exact IdealCVP.SidonPositions.erdosTuran_strictMono hell (by simpa using hij)

theorem position_le_bound {ell v : ℕ} (hell : 0 < ell) (i : Fin v) :
    position ell i ≤ bound ell v :=
  (IdealCVP.SidonPositions.erdosTuran_strictMono hell).monotone (by omega)

theorem position_pos {ell v : ℕ} (hell : 0 < ell) (i : Fin v) :
    0 < position ell i := by
  have h := IdealCVP.SidonPositions.erdosTuran_strictMono hell
    (show 0 < i.val + 1 by omega)
  simpa [position, IdealCVP.SidonPositions.erdosTuran_zero] using h

theorem bound_lt {ell v : ℕ} (hell : 0 < ell) (hhi : ell < 2 * v) :
    bound ell v < 4 * v ^ 2 + 2 * v := by
  have hr := Nat.mod_lt (v ^ 2) hell
  have hm := Nat.mul_le_mul_right v (show 2 * ell ≤ 4 * v by omega)
  dsimp [bound, IdealCVP.SidonPositions.erdosTuranAlpha]
  nlinarith

theorem differences {ell v : ℕ} (hp : ell.Prime) (hodd : 2 < ell)
    (hv : v < ell) (i j k l : Fin v) (hij : i ≠ j) (hkl : k ≠ l)
    (he : (position ell j : ℤ) - position ell i =
      (position ell l : ℤ) - position ell k) : i = k ∧ j = l := by
  let lift : Fin v → Fin (v + 1) := fun a => ⟨a.val + 1, by omega⟩
  have hinj : Function.Injective lift := by
    intro a b h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp [lift] at this
    omega
  have h := IdealCVP.SidonPositions.erdosTuran_differences hp hodd
    (show v + 1 ≤ ell by omega) (lift i) (lift j) (lift k) (lift l)
    (fun h => hij (hinj h)) (fun h => hkl (hinj h)) he
  exact ⟨hinj h.1, hinj h.2⟩

/-- Unordered pair-sum uniqueness includes repeated indices. -/
theorem pair_sums {ell v : ℕ} (hp : ell.Prime) (hodd : 2 < ell)
    (hv : v < ell) (i j k l : Fin v)
    (he : position ell i + position ell j = position ell k + position ell l) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  have hinj := (strictMono (v := v) hp.pos).injective
  by_cases hik : i = k
  · subst k
    exact Or.inl ⟨rfl, hinj (by omega)⟩
  · have hjl : j ≠ l := by
      intro hjl
      subst l
      exact hik (hinj (by omega))
    have hz : (position ell i : ℤ) - position ell k =
        (position ell l : ℤ) - position ell j := by omega
    have h := differences hp hodd hv k i j l (Ne.symm hik) hjl hz
    exact Or.inr ⟨h.2, h.1.symm⟩

end Sidon
end Power2ModuleSVP
