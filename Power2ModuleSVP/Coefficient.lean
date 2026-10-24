import IdealCVP.Complexity.GeneralModule

/-! Coefficient predicates in the existing negacyclic coefficient model. -/
namespace Power2ModuleSVP

abbrev Coeff := IdealCVP.Coeff
abbrev Rd := IdealCVP.Cyclotomic.QuotRing

def Dyadic (d : ℕ) : Prop := ∃ k : ℕ, d = 2^k
def Cube {d : ℕ} (a : Coeff d) : Prop := ∀ i, |a i| ≤ 1
def Signs {d : ℕ} (a : Coeff d) : Prop := ∀ i, a i = -1 ∨ a i = 1
def Bits {d : ℕ} (a : Coeff d) : Prop := ∀ i, a i = 0 ∨ a i = 1
def EvenCoeffs {d : ℕ} (a : Coeff d) : Prop := ∀ i, Even (a i)
def SignedMonomial {d : ℕ} (a : Coeff d) : Prop :=
  ∃ j : Fin d, a = IdealCVP.Cyclotomic.monomial j 1 ∨
    a = -IdealCVP.Cyclotomic.monomial j 1
def Rigid {d : ℕ} (J : Coeff d) : Prop :=
  ∀ v : Coeff d, Cube (IdealCVP.Cyclotomic.mul J v) →
    v = 0 ∨ SignedMonomial v

def coeffSup {d : ℕ} (a : Coeff d) : ℕ := Finset.univ.sup (fun i => (a i).natAbs)
def pairSup {d : ℕ} (z : Coeff d × Coeff d) : ℕ := max (coeffSup z.1) (coeffSup z.2)

theorem Dyadic.pos {d : ℕ} (hd : Dyadic d) : 0 < d := by
  obtain ⟨k, rfl⟩ := hd
  positivity

theorem Signs.cube {d : ℕ} {a : Coeff d} (ha : Signs a) : Cube a := by
  intro i
  rcases ha i with h | h <;> simp [h]

theorem Bits.cube {d : ℕ} {a : Coeff d} (ha : Bits a) : Cube a := by
  intro i
  rcases ha i with h | h <;> simp [h]

theorem Signs.ne_zero {d : ℕ} (hd : 0 < d) {a : Coeff d} (ha : Signs a) : a ≠ 0 := by
  intro h
  rcases ha ⟨0, hd⟩ with hi | hi <;> simp [h] at hi

theorem cube_iff_coeffSup_le {d : ℕ} (a : Coeff d) : Cube a ↔ coeffSup a ≤ 1 := by
  simp only [coeffSup, Finset.sup_le_iff, Finset.mem_univ, forall_const, Cube]
  constructor
  · intro h i
    exact_mod_cast (show (a i).natAbs ≤ (1 : ℤ) from by simpa using h i)
  · intro h i
    have := h i
    have hi : ((a i).natAbs : ℤ) ≤ 1 := by exact_mod_cast this
    simpa only [Int.natCast_natAbs] using hi

theorem Cube.sqNorm_le {d : ℕ} {a : Coeff d} (ha : Cube a) :
    IdealCVP.sqNorm a ≤ (d : ℤ) := by
  calc
    _ ≤ ∑ _i : Fin d, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := abs_le.mp (ha i)
      nlinarith
    _ = _ := by simp

end Power2ModuleSVP
