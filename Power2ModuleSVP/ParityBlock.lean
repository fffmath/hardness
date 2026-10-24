import Power2ModuleSVP.Problem

/-!
Coefficient arithmetic for `lem:parity-block`. Congruence to one below means
congruence to the constant polynomial, not to the all-one coefficient vector.
-/
namespace Power2ModuleSVP
open IdealCVP.Cyclotomic

/-- The constant polynomial one in the coefficient model. -/
def coeffOne {d : ℕ} (hd : 0 < d) : Coeff d := monomial ⟨0, hd⟩ 1

@[simp]theorem mul_coeffOne {d : ℕ} (hd : 0 < d) (a : Coeff d) :
    mul (coeffOne hd) a = a := by
  funext r
  rw [coeffOne, mul_monomial_left]
  simp [Nat.mod_eq_of_lt, ← Fin.ext_iff]

@[simp]theorem mul_coeffOne_right {d : ℕ} (hd : 0 < d) (a : Coeff d) :
    mul a (coeffOne hd) = a := by rw [mul_comm, mul_coeffOne]

theorem coeff_mul_assoc {d : ℕ} (hd : 0 < d) (a b c : Coeff d) :
    mul (mul a b) c = mul a (mul b c) := by
  apply (toQuot_bijective hd).injective
  simp only [toQuot_mul hd, _root_.mul_assoc]

@[simp]theorem coeff_mul_zero_left {d : ℕ} (a : Coeff d) : mul 0 a = 0 := by
  rw [mul_comm, mul_zero]

@[simp]theorem coeff_mul_neg_left {d : ℕ} (a b : Coeff d) :
    mul (-a) b = -mul a b := by rw [mul_comm, mul_neg, mul_comm]

theorem coeff_mul_sub_left {d : ℕ} (a b c : Coeff d) :
    mul (a - b) c = mul a c - mul b c := by
  simp only [sub_eq_add_neg, mul_add_left, coeff_mul_neg_left]

theorem Cube.neg {d : ℕ} {a : Coeff d} (h : Cube a) : Cube (-a) := by
  intro i
  simpa using h i

/-- A monomial is a signed permutation, also for the coefficient maximum norm. -/
theorem cube_monomial_mul_iff {d : ℕ} (e : Fin d) (a : Coeff d) :
    Cube (mul (monomial e 1) a) ↔ Cube a := by
  have hd : 0 < d := by have := e.isLt; omega
  letI : NeZero d := ⟨by omega⟩
  have hinj : Function.Injective (fun j : Fin d => e + j) :=
    fun _ _ h => add_left_cancel h
  have heq : mul (monomial e 1) a = sparse (fun j : Fin d => e + j)
      (fun j => (if e.val + j.val < d then 1 else -1) * a j) := by
    funext r
    rw [mul_monomial_left, sparse_apply]
    apply Finset.sum_congr rfl
    intro j _
    have hc : (e.val + j.val) % d = r.val ↔ r = e + j := by
      simp only [Fin.ext_iff, Fin.val_add]
      omega
    simp only [hc, mul_one]
  have hat (j : Fin d) : |mul (monomial e 1) a (e+j)| = |a j| := by
    rw [heq, sparse_at hinj]
    split_ifs <;> simp
  constructor
  · intro h j
    simpa only [hat] using h (e+j)
  · intro h r
    obtain ⟨j, rfl⟩ := (Equiv.addLeft e).surjective r
    change |mul (monomial e 1) a (e+j)| ≤ 1
    rw [hat]
    exact h j

theorem SignedMonomial.cube_mul_iff {d : ℕ} {v : Coeff d}
    (hv : SignedMonomial v) (a : Coeff d) : Cube (mul v a) ↔ Cube a := by
  obtain ⟨j, rfl | rfl⟩ := hv
  · exact cube_monomial_mul_iff j a
  · rw [coeff_mul_neg_left]
    constructor
    · intro h
      exact (cube_monomial_mul_iff j a).mp (by simpa using h.neg)
    · intro h
      exact ((cube_monomial_mul_iff j a).mpr h).neg

/-- Integral bounded even vectors vanish. -/
theorem even_cube_eq_zero {d : ℕ} {a : Coeff d} (ha : EvenCoeffs a)
    (hc : Cube a) : a = 0 := by
  funext i
  obtain ⟨z, hz⟩ := ha i
  have hi := abs_le.mp (hc i)
  change a i = 0
  omega

theorem even_mul_left {d : ℕ} {g : Coeff d} (hg : EvenCoeffs g)
    (u : Coeff d) : EvenCoeffs (mul g u) := by
  intro r
  unfold mul
  apply Finset.even_sum
  intro i _
  apply Finset.even_sum
  intro j _
  by_cases hm : (i.val + j.val) % d = r.val
  · simp only [hm, ite_true]
    exact ((hg i).mul_left _).mul_right _
  · simp only [hm, ite_false]
    exact ⟨0, rfl⟩

/-- A general version of the parity-block estimate: an integral left inverse
up to the scalar two suffices. The monomial may shift by an entire block. -/
theorem parity_block_bound {d : ℕ} (hd : 0 < d) (F M v : Coeff d)
    (hM : SignedMonomial M)
    (hF : mul (coeffOne hd - M) F = (2 : ℤ) • coeffOne hd)
    (hE : Cube (mul F v)) : Cube v := by
  have hid : (2 : ℤ) • v = mul F v - mul M (mul F v) := by
    calc
      _ = mul ((2 : ℤ) • coeffOne hd) v := by rw [mul_smul_left, mul_coeffOne]
      _ = mul (mul (coeffOne hd - M) F) v := by rw [hF]
      _ = _ := by rw [coeff_mul_assoc hd, coeff_mul_sub_left, mul_coeffOne]
  have hshift := (hM.cube_mul_iff (mul F v)).mpr hE
  intro i
  have hi := congrFun hid i
  have h1 := abs_le.mp (hE i)
  have h2 := abs_le.mp (hshift i)
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hi
  exact abs_le.mpr (by constructor <;> omega)

/-- The forced parity pattern has signs at odd positions and zero elsewhere. -/
theorem parity_block_forcing {d : ℕ} (hd : 0 < d) (F M v H : Coeff d)
    (hM : SignedMonomial M)
    (hF : mul (coeffOne hd - M) F = (2 : ℤ) • coeffOne hd)
    (hE : Cube (mul F v)) (hp : EvenCoeffs (v-H)) :
    ∀ i, (Odd (H i) → v i = -1 ∨ v i = 1) ∧
      (Even (H i) → v i = 0) := by
  have hc := parity_block_bound hd F M v hM hF hE
  intro i
  have hb := abs_le.mp (hc i)
  have he := hp i
  simp only [Pi.sub_apply] at he
  obtain ⟨z, hz⟩ := he
  constructor
  · rintro ⟨t, ht⟩
    omega
  · rintro ⟨t, ht⟩
    omega


/-- The full geometric word in the negacyclic coefficient model. -/
def geometricWord (d : ℕ) : Coeff d := fun _ => 1

/-- `lem:parity-block`, without a restriction on the positive degree. -/
theorem parity_block {d : ℕ} (hd : 0 < d) (v : Coeff d)
    (hE : Cube (mul (geometricWord d) v)) : Cube v := by
  by_cases hd1 : d = 1
  · subst d
    have hone : geometricWord 1 = coeffOne (by decide : 0 < 1) := by
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      simp [geometricWord, coeffOne, monomial, hi]
    simpa only [hone, mul_coeffOne] using hE
  · have htwo : 1 < d := by omega
    let M : Coeff d := monomial ⟨1,htwo⟩ 1
    have hid : mul (coeffOne hd-M) (geometricWord d) = (2 : ℤ) • coeffOne hd := by
      rw [coeff_mul_sub_left, mul_coeffOne, mul_y]
      ext i
      by_cases hi : i.val = 0 <;>
        simp [geometricWord,coeffOne,monomial,shift,Fin.ext_iff,hi]
    exact parity_block_bound hd _ M v ⟨⟨1,htwo⟩,Or.inl rfl⟩ hid hE

/-- The zero-parity consequence of the geometric-word estimate. -/
theorem parity_block_even {d : ℕ} (hd : 0 < d) (v : Coeff d)
    (hE : Cube (mul (geometricWord d) v)) (hp : EvenCoeffs v) : v = 0 :=
  even_cube_eq_zero hp (parity_block hd v hE)

/-- Congruence to the constant polynomial one forces a signed constant. -/
theorem parity_block_one {d : ℕ} (hd : 0 < d) (v : Coeff d)
    (hE : Cube (mul (geometricWord d) v))
    (hp : EvenCoeffs (v-coeffOne hd)) : v = coeffOne hd ∨ v = -coeffOne hd := by
  have hc := parity_block hd v hE
  have hb := abs_le.mp (hc ⟨0,hd⟩)
  obtain ⟨z,hz⟩ := hp ⟨0,hd⟩
  simp only [Pi.sub_apply, coeffOne, monomial_self] at hz
  have hv0 : v ⟨0,hd⟩ = 1 ∨ v ⟨0,hd⟩ = -1 := by omega
  have hout (i : Fin d) (hi : i.val ≠ 0) : v i = 0 := by
    have hb := abs_le.mp (hc i)
    obtain ⟨z,hz⟩ := hp i
    have hi' : i ≠ ⟨0,hd⟩ := by
      intro he
      exact hi (congrArg Fin.val he)
    simp [coeffOne,monomial,hi'] at hz
    omega
  rcases hv0 with hv | hv
  · left
    ext i
    by_cases hi : i.val = 0
    · have he : i = ⟨0,hd⟩ := Fin.ext hi
      simpa [he,coeffOne] using hv
    · simp [coeffOne,monomial,Fin.ext_iff,hi,hout i hi]
  · right
    ext i
    by_cases hi : i.val = 0
    · have he : i = ⟨0,hd⟩ := Fin.ext hi
      simpa [he,coeffOne] using hv
    · simp [coeffOne,monomial,Fin.ext_iff,hi,hout i hi]

end Power2ModuleSVP
