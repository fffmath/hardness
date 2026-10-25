import IdealCVP.Lattice

/-! # Negacyclic coefficient arithmetic

`R d` is the degree-<d coefficient model for ℤ[y]/(y ^ d+1).
`mul` is ordinary convolution with each exponent ≥d folded back with a minus
sign. The reduction uses powers of two, but this arithmetic makes sense for
any d. We use the additive image of multiplication for the principal ideal
lattice; no unproved ring instance or domain instance is installed.
-/
namespace IdealCVP.Cyclotomic
open IdealCVP

/-- Integral coefficients of degree below the negacyclic dimension. -/
abbrev R (d : ℕ) := Coeff d

/-- Negacyclic multiplication, in the coefficient embedding. -/
def mul {d : ℕ} (f g : R d) : R d := fun r =>
  ∑ i : Fin d, ∑ j : Fin d,
    if (i.val + j.val) % d = r.val then
      (if i.val + j.val < d then 1 else - 1) * f i * g j else 0

@[simp] theorem mul_zero {d : ℕ} (f : R d) : mul f 0 = 0 := by
  funext r; simp [mul]

theorem mul_add {d : ℕ} (f a b : R d) : mul f (a + b) = mul f a + mul f b := by
  funext r
  simp only [mul, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  split_ifs <;> simp [_root_.mul_add]

@[simp] theorem mul_neg {d : ℕ} (f a : R d) : mul f (-a) = - mul f a := by
  funext r
  simp only [mul, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro j _
  split_ifs <;> simp

/-- Multiplication by a fixed generator as an additive homomorphism. -/
def mulHom {d : ℕ} (g : R d) : R d →+ R d where
  toFun := mul g
  map_zero' := mul_zero g
  map_add' := mul_add g

/-- The honest principal ideal coefficient lattice {gq : q ∈ R_d}. -/
def principalIdealLattice {d : ℕ} (g : R d) : AddSubgroup (Coeff d) :=
  (mulHom g).range

/-- A vector belongs to the principal lattice exactly when it is a multiple of the generator. -/
@[simp] theorem mem_principalIdealLattice {d : ℕ} (g v : R d) :
    v ∈ principalIdealLattice g ↔ ∃ q, mul g q = v := Iff.rfl

theorem mul_comm {d : ℕ} (f g : R d) : mul f g = mul g f := by
  funext r
  simp only [mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  simp only [Nat.add_comm]
  split_ifs <;> ring

theorem mul_sum_right {ι : Type*} [Fintype ι] {d : ℕ} (f : R d) (a : ι → R d) :
    mul f (∑ i, a i) = ∑ i, mul f (a i) := map_sum (mulHom f) _ _

theorem mul_sum_left {ι : Type*} [Fintype ι] {d : ℕ} (a : ι → R d) (f : R d) :
    mul (∑ i, a i) f = ∑ i, mul (a i) f := by
  simp_rw [mul_comm _ f]
  exact mul_sum_right f a

theorem mul_smul_right {d : ℕ} (f a : R d) (k : ℤ) :
    mul f (k • a) = k • mul f a := map_zsmul (mulHom f) _ _

theorem mul_add_left {d : ℕ} (a b f : R d) : mul (a + b) f = mul a f + mul b f := by
  rw [mul_comm, mul_add]
  simp only [mul_comm f]

theorem mul_smul_left {d : ℕ} (a f : R d) (k : ℤ) :
    mul (k • a) f = k • mul a f := by
  rw [mul_comm, mul_smul_right, mul_comm f a]

/-- A monomial of exponent <d. -/
def monomial {d : ℕ} (e : Fin d) (z : ℤ) : R d := fun r => if r = e then z else 0

@[simp] theorem monomial_self {d : ℕ} (e : Fin d) (z : ℤ) : monomial e z e = z := by
  simp [monomial]

theorem mul_monomial_left {d : ℕ} (e : Fin d) (z : ℤ) (q : R d) (r : Fin d) :
    mul (monomial e z) q r = ∑ j : Fin d,
      if (e.val + j.val) % d = r.val then
        (if e.val + j.val < d then 1 else - 1) * z * q j else 0 := by
  have hs (i j : Fin d) :
      (if (i.val + j.val) % d = r.val then
        (if i.val + j.val < d then (1 : ℤ) else - 1) * monomial e z i * q j else 0) =
      if i = e then (if (i.val + j.val) % d = r.val then
        (if i.val + j.val < d then (1 : ℤ) else - 1) * z * q j else 0) else 0 := by
    by_cases hi : i = e <;> simp [monomial, hi]
  unfold mul
  simp_rw [hs, Finset.sum_ite_irrel]
  simp

/-- Negacyclic multiplication by the variable is a signed shift. -/
def shift {N : ℕ} (hN : 0 < N) (a : R N) : R N := fun r =>
  if r.val = 0 then - a ⟨N - 1, by omega⟩ else a ⟨r.val - 1, by omega⟩

/-- Multiplication by a scalar monomial of degree one is a scaled negacyclic shift. -/
theorem mul_y {d : ℕ} (hd : 1 < d) (z : ℤ) (q : R d) :
    mul (monomial ⟨1, hd⟩ z) q = z • shift (by omega) q := by
  funext r
  rw [mul_monomial_left]
  simp only [Pi.smul_apply, smul_eq_mul, shift]
  by_cases hr : r.val = 0
  · rw [ite_eq_left hr]
    rw [Finset.sum_eq_single (⟨d - 1, by omega⟩ : Fin d)]
    · have hsum : 1 + (d - 1) = d := by omega
      simp [hsum, hr]
    · intro j _ hj
      have hj' : j.val ≠ d - 1 := by intro h; apply hj; exact Fin.ext h
      have hlt : 1 + j.val < d := by omega
      simp [Nat.mod_eq_of_lt hlt, hr]
    · simp
  · rw [ite_eq_right hr]
    rw [Finset.sum_eq_single (⟨r.val - 1, by omega⟩ : Fin d)]
    · have hsum : 1 + (r.val - 1) = r.val := by omega
      simp [hsum, Nat.mod_eq_of_lt r.isLt, r.isLt]
    · intro j _ hj
      have hj' : j.val ≠ r.val - 1 := by intro h; apply hj; exact Fin.ext h
      by_cases hlt : 1 + j.val < d
      · simp [Nat.mod_eq_of_lt hlt, show 1 + j.val ≠ r.val by omega]
      · have he : 1 + j.val = d := by omega
        simp [he, Ne.symm hr]
    · simp

/-- Coefficient pairing of even and odd positions. -/
def interleave {N : ℕ} (a b : R N) : R (2 * N) := fun r =>
  if r.val % 2 = 0 then a ⟨r.val / 2, by omega⟩
  else b ⟨r.val / 2, by omega⟩

@[simp] theorem interleave_even {N : ℕ} (a b : R N) (i : Fin N) :
    interleave a b ⟨2 * i.val, by omega⟩ = a i := by
  simp [interleave]

@[simp] theorem interleave_odd {N : ℕ} (a b : R N) (i : Fin N) :
    interleave a b ⟨2 * i.val + 1, by omega⟩ = b i := by
  simp [interleave, Nat.add_div]

/-- Equality of interleaved vectors determines both parity blocks. -/
theorem interleave_injective {N : ℕ} {a b a' b' : R N}
    (h : interleave a b = interleave a' b') : a = a' ∧ b = b' := by
  constructor
  · funext i
    have := congrFun h (⟨2 * i.val, by omega⟩ : Fin (2 * N))
    simpa using this
  · funext i
    have := congrFun h (⟨2 * i.val + 1, by omega⟩ : Fin (2 * N))
    simpa using this

/-- Every multiplier has the unique even/odd decomposition used in the paper. -/
theorem exists_interleave {N : ℕ} (q : R (2 * N)) :
    ∃ a b, q = interleave a b := by
  refine ⟨(fun i => q ⟨2 * i.val, by omega⟩),
    (fun i => q ⟨2 * i.val + 1, by omega⟩), ?_⟩
  funext r
  dsimp [interleave]
  split_ifs with h <;> congr 1 <;> apply Fin.ext <;> dsimp <;> omega

/-- Squared norm splits orthogonally into even and odd blocks. -/
theorem sqNorm_interleave {N : ℕ} (a b : R N) :
    sqNorm (interleave a b) = sqNorm a + sqNorm b := by
  let he : Fin N × Fin 2 ≃ Fin (2 * N) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm N 2))
  rw [sqNorm, ← he.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  have h0 (i : Fin N) : he (i, 0) = ⟨2 * i.val, by omega⟩ := by
    apply Fin.ext; simp [he, finProdFinEquiv]
  have h1 (i : Fin N) : he (i, 1) = ⟨2 * i.val + 1, by omega⟩ := by
    apply Fin.ext; simp [he, finProdFinEquiv]; omega
  simp_rw [h0, h1, interleave_even, interleave_odd]
  exact Finset.sum_add_distrib

/-- A sum of monomials at injectively indexed positions. -/
def sparse {ι : Type*} [Fintype ι] {d : ℕ} (e : ι → Fin d) (v : ι → ℤ) : R d :=
  ∑ j, monomial (e j) (v j)

theorem sparse_apply {ι : Type*} [Fintype ι] {d : ℕ}
    (e : ι → Fin d) (v : ι → ℤ) (r : Fin d) :
    sparse e v r = ∑ j, if r = e j then v j else 0 := by
  simp [sparse, monomial, Finset.sum_apply]

theorem sparse_at {ι : Type*} [Fintype ι] {d : ℕ}
    {e : ι → Fin d} (he : Function.Injective e) (v : ι → ℤ) (j : ι) :
    sparse e v (e j) = v j := by
  classical
  simp [sparse_apply, he.eq_iff]

/-- Orthogonality of distinct monomials, used in both blocks of the reduction. -/
theorem sqNorm_sparse {ι : Type*} [Fintype ι] {d : ℕ}
    {e : ι → Fin d} (he : Function.Injective e) (v : ι → ℤ) :
    sqNorm (sparse e v) = ∑ j, (v j) ^ 2 := by
  classical
  have h (r : Fin d) : (sparse e v r) ^ 2 =
      ∑ j, if r = e j then (v j) ^ 2 else 0 := by
    by_cases hr : ∃ j, r = e j
    · obtain ⟨j, rfl⟩ := hr
      simp [sparse_at he, he.eq_iff]
    · have hn : ∀ j, r ≠ e j := by simpa using hr
      simp [sparse_apply, hn]
  simp only [sqNorm, h]
  rw [Finset.sum_comm]
  simp

theorem sparse_sub {ι : Type*} [Fintype ι] {d : ℕ}
    (e : ι → Fin d) (v w : ι → ℤ) :
    sparse e (fun j => v j - w j) = sparse e v - sparse e w := by
  funext r
  simp only [sparse_apply, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _
  split_ifs <;> simp

theorem sparse_smul {ι : Type*} [Fintype ι] {d : ℕ}
    (e : ι → Fin d) (k : ℤ) (v : ι → ℤ) :
    sparse e (fun j => k * v j) = k • sparse e v := by
  funext r
  simp only [sparse_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_ite]
  simp

/-- Monomial multiplication when the exponents do not reach the modulus. -/
theorem mul_monomial_of_lt {d : ℕ} (e f : Fin d) (a b : ℤ)
    (h : e.val + f.val < d) :
    mul (monomial e a) (monomial f b) = monomial ⟨e.val + f.val, h⟩ (a * b) := by
  funext r
  have step (i j : Fin d) :
      (if (i.val + j.val) % d = r.val then
        (if i.val + j.val < d then (1 : ℤ) else - 1) *
          monomial e a i * monomial f b j else 0) =
      if i = e then if j = f then
        (if (i.val + j.val) % d = r.val then
          (if i.val + j.val < d then (1 : ℤ) else - 1) * a * b else 0)
        else 0 else 0 := by
    by_cases hi : i = e <;> by_cases hj : j = f <;> simp [monomial, hi, hj]
  unfold mul
  simp_rw [step]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  simp [h, Nat.mod_eq_of_lt h, monomial, Fin.ext_iff, eq_comm]

end IdealCVP.Cyclotomic
