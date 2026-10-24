import IdealCVP.X3C
import IdealCVP.Coordinates
import IdealCVP.Blocks
import IdealCVP.Rounding
import IdealCVP.Norms
import IdealCVP.Penalty

/-! # The masked-system compiler

All coefficients and thresholds below are integral. The construction follows
`principal-ideal.tex`, using any proved `SidonPositions`. The canonical X3C
compiler uses the explicit cubic-size positions in `Sidon.lean`.

## Explicit size and complexity (not a complexity formalization)

Entries and cross terms are finite indexed families of sizes W≤Mn and
ν=(n−1)W≤Mn². The row spacing is L=2c+1 and N is the least power of two
at least ML (equivalently, greater than ρ_{M−1}+c). Thus d=2N<4ML for
ML>1. With the cubic positions c≤3n³+n, d=O(M(n³+1)). The paper's
Erdős–Turán positions improve this to O(Mn²). The definitions of s and P
are exactly the paper's ceiling formulas. Since ‖t‖²=4‖b‖₀+ν, they have
polynomial encoding length. Finite sums, shifts, products and integer square
root ceilings give explicit constructions; no runtime theorem is asserted.
-/
namespace IdealCVP
open IdealCVP.Cyclotomic

structure ReductionData (M n : ℕ) where
  system : MaskedSystem M n
  positions : SidonPositions n
  M_pos : 0 < M
  n_pos : 0 < n

namespace ReductionData
variable {M n : ℕ} (D : ReductionData M n)

abbrev N : ℕ := D.positions.N M
abbrev d : ℕ := 2 * D.N

/-- Nonzero entries of A, with their row and column indices. -/
abbrev Entry := {ij : Fin M × Fin n // D.system.A ij.1 ij.2 = true}

/-- One cross term for every nonzero entry and every other column. -/
abbrev Cross := (e : D.Entry) × {k : Fin n // k ≠ e.val.2}

abbrev Coordinates := Fin M ⊕ D.Cross

def W : ℕ := Fintype.card D.Entry

def ν : ℕ := (n - 1) * D.W

def alpha (j : Fin n) : Fin D.N :=
  ⟨D.positions.α j, D.positions.alpha_lt_N D.M_pos j⟩

def hPosition (e : D.Entry) : Fin D.N :=
  ⟨D.positions.hExp e.val.1 e.val.2, D.positions.hExp_lt_N _ _⟩

def coordinate : D.Coordinates → Fin D.N
  | .inl i => ⟨D.positions.ρ i, D.positions.row_lt_N i⟩
  | .inr ⟨e, k⟩ => ⟨D.positions.crossExp e.val.1 e.val.2 k.val,
      D.positions.crossExp_lt_N _ _ _⟩

theorem alpha_injective : Function.Injective D.alpha := by
  intro j k h
  exact D.positions.strictMono.injective (congrArg Fin.val h)

theorem hPosition_injective : Function.Injective D.hPosition := by
  intro e f h
  apply Subtype.ext
  exact D.positions.hExp_injective (congrArg Fin.val h)

/-- Distinctness and disjointness of all coordinates in (sol). -/
theorem coordinate_injective : Function.Injective D.coordinate := by
  intro z z' h
  cases z with
  | inl i =>
    cases z' with
    | inl i' =>
      exact congrArg Sum.inl (D.positions.row_injective (congrArg Fin.val h))
    | inr z' =>
      exact False.elim (D.positions.row_ne_cross i z'.1.val.1 z'.1.val.2 z'.2.val
        (Ne.symm z'.2.property) (congrArg Fin.val h))
  | inr z =>
    cases z' with
    | inl i' =>
      exact False.elim (D.positions.row_ne_cross i' z.1.val.1 z.1.val.2 z.2.val
        (Ne.symm z.2.property) (congrArg Fin.val h).symm)
    | inr z' =>
      obtain ⟨hi, hj, hk⟩ := D.positions.crossExp_injective
        (Ne.symm z.2.property) (Ne.symm z'.2.property) (congrArg Fin.val h)
      have he : z.1 = z'.1 := Subtype.ext (Prod.ext hi hj)
      have hz : z = z' := by
        cases z; cases z'; dsimp at he hk; subst he
        congr 1; exact Subtype.ext hk
      exact congrArg Sum.inr hz

/-- h(x), a sum of exactly W distinct unit monomials. -/
def h : R D.N := sparse D.hPosition (fun _ => 1)

/-- a_ξ; also used with ξ=μ to obtain u_μ. -/
def a (ξ : Fin n → Bool) : R D.N := sparse D.alpha (fun j => bit (ξ j))

def u : R D.N := D.a D.system.μ

/-- The row coefficients 2b_i and the unit cross-term coefficients. -/
def t : R D.N := sparse D.coordinate (Sum.elim (fun i => 2 * bit (D.system.b i)) (fun _ => 1))

/-- Integer implementation of the nonnegative ceiling of a square root. -/
def ceilSqrt (r : ℕ) : ℕ := Nat.sqrt r + if (Nat.sqrt r)^2 = r then 0 else 1

theorem ceilSqrt_le_iff (r k : ℕ) : ceilSqrt r ≤ k ↔ r ≤ k ^ 2 := by
  have hs := Nat.sqrt_le r
  have ht := Nat.lt_succ_sqrt r
  by_cases he : (Nat.sqrt r)^2 = r
  · simp only [ceilSqrt, he, ite_true, add_zero]
    constructor <;> intro h <;> nlinarith
  · simp only [ceilSqrt, he, ite_false]
    constructor
    · intro h
      have hm := Nat.pow_le_pow_left h 2
      nlinarith
    · intro h
      by_contra hn
      have hk : k ≤ Nat.sqrt r := by omega
      have hm := Nat.pow_le_pow_left hk 2
      apply he
      nlinarith

/-- The computable natural-number definition equals the paper's real ceiling. -/
theorem ceilSqrt_eq (r : ℕ) : ceilSqrt r = ⌈Real.sqrt (r : ℝ)⌉₊ := by
  apply Nat.le_antisymm
  · apply (ceilSqrt_le_iff _ _).mpr
    have h := Nat.le_ceil (Real.sqrt (r : ℝ))
    have hh := (Real.sqrt_le_iff).mp h
    exact_mod_cast hh.2
  · apply Nat.ceil_le.mpr
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · exact_mod_cast (ceilSqrt_le_iff r (ceilSqrt r)).mp le_rfl

def s (_D : ReductionData M n) : ℕ := ceilSqrt (n + 4)

def P : ℕ := 1 + D.s * (D.s * D.W + ceilSqrt (sqNorm D.t).toNat +
  ceilSqrt (D.ν + 4))

/-- g=2h(y²)+2Py, with even/odd coefficient blocks. -/
def g : R D.d := interleave ((2 : ℤ) • D.h)
  (monomial ⟨0, D.positions.N_pos⟩ (2 * (D.P : ℤ)))

/-- T_μ=t(y²)+Py u_μ(y²). -/
def T : R D.d := interleave D.t ((D.P : ℤ) • D.u)

def weight : ℕ := (Finset.univ.filter fun j => D.system.μ j = true).card

def Δ : ℤ := (D.P : ℤ)^2 * D.weight + D.ν

def encode (ξ : Fin n → Bool) : R D.d := interleave (D.a ξ) 0

def lattice : AddSubgroup (Coeff D.d) := principalIdealLattice D.g

/-- Changing only the mask leaves h, t, P, and the ideal generator fixed. -/
def withMask (μ : Fin n → Bool) : ReductionData M n :=
  { D with system := { D.system with μ := μ } }

theorem generator_mask_independent (μ : Fin n → Bool) : (D.withMask μ).g = D.g := by
  have hh : (D.withMask μ).h = D.h := rfl
  have ht : (D.withMask μ).t = D.t := by
    unfold t
    congr 1
    funext z
    cases z <;> rfl
  have hw : (D.withMask μ).W = D.W := rfl
  have hν : (D.withMask μ).ν = D.ν := rfl
  have hs : (D.withMask μ).s = D.s := rfl
  have hp : (D.withMask μ).P = D.P := by
    simp only [P, hs, hw, ht, hν]
    rfl
  simp only [g, hh, hp]
  rfl

theorem P_pos : 0 < D.P := by unfold P; omega

theorem d_power_two : ∃ k : ℕ, D.d = 2 ^ k := by
  refine ⟨Nat.clog 2 (M * D.positions.L) + 1, ?_⟩
  simp [d, N, SidonPositions.N, pow_succ, Nat.mul_comm]

theorem g_ne_zero : D.g ≠ 0 := by
  intro hg
  have hh := congrFun hg (⟨1, by change 1 < 2 * D.N; have hn : 0 < D.N := D.positions.N_pos; omega⟩ : Fin D.d)
  have hval : D.g ⟨1, by change 1 < 2 * D.N; have hn : 0 < D.N := D.positions.N_pos; omega⟩ =
      2 * (D.P : ℤ) := by
    exact interleave_odd _ _ ⟨0, D.positions.N_pos⟩ |>.trans (monomial_self _ _)
  rw [hval] at hh
  have hp : (0 : ℤ) < D.P := by exact_mod_cast D.P_pos
  change 2 * (D.P : ℤ) = 0 at hh
  omega

theorem encode_injective : Function.Injective D.encode := by
  intro ξ η h
  have h' := (interleave_injective h).1
  funext j
  apply bit_injective
  have := congrFun h' (D.alpha j)
  simpa only [a, sparse_at D.alpha_injective] using this

theorem cross_card : Fintype.card D.Cross = D.ν := by
  classical
  simp only [Cross, Fintype.card_sigma]
  have hc (e : D.Entry) : Fintype.card {k : Fin n // k ≠ e.val.2} = n - 1 := by
    simp [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  simp [hc, ν, W, Nat.mul_comm]

/-- The unnumbered distinct-monomials lemma after `lem:boolean-identity`.
This also computes the coefficient ℓ₂ norm of h. -/
theorem h_norm : sqNorm D.h = D.W := by
  rw [h, sqNorm_sparse D.hPosition_injective]
  simp [W]


/-- The support of h consists of exactly W positions, all with coefficient one. -/
theorem h_support_card : (Finset.univ.filter fun r => D.h r ≠ 0).card = D.W := by
  classical
  have he : (Finset.univ.filter fun r => D.h r ≠ 0) =
      Finset.univ.image D.hPosition := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      exists_prop]
    constructor
    · intro hr
      by_contra hn
      have hz : ∀ j : D.Entry, r ≠ D.hPosition j := by
        intro j hj
        exact hn ⟨j, hj.symm⟩
      have hh : D.h r = 0 := by simp [h, sparse_apply, hz]
      exact hr hh
    · rintro ⟨e, rfl⟩
      rw [h, sparse_at D.hPosition_injective]
      norm_num
  rw [he, Finset.card_image_of_injective _ D.hPosition_injective]
  rfl

/-- Regroup an entry-indexed sum by rows of A. -/
theorem entry_sum (F : Fin M → Fin n → ℤ) :
    (∑ e : D.Entry, F e.val.1 e.val.2) =
      ∑ i, ∑ j, bit (D.system.A i j) * F i j := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter
    (fun ij : Fin M × Fin n => D.system.A ij.1 ij.2 = true))
    (by intro z; simp) (fun ij => F ij.1 ij.2)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  cases h : D.system.A i j <;> simp [h]

/-- The polynomial convolution formula preceding equation (ha). -/
theorem ha_expansion (ξ : Fin n → Bool) :
    mul D.h (D.a ξ) = sparse D.coordinate
      (Sum.elim (fun i => ∑ j, bit (D.system.A i j) * bit (ξ j))
        (fun z => bit (ξ z.2.val))) := by
  classical
  have hm (e : D.Entry) (k : Fin n) :
      mul (monomial (D.hPosition e) 1) (monomial (D.alpha k) (bit (ξ k))) =
      monomial ⟨D.positions.crossExp e.val.1 e.val.2 k,
        D.positions.crossExp_lt_N _ _ _⟩ (bit (ξ k)) := by
    exact (mul_monomial_of_lt _ _ _ _ (D.positions.crossExp_lt_N _ _ _)).trans
      (by simp [hPosition, alpha, SidonPositions.crossExp])
  have hd (e : D.Entry) : D.positions.crossExp e.val.1 e.val.2 e.val.2 =
      D.positions.ρ e.val.1 := by
    have hb := D.positions.bound e.val.2
    dsimp [SidonPositions.crossExp, SidonPositions.hExp, SidonPositions.ρ]
    omega
  unfold h a sparse
  rw [mul_sum_left]
  simp_rw [mul_sum_right, hm]
  funext r
  simp only [Finset.sum_apply, Fintype.sum_sum_type, coordinate, Sum.elim_inl, Sum.elim_inr]
  have hs (e : D.Entry) := Fintype.sum_eq_add_sum_subtype_ne
    (fun k : Fin n => monomial
      (⟨D.positions.crossExp e.val.1 e.val.2 k, D.positions.crossExp_lt_N _ _ _⟩ : Fin D.N)
      (bit (ξ k)) r) e.val.2
  simp_rw [hs]
  rw [Finset.sum_add_distrib, Fintype.sum_sigma]
  congr 1
  simp_rw [hd, monomial]
  rw [D.entry_sum (fun i j => if r = (⟨D.positions.ρ i, D.positions.row_lt_N i⟩ : Fin D.N)
    then bit (ξ j) else 0)]
  apply Finset.sum_congr rfl; intro i _
  by_cases hr : r.val = D.positions.ρ i
  · have hr' : r = (⟨D.positions.ρ i, D.positions.row_lt_N i⟩ : Fin D.N) := Fin.ext hr
    simp [hr']
  · have hr' : r ≠ (⟨D.positions.ρ i, D.positions.row_lt_N i⟩ : Fin D.N) := by
      intro h; exact hr (congrArg Fin.val h)
    simp [hr']

/-- Lemma `lem:boolean-identity`. -/
theorem boolean_identity (ξ : Fin n → Bool) :
    sqNorm ((2 : ℤ) • mul D.h (D.a ξ) - D.t) =
      (D.ν : ℤ) + 4 * sqNorm (D.system.residual ξ) := by
  rw [D.ha_expansion]
  unfold t
  rw [← sparse_smul, ← sparse_sub, sqNorm_sparse D.coordinate_injective,
    Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hb (z : D.Cross) : (2 * bit (ξ z.2.val) - 1)^2 = 1 := by
    cases ξ z.2.val <;> simp
  simp_rw [hb]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, D.cross_card]
  rw [add_comm]
  congr 1
  change (∑ i, (2 * (∑ j, bit (D.system.A i j) * bit (ξ j)) -
    2 * bit (D.system.b i)) ^ 2) =
    4 * ∑ i, ((∑ j, bit (D.system.A i j) * bit (ξ j)) - bit (D.system.b i)) ^ 2
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  ring

/-- Multiplication by x in the half-size negacyclic ring. -/
def xmul (b : R D.N) : R D.N := fun r =>
  if r.val = 0 then - b ⟨D.N - 1, by change D.N - 1 < D.N; have hn : 0 < D.N := D.positions.N_pos; omega⟩
  else b ⟨r.val - 1, by omega⟩

/-- Multiplication by g before subtracting the target. -/
theorem generator_product (a b : R D.N) :
    mul D.g (interleave a b) =
      interleave ((2 : ℤ) • mul D.h a + (2 * (D.P : ℤ)) • D.xmul b)
        ((2 : ℤ) • mul D.h b + (2 * (D.P : ℤ)) • a) := by
  unfold g
  rw [interleave_monomial_one D.positions.N_pos, mul_add_left, even_mul, mul_y]
  simp only [mul_smul_left]
  rw [shift_interleave D.positions.N_pos, interleave_smul, interleave_add]
  rfl

/-- Equation (block-product), for arbitrary integral multiplier blocks. -/
theorem block_product (a b : R D.N) :
    mul D.g (interleave a b) - D.T =
      interleave ((2 : ℤ) • mul D.h a + (2 * (D.P : ℤ)) • D.xmul b - D.t)
        ((2 : ℤ) • mul D.h b + (2 * (D.P : ℤ)) • a - (D.P : ℤ) • D.u) := by
  unfold g T
  rw [interleave_monomial_one D.positions.N_pos, mul_add_left, even_mul, mul_y]
  simp only [mul_smul_left]
  rw [shift_interleave D.positions.N_pos, interleave_smul, interleave_add, interleave_sub]
  rfl


theorem sum_bit_mask : (∑ j, bit (D.system.μ j)) = (D.weight : ℤ) := by
  simp [bit, weight, Finset.sum_boole]

theorem mask_square (ξ : Fin n → Bool) (hξ : D.system.Allowed ξ) (j : Fin n) :
    (2 * bit (ξ j) - bit (D.system.μ j))^2 = bit (D.system.μ j) := by
  have h := hξ j
  cases hx : ξ j <;> cases hm : D.system.μ j <;> simp_all

theorem mask_norm (ξ : Fin n → Bool) (hξ : D.system.Allowed ξ) :
    sqNorm ((2 : ℤ) • D.a ξ - D.u) = D.weight := by
  have he : (2 : ℤ) • D.a ξ - D.u =
      sparse D.alpha (fun j => 2 * bit (ξ j) - bit (D.system.μ j)) := by
    rw [sparse_sub, sparse_smul]
    rfl
  rw [he, sqNorm_sparse D.alpha_injective]
  simp_rw [D.mask_square ξ hξ]
  exact D.sum_bit_mask

@[simp] theorem xmul_zero : D.xmul 0 = 0 := by
  funext r; simp [xmul]

/-- The allowed-distance assertion of Lemma `lem:admissible`. -/
theorem admissible_allowed (ξ : Fin n → Bool) (hξ : D.system.Allowed ξ) :
    sqNorm (mul D.g (D.encode ξ) - D.T) =
      D.Δ + 4 * sqNorm (D.system.residual ξ) := by
  unfold encode
  rw [D.block_product]
  simp only [mul_zero, D.xmul_zero, smul_zero, add_zero, zero_add]
  have ho : (2 * (D.P : ℤ)) • D.a ξ - (D.P : ℤ) • D.u =
      (D.P : ℤ) • ((2 : ℤ) • D.a ξ - D.u) := by
    funext r
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [ho, sqNorm_interleave, sqNorm_smul, D.mask_norm ξ hξ, D.boolean_identity]
  unfold Δ
  ring


theorem a_at (ξ : Fin n → Bool) (j : Fin n) : D.a ξ (D.alpha j) = bit (ξ j) :=
  sparse_at D.alpha_injective _ _

theorem a_off (ξ : Fin n → Bool) (r : Fin D.N) (hr : ¬ ∃ j, r = D.alpha j) :
    D.a ξ r = 0 := by
  have hn : ∀ j, r ≠ D.alpha j := by simpa using hr
  simp [a, sparse_apply, hn]

theorem u_bits (r : Fin D.N) : D.u r = 0 ∨ D.u r = 1 := by
  classical
  by_cases hr : ∃ j, r = D.alpha j
  · obtain ⟨j, rfl⟩ := hr
    change D.a D.system.μ (D.alpha j) = 0 ∨ D.a D.system.μ (D.alpha j) = 1
    rw [D.a_at]
    cases D.system.μ j <;> simp
  · exact Or.inl (D.a_off _ r hr)

theorem sum_u : (∑ r, D.u r) = (D.weight : ℤ) := by
  unfold u a
  simp only [sparse_apply]
  rw [Finset.sum_comm]
  simpa using D.sum_bit_mask

/-- Recover the masked Boolean vector from a coordinatewise rounded pair. -/
theorem decode_rounded (a b : R D.N) (hr : Rounded D.u a b) :
    ∃ ξ, D.system.Allowed ξ ∧ a = D.a ξ ∧ b = 0 := by
  classical
  let ξ : Fin n → Bool := fun j => decide (a (D.alpha j) = 1)
  have hu (j : Fin n) : D.u (D.alpha j) = bit (D.system.μ j) := D.a_at _ j
  have hallowed : D.system.Allowed ξ := by
    intro j hj
    have haj : a (D.alpha j) = 1 := by simpa [ξ] using hj
    cases hm : D.system.μ j
    · have hz := (hr.2 (D.alpha j)).1 (by simp [hu, hm])
      omega
    · rfl
  refine ⟨ξ, hallowed, ?_, hr.1⟩
  funext r
  by_cases hrange : ∃ j, r = D.alpha j
  · obtain ⟨j, rfl⟩ := hrange
    rw [D.a_at]
    have hj : a (D.alpha j) = 0 ∨ a (D.alpha j) = 1 := by
      cases hm : D.system.μ j
      · exact Or.inl ((hr.2 (D.alpha j)).1 (by simp [hu, hm]))
      · exact (hr.2 (D.alpha j)).2 (by simp [hu, hm])
    rcases hj with hj | hj <;> simp [ξ, hj]
  · have hu0 : D.u r = 0 := D.a_off _ r hrange
    rw [D.a_off ξ r hrange]
    exact (hr.2 r).1 hu0

/-- Case 2's bound 4Φ≥ω+4, for the actual sparse mask polynomial. -/
theorem discrete_gap (a b : R D.N)
    (hbad : ¬ ∃ ξ, D.system.Allowed ξ ∧ interleave a b = D.encode ξ) :
    (D.weight : ℤ) + 4 ≤ sqNorm ((2 : ℤ) • a - D.u) + 4 * sqNorm b := by
  have hr : ¬ Rounded D.u a b := by
    intro hh
    obtain ⟨ξ, hξ, ha, hb⟩ := D.decode_rounded a b hh
    exact hbad ⟨ξ, hξ, by simp [encode, ha, hb]⟩
  have hg := rounding_gap D.u a b D.u_bits hr
  rw [D.sum_u] at hg
  exact hg

/-- ℓ₂ norm of the target in the half-size ring, used in the size estimate. -/
theorem t_norm : sqNorm D.t =
    4 * ((Finset.univ.filter fun i => D.system.b i = true).card : ℤ) + D.ν := by
  rw [t, sqNorm_sparse D.coordinate_injective, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, one_pow, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, D.cross_card]
  congr 1
  have hb (i : Fin M) : (2 * bit (D.system.b i))^2 = 4 * bit (D.system.b i) := by
    cases D.system.b i <;> norm_num
  simp_rw [hb]
  rw [← Finset.mul_sum]
  simp [bit, Finset.sum_boole]

theorem W_le : D.W ≤ M * n := by
  unfold W Entry
  simpa using Fintype.card_subtype_le (fun ij : Fin M × Fin n => D.system.A ij.1 ij.2 = true)

theorem weight_le : D.weight ≤ n := by
  unfold weight
  simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n))
    (fun j => D.system.μ j = true)


theorem u_norm : sqNorm D.u = D.weight := by
  rw [u, a, sqNorm_sparse D.alpha_injective]
  have hb (j : Fin n) : bit (D.system.μ j)^2 = bit (D.system.μ j) := by
    cases D.system.μ j <;> simp
  simp_rw [hb]
  exact D.sum_bit_mask

theorem s_sq : n + 4 ≤ D.s ^ 2 := by
  exact (ceilSqrt_le_iff _ _).mp le_rfl

theorem W_lt_P : D.W < D.P := by
  have hs : 1 ≤ D.s := by have := D.s_sq; nlinarith
  have hW : D.W ≤ D.s * D.W := by
    have := Nat.mul_le_mul_right D.W hs
    simpa using this
  have hB : D.W ≤ D.s * D.W + ceilSqrt (sqNorm D.t).toNat + ceilSqrt (D.ν + 4) := by omega
  have hm := Nat.mul_le_mul_right
    (D.s * D.W + ceilSqrt (sqNorm D.t).toNat + ceilSqrt (D.ν + 4)) hs
  unfold P
  nlinarith

/-- The exclusion assertion of Lemma `lem:admissible`. -/
theorem admissible_forbidden (q : R D.d)
    (hq : ¬ ∃ ξ, D.system.Allowed ξ ∧ q = D.encode ξ) :
    D.Δ + 4 < sqNorm (mul D.g q - D.T) := by
  obtain ⟨a, b, rfl⟩ := exists_interleave q
  have hd := D.discrete_gap a b hq
  have hnorm := block_norm_lower_bound D.positions.N_pos D.hPosition a b D.u D.t D.P
  change ((D.P : ℝ) - D.W) *
      Real.sqrt ((sqNorm ((2 : ℤ) • a - D.u) + 4 * sqNorm b : ℤ) : ℝ) -
      (D.W : ℝ) * Real.sqrt (sqNorm D.u : ℝ) - Real.sqrt (sqNorm D.t : ℝ) ≤ _ at hnorm
  rw [D.u_norm] at hnorm
  simp only [Int.cast_natCast] at hnorm
  let E := (2 : ℤ) • mul D.h a + (2 * (D.P : ℤ)) • D.xmul b - D.t
  let O := (2 : ℤ) • mul D.h b + (2 * (D.P : ℤ)) • a - (D.P : ℤ) • D.u
  have hnorm' : ((D.P : ℝ) - D.W) * Real.sqrt ((D.weight : ℝ) + 4) -
      (D.W : ℝ) * Real.sqrt (D.weight : ℝ) - Real.sqrt (sqNorm D.t : ℝ) ≤
      ‖realVec (pair E O)‖ := by
    have hg : (D.weight : ℝ) + 4 ≤
        ((sqNorm ((2 : ℤ) • a - D.u) + 4 * sqNorm b : ℤ) : ℝ) := by exact_mod_cast hd
    have hp : (0 : ℝ) ≤ D.P - D.W := by
      have hh : (D.W : ℝ) ≤ (D.P : ℝ) := by exact_mod_cast (Nat.le_of_lt D.W_lt_P)
      linarith
    have hm := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg) hp
    exact le_trans (by linarith) hnorm
  let c := ceilSqrt (sqNorm D.t).toNat
  let e := ceilSqrt (D.ν + 4)
  have hc : Real.sqrt (sqNorm D.t : ℝ) ≤ (c : ℝ) := by
    have hh := Nat.le_ceil (Real.sqrt ((sqNorm D.t).toNat : ℝ))
    rw [← ceilSqrt_eq] at hh
    have hcast : ((sqNorm D.t).toNat : ℝ) = (sqNorm D.t : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (sqNorm_nonneg D.t)]
    simpa only [hcast] using hh
  have he : Real.sqrt ((D.ν : ℝ) + 4) ≤ (e : ℝ) := by
    have hh := Nat.le_ceil (Real.sqrt ((D.ν + 4 : ℕ) : ℝ))
    rw [← ceilSqrt_eq] at hh
    simpa [e] using hh
  have hs : (D.weight : ℝ) + 4 ≤ (D.s : ℝ)^2 := by
    have hh : D.weight + 4 ≤ D.s ^ 2 := le_trans (by have := D.weight_le; omega) D.s_sq
    exact_mod_cast hh
  have hP : (D.P : ℝ) = 1 + (D.s : ℝ) * ((D.s : ℝ) * D.W + c + e) := by
    dsimp [c, e]
    simp only [P, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  have hR : ((D.P : ℝ) - D.W) * Real.sqrt ((D.weight : ℝ) + 4) -
      (D.W : ℝ) * Real.sqrt (D.weight : ℝ) - c ≤ ‖realVec (pair E O)‖ := by linarith
  have hsep := penalty_separation (D.weight : ℝ) (D.ν : ℝ) (D.s : ℝ) (D.W : ℝ)
    c e D.P ‖realVec (pair E O)‖ (by positivity) (by positivity) (by positivity)
    (by positivity) hs (by positivity) he hP hR
  rw [realVec_norm_sq, sqNorm_pair] at hsep
  rw [D.block_product, sqNorm_interleave]
  change D.Δ + 4 < sqNorm E + sqNorm O
  unfold Δ
  exact_mod_cast hsep


end ReductionData
end IdealCVP
