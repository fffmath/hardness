import IdealCVP.Cyclotomic

/-! # Coefficient norm bounds for negacyclic convolution -/
namespace IdealCVP.Cyclotomic
open IdealCVP

/-- A monomial acts by a signed permutation of the coefficient coordinates. -/
theorem sqNorm_monomial_mul {d : ℕ} (e : Fin d) (a : R d) :
    sqNorm (mul (monomial e 1) a) = sqNorm a := by
  have hd : 0 < d := by have := e.isLt; omega
  letI : NeZero d := ⟨by omega⟩
  have hinj : Function.Injective (fun j : Fin d => e + j) := by
    intro i j h
    exact add_left_cancel h
  have heq : mul (monomial e 1) a = sparse (fun j : Fin d => e + j)
      (fun j => (if e.val + j.val < d then 1 else -1) * a j) := by
    funext r
    rw [mul_monomial_left, sparse_apply]
    apply Finset.sum_congr rfl; intro j _
    have hc : (e.val + j.val) % d = r.val ↔ r = e + j := by
      simp only [Fin.ext_iff, Fin.val_add]
      omega
    simp only [hc, mul_one]
  rw [heq, sqNorm_sparse hinj]
  unfold sqNorm
  apply Finset.sum_congr rfl; intro j _
  split_ifs <;> ring

/-- Young's inequality for a sum of W unit monomials, squared and integral.
Injectivity of the positions is not needed for this upper bound. -/
theorem sparse_mul_bound {ι : Type*} [Fintype ι] {d : ℕ}
    (e : ι → Fin d) (a : R d) :
    sqNorm (mul (sparse e (fun _ => 1)) a) ≤ (Fintype.card ι : ℤ)^2 * sqNorm a := by
  classical
  rw [sparse, mul_sum_left]
  calc
    sqNorm (∑ j, mul (monomial (e j) 1) a) ≤
        ∑ r : Fin d, (Fintype.card ι : ℤ) *
          ∑ j, (mul (monomial (e j) 1) a r)^2 := by
      apply Finset.sum_le_sum
      intro r _
      simp only [Finset.sum_apply]
      simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun j => mul (monomial (e j) 1) a r))
    _ = (Fintype.card ι : ℤ)^2 * sqNorm a := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      change (Fintype.card ι : ℤ) * (∑ j : ι, sqNorm (mul (monomial (e j) 1) a)) = _
      simp only [sqNorm_monomial_mul, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring

/-- The real Euclidean embedding used only for analytic bounds. -/
noncomputable def realVec {ι : Type*} [Fintype ι] (a : ι → ℤ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => (a i : ℝ))

theorem realVec_norm_sq {ι : Type*} [Fintype ι] (a : ι → ℤ) :
    ‖realVec a‖^2 = (sqNorm a : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [realVec, sqNorm]

@[simp] theorem realVec_add {ι : Type*} [Fintype ι] (a b : ι → ℤ) :
    realVec (a + b) = realVec a + realVec b := by
  ext i; simp [realVec]

@[simp] theorem realVec_sub {ι : Type*} [Fintype ι] (a b : ι → ℤ) :
    realVec (a - b) = realVec a - realVec b := by
  ext i; simp [realVec]

@[simp] theorem realVec_smul {ι : Type*} [Fintype ι] (k : ℤ) (a : ι → ℤ) :
    realVec (k • a) = (k : ℝ) • realVec a := by
  ext i; simp [realVec]

@[simp] theorem realVec_zero {ι : Type*} [Fintype ι] : realVec (0 : ι → ℤ) = 0 := by
  ext i; simp [realVec]

theorem realVec_norm {ι : Type*} [Fintype ι] (a : ι → ℤ) :
    ‖realVec a‖ = Real.sqrt (sqNorm a : ℝ) := by
  rw [← realVec_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Coefficient pairing for norm estimates. -/
def pair {ι κ : Type*} (a : ι → ℤ) (b : κ → ℤ) : (ι ⊕ κ) → ℤ := Sum.elim a b

theorem sqNorm_pair {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → ℤ) (b : κ → ℤ) :
    sqNorm (pair a b) = sqNorm a + sqNorm b := by
  exact Fintype.sum_sum_type _

theorem sqNorm_shift {N : ℕ} (hN : 0 < N) (a : R N) : sqNorm (shift hN a) = sqNorm a := by
  let prev : Fin N → Fin N := fun r =>
    if r.val = 0 then ⟨N - 1, by omega⟩ else ⟨r.val - 1, by omega⟩
  have hinj : Function.Injective prev := by
    intro r s h
    have hv := congrArg Fin.val h
    dsimp [prev] at hv
    split_ifs at hv <;> apply Fin.ext <;> dsimp at hv ⊢ <;> omega
  have hb : Function.Bijective prev := ⟨hinj, Finite.surjective_of_injective hinj⟩
  calc
    sqNorm (shift hN a) = ∑ r, (a (prev r))^2 := by
      apply Finset.sum_congr rfl; intro r _
      dsimp [shift, prev]
      split_ifs <;> ring
    _ = sqNorm a := hb.sum_comp (fun r => a r ^ 2)

/-- Young's bound applied simultaneously to the two multiplier blocks. -/
theorem norm_pair_mul_bound {ι : Type*} [Fintype ι] {d : ℕ}
    (e : ι → Fin d) (a b : R d) :
    ‖realVec (pair (mul (sparse e (fun _ => 1)) a) (mul (sparse e (fun _ => 1)) b))‖ ≤
      (Fintype.card ι : ℝ) * ‖realVec (pair a b)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [realVec_norm_sq, mul_pow, realVec_norm_sq]
  have ha := sparse_mul_bound e a
  have hb := sparse_mul_bound e b
  have hs : sqNorm (pair (mul (sparse e (fun _ => 1)) a)
      (mul (sparse e (fun _ => 1)) b)) ≤
      (Fintype.card ι : ℤ)^2 * sqNorm (pair a b) := by
    rw [sqNorm_pair, sqNorm_pair]
    nlinarith
  exact_mod_cast hs

/-- The reverse triangle estimate in Case 2, independent of coordinates. -/
theorem perturbation_lower_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P W : ℝ) (X C C' H U T F : E) (hP : 0 ≤ P) (hW : 0 ≤ W)
    (hX : (2 : ℝ) • X = C' + U)
    (hF : P • C = F - (2 : ℝ) • H + T)
    (hC : ‖C'‖ = ‖C‖) (hH : ‖H‖ ≤ W * ‖X‖) :
    (P - W) * ‖C‖ - W * ‖U‖ - ‖T‖ ≤ ‖F‖ := by
  have hx := norm_add_le C' U
  rw [← hX, norm_smul] at hx
  norm_num at hx
  rw [hC] at hx
  have hf := norm_add_le (F - (2 : ℝ) • H) T
  rw [← hF, norm_smul, Real.norm_eq_abs, abs_of_nonneg hP] at hf
  have ht := norm_sub_le F ((2 : ℝ) • H)
  rw [norm_smul] at ht
  norm_num at ht
  have hw := mul_le_mul_of_nonneg_left hx hW
  nlinarith

/-- Reverse triangle estimate for the two negacyclic product blocks. -/
theorem block_norm_lower_bound {ι : Type*} [Fintype ι] {N : ℕ}
    (hN : 0 < N) (e : ι → Fin N) (a b u t : R N) (P : ℕ) :
    ((P : ℝ) - Fintype.card ι) *
        Real.sqrt ((sqNorm ((2 : ℤ) • a - u) + 4 * sqNorm b : ℤ) : ℝ) -
      (Fintype.card ι : ℝ) * Real.sqrt (sqNorm u : ℝ) - Real.sqrt (sqNorm t : ℝ) ≤
      ‖realVec (pair ((2 : ℤ) • mul (sparse e (fun _ => 1)) a +
          (2 * (P : ℤ)) • shift hN b - t)
        ((2 : ℤ) • mul (sparse e (fun _ => 1)) b +
          (2 * (P : ℤ)) • a - (P : ℤ) • u))‖ := by
  let h := sparse e (fun _ => 1)
  let X := realVec (pair a b)
  let C := realVec (pair ((2 : ℤ) • shift hN b) ((2 : ℤ) • a - u))
  let C' := realVec (pair ((2 : ℤ) • a - u) ((2 : ℤ) • b))
  let H := realVec (pair (mul h a) (mul h b))
  let U := realVec (pair u (0 : R N))
  let TT := realVec (pair t (0 : R N))
  let F := realVec (pair ((2 : ℤ) • mul h a + (2 * (P : ℤ)) • shift hN b - t)
    ((2 : ℤ) • mul h b + (2 * (P : ℤ)) • a - (P : ℤ) • u))
  have hX : (2 : ℝ) • X = C' + U := by
    ext r; cases r <;> simp [X, C', U, realVec, pair] <;> ring
  have hF : (P : ℝ) • C = F - (2 : ℝ) • H + TT := by
    ext r; cases r <;> simp [C, F, H, TT, realVec, pair] <;> ring
  have hC : ‖C'‖ = ‖C‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [C', C, realVec_norm_sq, sqNorm_pair, sqNorm_smul, sqNorm_shift]
    push_cast
    ring
  have hH : ‖H‖ ≤ (Fintype.card ι : ℝ) * ‖X‖ := norm_pair_mul_bound e a b
  have hm := perturbation_lower_bound (P : ℝ) (Fintype.card ι : ℝ)
    X C C' H U TT F (by positivity) (by positivity) hX hF hC hH
  have hc : ‖C‖ = Real.sqrt
      ((sqNorm ((2 : ℤ) • a - u) + 4 * sqNorm b : ℤ) : ℝ) := by
    dsimp only [C]
    rw [realVec_norm, sqNorm_pair, sqNorm_smul, sqNorm_shift]
    congr 1
    norm_num
    ring
  have hu : ‖U‖ = Real.sqrt (sqNorm u : ℝ) := by
    dsimp only [U]
    rw [realVec_norm, sqNorm_pair, sqNorm_zero, add_zero]
  have ht : ‖TT‖ = Real.sqrt (sqNorm t : ℝ) := by
    dsimp only [TT]
    rw [realVec_norm, sqNorm_pair, sqNorm_zero, add_zero]
  rw [hc, hu, ht] at hm
  exact hm

end IdealCVP.Cyclotomic
