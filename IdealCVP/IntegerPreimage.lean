import IdealCVP.CertificateBound
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Nat.Size
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Integer preimages through independent columns and their Gram matrix -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace IdealCVP

/-- A finite independent subfamily spanning every column, without choosing rank minors. -/
theorem exists_independent_columns {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ) :
    ∃ (r : ℕ) (s : Fin r → Fin n), Function.Injective s ∧ r ≤ n ∧
      LinearIndependent ℝ (fun j : Fin r => fun i : Fin m => (M i (s j) : ℝ)) ∧
      ∀ j : Fin n, ∃ a : Fin r → ℝ,
        (fun i => (M i j : ℝ)) = (fun i => ∑ k, (M i (s k) : ℝ)*a k) := by
  classical
  let cols : Fin n → (Fin m → ℝ) := fun j i => M i j
  obtain ⟨κ,s,hs,hspan,hli⟩ := exists_linearIndependent' ℝ cols
  letI : Finite κ := Finite.of_injective s hs
  letI : Fintype κ := Fintype.ofFinite κ
  let e := Fintype.equivFin κ
  let t : Fin (Fintype.card κ) → Fin n := s ∘ e.symm
  have ht : Function.Injective t := hs.comp e.symm.injective
  refine ⟨Fintype.card κ,t,ht,?_,?_,?_⟩
  · simpa using Fintype.card_le_of_injective s hs
  · exact hli.comp e.symm e.symm.injective
  · intro j
    have hm : cols j ∈ Submodule.span ℝ (Set.range (cols ∘ s)) := by
      rw [hspan]
      exact Submodule.subset_span ⟨j,rfl⟩
    obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hm
    refine ⟨a ∘ e.symm, ?_⟩
    have hh := congrFun ha
    ext i
    change (cols j) i = ∑ k : Fin (Fintype.card κ), (cols (s (e.symm k))) i * a (e.symm k)
    rw [e.symm.sum_comp (fun k => (cols (s k)) i * a k)]
    simpa [smul_eq_mul, Finset.sum_apply, mul_comm] using (hh i).symm

/-- Independent real columns have a nonsingular integral Gram matrix. -/
theorem gram_det_ne_zero {m r : ℕ} (C : Matrix (Fin m) (Fin r) ℤ)
    (hC : LinearIndependent ℝ (fun j : Fin r => fun i : Fin m => (C i j : ℝ))) :
    (C.transpose * C).det ≠ 0 := by
  let R : Matrix (Fin m) (Fin r) ℝ := C.map (Int.castRingHom ℝ)
  have hinj : Function.Injective R.mulVec := Matrix.mulVec_injective_iff.mpr hC
  have hp := Matrix.PosDef.conjTranspose_mul_self R hinj
  have hd := hp.det_pos.ne'
  intro hz
  apply hd
  have he : (C.transpose * C).map (Int.castRingHom ℝ) = R.conjTranspose * R := by
    rw [Matrix.map_mul (f := Int.castRingHom ℝ), Matrix.transpose_map]
    simp only [R, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [← he, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hz, map_zero]

/-- The Gram adjugate acts as a determinant-scaled projector on the column space. -/
theorem gram_adjugate_projector {m r : ℕ} (C : Matrix (Fin m) (Fin r) ℤ)
    (w : Fin m → ℤ)
    (hw : ∃ a : Fin r → ℝ,
      (fun i => (w i : ℝ)) = (C.map (Int.castRingHom ℝ)).mulVec a) :
    C.mulVec ((C.transpose*C).adjugate.mulVec (C.transpose.mulVec w)) =
      (C.transpose*C).det • w := by
  classical
  obtain ⟨a,ha⟩ := hw
  let R : Matrix (Fin m) (Fin r) ℝ := C.map (Int.castRingHom ℝ)
  have he : (C.transpose*C).map (Int.castRingHom ℝ) = R.transpose*R := by
    rw [Matrix.map_mul (f := Int.castRingHom ℝ), Matrix.transpose_map]
  have hh : R.mulVec ((R.transpose*R).adjugate.mulVec (R.transpose.mulVec (R.mulVec a))) =
      (R.transpose*R).det • R.mulVec a := by
    rw [Matrix.mulVec_mulVec a R.transpose R,
      Matrix.mulVec_mulVec a (R.transpose*R).adjugate (R.transpose*R),
      Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul]
  rw [← ha] at hh
  ext i
  apply Int.cast_injective (α := ℝ)
  have ht := congrFun hh i
  change (Int.castRingHom ℝ) (C.mulVec ((C.transpose*C).adjugate.mulVec
    (C.transpose.mulVec w)) i) = (Int.castRingHom ℝ) ((C.transpose*C).det * w i)
  simp only [RingHom.map_mulVec, map_mul]
  have hA : ((C.transpose*C).adjugate).map (Int.castRingHom ℝ) =
      ((C.transpose*C).map (Int.castRingHom ℝ)).adjugate := by
    simpa only [RingHom.mapMatrix_apply] using (Int.castRingHom ℝ).map_adjugate (C.transpose*C)
  have hD : (Int.castRingHom ℝ) (C.transpose*C).det =
      ((C.transpose*C).map (Int.castRingHom ℝ)).det := by
    simpa only [RingHom.mapMatrix_apply] using (Int.castRingHom ℝ).map_det (C.transpose*C)
  simp only [Function.comp_def, RingHom.map_mulVec, hA, hD, he, Matrix.transpose_map]
  exact ht

/-- Embed the chosen column coordinates, filling every other coordinate with zero. -/
def columnEmbedding {n r : ℕ} (s : Fin r → Fin n) : Matrix (Fin n) (Fin r) ℤ :=
  fun j k => if j = s k then 1 else 0

theorem mul_columnEmbedding {m n r : ℕ} (M : Matrix (Fin m) (Fin n) ℤ)
    (s : Fin r → Fin n) : M * columnEmbedding s = fun i k => M i (s k) := by
  classical
  ext i k
  simp [Matrix.mul_apply, columnEmbedding, mul_ite]

theorem columnEmbedding_mulVec_of_not_mem {n r : ℕ} (s : Fin r → Fin n)
    (j : Fin n) (hj : j ∉ Set.range s) (a : Fin r → ℤ) :
    (columnEmbedding s).mulVec a j = 0 := by
  classical
  have hs : ∀ k, j ≠ s k := fun k h => hj ⟨k,h.symm⟩
  simp [Matrix.mulVec, dotProduct, columnEmbedding, hs]

theorem columnEmbedding_mulVec_apply {n r : ℕ} (s : Fin r → Fin n)
    (hs : Function.Injective s) (a : Fin r → ℤ) (k : Fin r) :
    (columnEmbedding s).mulVec a (s k) = a k := by
  classical
  simp [Matrix.mulVec, dotProduct, columnEmbedding, hs.eq_iff]

/-- Modulo the Gram determinant, every nonpivot coefficient can be made small
by subtracting explicit integer kernel vectors. This includes rank zero. -/
theorem exists_preimage_reduced {m n r : ℕ} (M : Matrix (Fin m) (Fin n) ℤ)
    (s : Fin r → Fin n)
    (hspan : ∀ j : Fin n, ∃ a : Fin r → ℝ,
      (fun i => (M i j : ℝ)) = (fun i => ∑ k, (M i (s k) : ℝ)*a k))
    (hdet : ((M * columnEmbedding s).transpose * (M * columnEmbedding s)).det ≠ 0)
    (q : Fin n → ℤ) :
    ∃ q' : Fin n → ℤ, M.mulVec q' = M.mulVec q ∧
      ∀ j ∉ Set.range s,
        |q' j| ≤ |((M * columnEmbedding s).transpose * (M * columnEmbedding s)).det| := by
  classical
  let C := M * columnEmbedding s
  let A := C.transpose*C
  let D := A.det
  let k : Fin n → (Fin n → ℤ) := fun j =>
    Pi.single j D - (columnEmbedding s).mulVec (A.adjugate.mulVec
      (C.transpose.mulVec (fun i => M i j)))
  have hk (j : Fin n) : M.mulVec (k j) = 0 := by
    have hp := gram_adjugate_projector C (fun i => M i j) (by
      obtain ⟨a,ha⟩ := hspan j
      refine ⟨a,?_⟩
      rw [show C = (fun i k => M i (s k)) from mul_columnEmbedding M s]
      ext i
      change (M i j : ℝ) = ∑ k, (M i (s k) : ℝ)*a k
      exact congrFun ha i)
    dsimp only [k]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, show M * columnEmbedding s = C from rfl, hp]
    ext i
    simp [Matrix.mulVec_single, D, A, Pi.smul_apply, smul_eq_mul, mul_comm]
  let t : Fin n → ℤ := fun j => if j ∈ Set.range s then 0 else q j / D
  let q' := q - ∑ j, t j • k j
  refine ⟨q', ?_, ?_⟩
  · change M.mulVec (q - ∑ j, t j • k j) = _
    rw [Matrix.mulVec_sub, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hk, smul_zero, Finset.sum_const_zero, sub_zero]
  · intro j hj
    have hkj (i : Fin n) : k i j = if j = i then D else 0 := by
      dsimp only [k, Pi.sub_apply]
      rw [columnEmbedding_mulVec_of_not_mem s j hj, sub_zero]
      simp [Pi.single_apply]
    have he : q' j = q j % D := by
      change q j - (∑ i, t i • k i) j = q j % D
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      simp_rw [hkj, mul_ite, MulZeroClass.mul_zero]
      simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, t, if_neg hj]
      have hh := Int.emod_add_mul_ediv (q j) D
      nlinarith only [hh]
    rw [he, abs_of_nonneg (Int.emod_nonneg _ hdet)]
    exact (Int.emod_lt_abs _ hdet).le

/-- A uniform elementary bound on integer matrix multiplication. -/
theorem mulVec_abs_bound {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ)
    (x : Fin n → ℤ) (A B : ℤ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hM : ∀ i j, |M i j| ≤ A) (hx : ∀ j, |x j| ≤ B) (i : Fin m) :
    |M.mulVec x i| ≤ (n : ℤ)*A*B := by
  calc
    _ ≤ ∑ j : Fin n, |M i j*x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, A*B := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hM i j) (hx j) (abs_nonneg _) hA
    _ = _ := by simp; ring

/-- A nonsingular selected Gram system bounds the pivot coordinates of any
solution whose other coordinates have already been reduced. -/
theorem preimage_pivot_equation {m n r : ℕ} (M : Matrix (Fin m) (Fin n) ℤ)
    (s : Fin r → Fin n) (hs : Function.Injective s) (q : Fin n → ℤ) :
    let C := M * columnEmbedding s
    let qN : Fin n → ℤ := fun j => if j ∈ Set.range s then 0 else q j
    (C.transpose*C).mulVec (q ∘ s) = C.transpose.mulVec (M.mulVec q - M.mulVec qN) := by
  classical
  dsimp only
  let qN : Fin n → ℤ := fun j => if j ∈ Set.range s then 0 else q j
  have he : q = (columnEmbedding s).mulVec (q ∘ s) + qN := by
    ext j
    by_cases hj : j ∈ Set.range s
    · obtain ⟨k,rfl⟩ := hj
      simp only [Pi.add_apply, columnEmbedding_mulVec_apply s hs, Function.comp_apply,
        qN, if_pos (Set.mem_range_self k), add_zero]
    · rw [Pi.add_apply, columnEmbedding_mulVec_of_not_mem s j hj]
      simp only [qN,if_neg hj,zero_add]
  have hh : M.mulVec q - M.mulVec qN = (M*columnEmbedding s).mulVec (q ∘ s) := by
    conv_lhs => lhs; rw [he]
    rw [Matrix.mulVec_add, add_sub_cancel_right, Matrix.mulVec_mulVec]
  rw [hh, Matrix.mulVec_mulVec]

/-- A uniform polynomial-bit magnitude bound for every solvable integer system.
The exponent is quadratic in the number of columns, including rank-deficient systems. -/
theorem exists_small_integer_preimage {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ)
    (v : Fin m → ℤ) (T : ℤ) (hT : 2 ≤ T) (hm : (m : ℤ) ≤ T) (hn : (n : ℤ) ≤ T)
    (hM : ∀ i j, |M i j| ≤ T) (hv : ∀ i, |v i| ≤ T)
    (hsol : ∃ q : Fin n → ℤ, M.mulVec q = v) :
    ∃ q : Fin n → ℤ, M.mulVec q = v ∧ ∀ j, |q j| ≤ T^(16*(n+1)^2) := by
  classical
  obtain ⟨q,hq⟩ := hsol
  obtain ⟨r,s,hs,hr,hli,hspan⟩ := exists_independent_columns M
  let C := M * columnEmbedding s
  let A := C.transpose*C
  have hdet : A.det ≠ 0 := gram_det_ne_zero C (by simpa only [C, mul_columnEmbedding] using hli)
  obtain ⟨q',heq,hred⟩ := exists_preimage_reduced M s hspan hdet q
  have hq' : M.mulVec q' = v := heq.trans hq
  let D₀ : ℤ := T^(4*(n+1))
  have hT₀ : 0 ≤ T := by omega
  have hT₁ : 1 ≤ T := by omega
  have hD₀ : 1 ≤ D₀ := one_le_pow₀ hT₁
  have hrn : (r : ℤ) ≤ (n : ℤ) := by exact_mod_cast hr
  have hrT : (r : ℤ) ≤ T := hrn.trans hn
  have hC (i : Fin m) (j : Fin r) : |C i j| ≤ T := by
    simpa only [C, mul_columnEmbedding] using hM i (s j)
  have hAe (i j : Fin r) : |A i j| ≤ T^3 := by
    have hh := mulVec_abs_bound C.transpose (fun k => C k j) T T hT₀ hT₀
      (fun i j => hC j i) (fun k => hC k j) i
    change |A i j| ≤ _ at hh
    apply hh.trans
    calc
      (m : ℤ)*T*T = (m : ℤ)*T^2 := by ring
      _ ≤ T*T^2 := mul_le_mul_of_nonneg_right hm (sq_nonneg T)
      _ = T^3 := by ring
  have hfac : (r.factorial : ℤ) ≤ T^r := by
    calc
      _ ≤ (r : ℤ)^r := by exact_mod_cast Nat.factorial_le_pow r
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hrT r
  have hD : |A.det| ≤ D₀ := by
    have hh := Matrix.det_le (abv := AbsoluteValue.abs) hAe
    have hh' : |A.det| ≤ (r.factorial : ℤ)*(T^3)^r := by
      simpa only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] using hh
    calc
      _ ≤ T^r*(T^3)^r := hh'.trans (mul_le_mul_of_nonneg_right hfac (by positivity))
      _ = (T^4)^r := by rw [← mul_pow]; congr 1; ring
      _ = T^(4*r) := (pow_mul _ _ _).symm
      _ ≤ D₀ := pow_le_pow_right₀ hT₁ (by omega)
  let qN : Fin n → ℤ := fun j => if j ∈ Set.range s then 0 else q' j
  have hN (j : Fin n) : |qN j| ≤ D₀ := by
    by_cases hj : j ∈ Set.range s
    · simp only [qN,if_pos hj,abs_zero]; omega
    · have hh : |q' j| ≤ |A.det| := hred j hj
      simpa only [qN,if_neg hj] using hh.trans hD
  let w := v - M.mulVec qN
  have hw (i : Fin m) : |w i| ≤ T^3*D₀ := by
    have hh := mulVec_abs_bound M qN T D₀ hT₀ (by omega) hM hN i
    have hh' := abs_sub (v i) (M.mulVec qN i)
    change |w i| ≤ _ at hh'
    have hh'' : (n : ℤ)*T*D₀ ≤ T^2*D₀ := by
      calc
        _ ≤ T*T*D₀ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hn hT₀) (by omega)
        _ = _ := by ring
    have hc : T+T^2*D₀ ≤ T^3*D₀ := by
      have hsq : T ≤ T^2 := by nlinarith
      have hd : T^2 ≤ T^2*D₀ := by nlinarith
      have ht : 2*T^2*D₀ ≤ T^3*D₀ := by nlinarith [mul_nonneg (by nlinarith : 0 ≤ T-2) (by positivity : 0 ≤ T^2*D₀)]
      linarith
    exact hh'.trans ((add_le_add (hv i) hh).trans (by linarith))
  let t := C.transpose.mulVec w
  have ht (i : Fin r) : |t i| ≤ T^5*D₀ := by
    exact (mulVec_abs_bound C.transpose w T (T^3*D₀) hT₀ (by positivity)
      (fun i j => hC j i) hw i).trans (by
        calc
          _ ≤ T*T*(T^3*D₀) := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hm hT₀) (by positivity)
          _ = _ := by ring)
  have hbmag : basisMagnitude A ≤ T^5 := by
    calc
      _ ≤ ∑ _i : Fin r, ∑ _j : Fin r, T^3 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hAe i j
      _ = (r : ℤ)^2*T^3 := by simp; ring
      _ ≤ T^5 := by
        calc
          _ ≤ T^2*T^3 := mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) hrT 2) (by positivity)
          _ = _ := by ring
  have htmag : targetMagnitude t ≤ T^6*D₀ := by
    calc
      _ ≤ ∑ _i : Fin r, T^5*D₀ := Finset.sum_le_sum fun i _ => ht i
      _ = (r : ℤ)*T^5*D₀ := by simp; ring
      _ ≤ T^6*D₀ := by
        calc
          _ ≤ T*T^5*D₀ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hrT (by positivity)) (by omega)
          _ = _ := by ring
  have hbase : 1 + basisMagnitude A + targetMagnitude t + |(0 : ℤ)| ≤ T^8*D₀ := by
    have h51 : T^5 ≤ T^6 := pow_le_pow_right₀ hT₁ (by omega)
    have h61 : 1 ≤ T^6 := one_le_pow₀ hT₁
    have h61D : T^6 ≤ T^6*D₀ := by nlinarith
    have h68 : 3*T^6*D₀ ≤ T^8*D₀ := by
      have h3 : 3 ≤ T^2 := by nlinarith
      nlinarith [mul_nonneg (by linarith : 0 ≤ T^2-3) (by positivity : 0 ≤ T^6*D₀)]
    simp only [abs_zero]
    linarith
  have hbound : certificateBound A t 0 ≤ T^(16*(n+1)^2) := by
    have hbase₀ : 0 ≤ 1+basisMagnitude A+targetMagnitude t+|(0:ℤ)| := by
      have hb0 := basisMagnitude_nonneg A
      have ht0 := targetMagnitude_nonneg t
      simp only [abs_zero]
      omega
    calc
      _ ≤ T^r*(T^8*D₀)^r :=
        mul_le_mul hfac (pow_le_pow_left₀ hbase₀ hbase r) (by positivity) (by positivity)
      _ = T^((4*(n+1)+9)*r) := by
        dsimp [D₀]
        rw [← mul_pow, ← pow_add, ← pow_succ', ← pow_mul]
        congr 1
        ring
      _ ≤ _ := pow_le_pow_right₀ hT₁ (by nlinarith)
  refine ⟨q',hq',?_⟩
  intro j
  by_cases hj : j ∈ Set.range s
  · obtain ⟨k,rfl⟩ := hj
    have hp : A.mulVec (q' ∘ s) = t := by
      dsimp [A,t,w,qN,C]
      rw [← hq']
      exact preimage_pivot_equation M s hs q'
    have hc := certificate_coeff_le A hdet t 0 (q' ∘ s)
      (by rw [hp,sub_self]; simp [sqNorm]) k
    exact hc.trans hbound
  · exact ((hred j hj).trans hD).trans (pow_le_pow_right₀ hT₁ (by nlinarith))

/-- Sum of absolute entries for an arbitrary rectangular matrix. -/
def matrixMagnitude {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ) : ℤ :=
  ∑ i, ∑ j, |M i j|

def integerPreimageScale {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ)
    (v : Fin m → ℤ) : ℤ := 2 + m + n + matrixMagnitude M + targetMagnitude v

def integerPreimageBound {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ)
    (v : Fin m → ℤ) : ℤ := integerPreimageScale M v ^ (16*(n+1)^2)

/-- An explicit bound depending only on the matrix and right hand side. -/
theorem exists_bounded_integer_preimage {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ)
    (v : Fin m → ℤ) (hsol : ∃ q : Fin n → ℤ, M.mulVec q = v) :
    ∃ q : Fin n → ℤ, M.mulVec q = v ∧ ∀ j, |q j| ≤ integerPreimageBound M v := by
  have hM₀ : 0 ≤ matrixMagnitude M :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hv₀ := targetMagnitude_nonneg v
  have hT : 2 ≤ integerPreimageScale M v := by unfold integerPreimageScale; omega
  apply exists_small_integer_preimage M v _ hT
  · unfold integerPreimageScale; omega
  · unfold integerPreimageScale; omega
  · intro i j
    have he : |M i j| ≤ matrixMagnitude M := by
      calc
        _ ≤ ∑ j, |M i j| := Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
        _ ≤ matrixMagnitude M := by
          unfold matrixMagnitude
          exact Finset.single_le_sum (f := fun k : Fin m => ∑ j, |M k j|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    unfold integerPreimageScale
    omega
  · intro i
    have he := target_entry_le v i
    unfold integerPreimageScale
    omega
  · exact hsol

/-- Polynomial bit bound when dimensions and entries fit under `2^L`.
Only the existence of an integer solution is assumed, with no rank promise. -/
theorem exists_integer_preimage_bits {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ)
    (v : Fin m → ℤ) (L : ℕ) (hL : 1 ≤ L)
    (hm : (m : ℤ) ≤ 2^L) (hn : (n : ℤ) ≤ 2^L)
    (hM : ∀ i j, |M i j| ≤ 2^L) (hv : ∀ i, |v i| ≤ 2^L)
    (hsol : ∃ q : Fin n → ℤ, M.mulVec q = v) :
    ∃ q : Fin n → ℤ, M.mulVec q = v ∧
      ∀ j, (q j).natAbs.size ≤ L*(16*(n+1)^2)+1 := by
  obtain ⟨q,hq,hb⟩ := exists_small_integer_preimage M v (2^L)
    (by simpa using pow_le_pow_right₀ (show (1 : ℤ) ≤ 2 by omega) hL) hm hn hM hv hsol
  refine ⟨q,hq,?_⟩
  intro j
  have hh := hb j
  rw [← pow_mul, ← Int.natCast_natAbs] at hh
  have hnat : (q j).natAbs ≤ 2^(L*(16*(n+1)^2)) := by exact_mod_cast hh
  apply Nat.size_le.mpr
  exact hnat.trans_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega))

end IdealCVP
