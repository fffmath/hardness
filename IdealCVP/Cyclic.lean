import IdealCVP.GeneralFullRank
import IdealCVP.FullRank

/-! # The principal cyclic lift

The ambient ring is the genuine ℤ[X]/(X^(2d)-1). Contiguous coefficient
blocks give the integral plus/minus decomposition used in `lem:principal-crt`.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace IdealCVP.Cyclic
open IdealCVP.Cyclotomic Polynomial

def cyclicModulus (d : ℕ) : Polynomial ℤ := X ^ (2 * d) - 1

abbrev S (d : ℕ) := AdjoinRoot (cyclicModulus d)

theorem cyclicModulus_monic {d : ℕ} (hd : 0 < d) : (cyclicModulus d).Monic := by
  simpa [cyclicModulus] using
    Polynomial.monic_X_pow_sub_C (1 : ℤ) (by omega : 2 * d ≠ 0)

theorem cyclicModulus_natDegree (d : ℕ) : (cyclicModulus d).natDegree = 2 * d := by
  simpa [cyclicModulus] using
    (Polynomial.natDegree_X_pow_sub_C (n := 2 * d) (r := (1 : ℤ)))

def x (d : ℕ) : S d := AdjoinRoot.root _

def poly {d : ℕ} (f : R d) : Polynomial ℤ := ∑ i : Fin d, C (f i) * X ^ i.val

def toRing {d : ℕ} (f : R (2 * d)) : S d := AdjoinRoot.mk _ (poly f)

def copy {d : ℕ} (f : R d) : S d := AdjoinRoot.mk _ (poly f)

@[simp] theorem poly_add {d : ℕ} (f g : R d) : poly (f + g) = poly f + poly g := by
  simp [poly, add_mul, Finset.sum_add_distrib]

@[simp] theorem poly_neg {d : ℕ} (f : R d) : poly (-f) = -poly f := by
  simp [poly, Finset.sum_neg_distrib]

@[simp] theorem poly_smul {d : ℕ} (k : ℤ) (f : R d) : poly (k • f) = k • poly f := by
  simp [poly, Polynomial.smul_eq_C_mul, map_mul, Finset.mul_sum, mul_assoc]

@[simp] theorem copy_add {d : ℕ} (f g : R d) : copy (f + g) = copy f + copy g := by
  simp [copy]

@[simp] theorem copy_neg {d : ℕ} (f : R d) : copy (-f) = -copy f := by simp [copy]

@[simp] theorem copy_sub {d : ℕ} (f g : R d) : copy (f - g) = copy f - copy g := by
  simp [sub_eq_add_neg]

@[simp] theorem copy_smul {d : ℕ} (k : ℤ) (f : R d) : copy (k • f) = k • copy f := by
  unfold copy
  rw [poly_smul, map_zsmul]

@[simp] theorem copy_zero (d : ℕ) : copy (0 : R d) = 0 := by simp [copy, poly]

/-- Standard contiguous lower and upper coefficient blocks. -/
def blockEquiv (d : ℕ) : Fin d ⊕ Fin d ≃ Fin (2 * d) :=
  finSumFinEquiv.trans (finCongr (by omega : d + d = 2 * d))

def concat {d : ℕ} (a b : R d) : R (2 * d) := fun i => (blockEquiv d).symm i |>.elim a b

@[simp] theorem concat_left {d : ℕ} (a b : R d) (i : Fin d) :
    concat a b (blockEquiv d (.inl i)) = a i := by simp [concat]

@[simp] theorem concat_right {d : ℕ} (a b : R d) (i : Fin d) :
    concat a b (blockEquiv d (.inr i)) = b i := by simp [concat]

theorem concat_injective {d : ℕ} {a b c e : R d} (h : concat a b = concat c e) :
    a = c ∧ b = e := by
  constructor
  · funext i
    simpa using congrFun h (blockEquiv d (.inl i))
  · funext i
    simpa using congrFun h (blockEquiv d (.inr i))

theorem exists_concat {d : ℕ} (v : R (2 * d)) : ∃ a b, v = concat a b := by
  refine ⟨(fun i => v (blockEquiv d (.inl i))),
    (fun i => v (blockEquiv d (.inr i))), ?_⟩
  funext i
  obtain ⟨j, rfl⟩ := (blockEquiv d).surjective i
  cases j <;> simp

@[simp] theorem concat_add {d : ℕ} (a b c e : R d) :
    concat a b + concat c e = concat (a + c) (b + e) := by
  funext i
  obtain ⟨j, rfl⟩ := (blockEquiv d).surjective i
  cases j <;> simp

@[simp] theorem concat_sub {d : ℕ} (a b c e : R d) :
    concat a b - concat c e = concat (a - c) (b - e) := by
  funext i
  obtain ⟨j, rfl⟩ := (blockEquiv d).surjective i
  cases j <;> simp

theorem sqNorm_concat {d : ℕ} (a b : R d) :
    sqNorm (concat a b) = sqNorm a + sqNorm b := by
  rw [sqNorm, ← (blockEquiv d).sum_comp, Fintype.sum_sum_type]
  simp [sqNorm]

theorem toRing_sum {d : ℕ} (f : R (2 * d)) :
    toRing f = ∑ i : Fin (2 * d), f i • x d ^ i.val := by
  simp [toRing, poly, x, ← AdjoinRoot.mk_X]

theorem copy_sum {d : ℕ} (f : R d) :
    copy f = ∑ i : Fin d, f i • x d ^ i.val := by
  simp [copy, poly, x, ← AdjoinRoot.mk_X]

theorem toRing_concat {d : ℕ} (a b : R d) :
    toRing (concat a b) = copy a + x d ^ d * copy b := by
  rw [toRing_sum, ← (blockEquiv d).sum_comp, Fintype.sum_sum_type]
  simp only [concat_left, concat_right]
  have hl (i : Fin d) : (blockEquiv d (.inl i)).val = i.val := by
    simp [blockEquiv, finSumFinEquiv]
  have hr (i : Fin d) : (blockEquiv d (.inr i)).val = d + i.val := by
    simp [blockEquiv, finSumFinEquiv, Nat.add_comm]
  simp_rw [hl, hr, pow_add]
  rw [copy_sum, copy_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_smul_comm]

/-- The cyclic quotient also has the expected unique coefficient vectors. -/
def coefficientBasis {d : ℕ} (hd : 0 < d) : Module.Basis (Fin (2 * d)) ℤ (S d) :=
  (AdjoinRoot.powerBasis' (cyclicModulus_monic hd)).basis.reindex
    (finCongr (cyclicModulus_natDegree d))

@[simp] theorem coefficientBasis_apply {d : ℕ} (hd : 0 < d) (i : Fin (2 * d)) :
    coefficientBasis hd i = x d ^ i.val := by
  rw [coefficientBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

def coeffEquiv {d : ℕ} (hd : 0 < d) : R (2 * d) ≃ₗ[ℤ] S d :=
  (coefficientBasis hd).equivFun.symm

@[simp] theorem coeffEquiv_apply {d : ℕ} (hd : 0 < d) (f : R (2 * d)) :
    coeffEquiv hd f = toRing f := by
  simp [coeffEquiv, Module.Basis.equivFun_symm_apply, toRing_sum]

theorem toRing_bijective {d : ℕ} (hd : 0 < d) : Function.Bijective (@toRing d) := by
  have he : (fun f : R (2 * d) => coeffEquiv hd f) = toRing := funext (coeffEquiv_apply hd)
  rw [← he]
  exact (coeffEquiv hd).bijective

@[simp] theorem x_pow_twice (d : ℕ) : x d ^ (2 * d) = 1 := by
  have h := AdjoinRoot.mk_self (f := cyclicModulus d)
  change AdjoinRoot.mk (cyclicModulus d) (X ^ (2 * d) - 1) = 0 at h
  simpa [map_sub, map_pow, x, sub_eq_zero] using h

@[simp] theorem square_half (d : ℕ) : (x d ^ d)^2 = 1 := by
  rw [← pow_mul, Nat.mul_comm d 2, x_pow_twice]

/-- Multiplication of copied representatives agrees with negacyclic
multiplication after projection by 1-X^d. -/
theorem anti_copy_mul {d : ℕ} (hd : 0 < d) (f g : R d) :
    (1 - x d ^ d) * copy (Cyclotomic.mul f g) =
      (1 - x d ^ d) * copy f * copy g := by
  have hdiv : modulus d ∣ poly (Cyclotomic.mul f g) - poly f * poly g := by
    exact polynomial_mul_difference_dvd hd f g
  obtain ⟨u, hu⟩ := hdiv
  have hm : AdjoinRoot.mk (cyclicModulus d) (modulus d) = x d ^ d + 1 := by
    simp [modulus, x]
  have he : copy (Cyclotomic.mul f g) - copy f * copy g =
      (x d ^ d + 1) * AdjoinRoot.mk _ u := by
    have h := congrArg (AdjoinRoot.mk (cyclicModulus d)) hu
    simpa [map_sub, map_mul, copy, hm] using h
  have hz : (1 - x d ^ d) * (x d ^ d + 1) = 0 := by
    calc
      _ = 1 - (x d ^ d)^2 := by ring
      _ = 0 := by rw [square_half]; ring
  apply sub_eq_zero.mp
  calc
    _ = (1 - x d ^ d) * (copy (Cyclotomic.mul f g) - copy f * copy g) := by ring
    _ = 0 := by rw [he, ← mul_assoc, hz, zero_mul]

/-- The copied constant polynomial 1. -/
def one {d : ℕ} (hd : 0 < d) : R d := monomial ⟨0, hd⟩ 1

@[simp] theorem copy_one {d : ℕ} (hd : 0 < d) : copy (one hd) = 1 := by
  rw [copy_sum]
  simp [one, Cyclotomic.monomial]

/-- The paper's principal generator (1-X^d)g + B(1+X^d). -/
def generator {d : ℕ} (hd : 0 < d) (g : R d) (B : ℤ) : R (2 * d) :=
  concat (g + B • one hd) (-g + B • one hd)

/-- The coefficient vector of 2(1-X^d)v. -/
def lift {d : ℕ} (v : R d) : R (2 * d) := concat ((2 : ℤ) • v) (-((2 : ℤ) • v))

theorem generator_image {d : ℕ} (hd : 0 < d) (g : R d) (B : ℤ) :
    toRing (generator hd g B) =
      (1 - x d ^ d) * copy g + B • (1 + x d ^ d) := by
  simp only [generator, toRing_concat, copy_add, copy_neg, copy_smul, copy_one]
  simp only [zsmul_eq_mul]
  ring

theorem lift_image {d : ℕ} (v : R d) :
    toRing (lift v) = 2 * (1 - x d ^ d) * copy v := by
  simp only [lift, toRing_concat, copy_neg, copy_smul]
  simp only [zsmul_eq_mul]
  ring

/-- The coefficient product G(p+X^d q). -/
def product {d : ℕ} (g : R d) (B : ℤ) (p q : R d) : R (2 * d) :=
  concat (B • (p + q) + Cyclotomic.mul g (p - q))
    (B • (p + q) - Cyclotomic.mul g (p - q))

/-- The integral block identity underlying equation `eq:principal-crt-distance`. -/
theorem product_image {d : ℕ} (hd : 0 < d) (g : R d) (B : ℤ) (p q : R d) :
    toRing (product g B p q) = toRing (generator hd g B) * toRing (concat p q) := by
  calc
    _ = (1 - x d ^ d) * copy (Cyclotomic.mul g (p - q)) +
        B • ((1 + x d ^ d) * copy (p + q)) := by
      simp only [product, toRing_concat, copy_add, copy_sub, copy_smul]
      simp only [zsmul_eq_mul]
      ring
    _ = _ := by
      rw [anti_copy_mul hd, copy_sub, copy_add, generator_image, toRing_concat]
      simp only [zsmul_eq_mul]
      linear_combination (copy g * copy q - (B : S d) * copy q) * square_half d

/-- The genuine principal cyclic ideal, viewed in coefficient coordinates. -/
def lattice {d : ℕ} (hd : 0 < d) (g : R d) (B : ℤ) : AddSubgroup (R (2 * d)) :=
  (Ideal.span {toRing (generator hd g B)}).toAddSubgroup.comap
    (coeffEquiv hd).toAddEquiv.toAddMonoidHom

@[simp] theorem mem_lattice {d : ℕ} (hd : 0 < d) (g : R d) (B : ℤ) (w : R (2 * d)) :
    w ∈ lattice hd g B ↔ toRing w ∈ Ideal.span {toRing (generator hd g B)} := by
  change coeffEquiv hd w ∈ Ideal.span {toRing (generator hd g B)} ↔
    toRing w ∈ Ideal.span {toRing (generator hd g B)}
  rw [coeffEquiv_apply]

theorem mem_lattice_iff {d : ℕ} (hd : 0 < d) (g : R d) (B : ℤ) (w : R (2 * d)) :
    w ∈ lattice hd g B ↔ ∃ p q, product g B p q = w := by
  rw [mem_lattice, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨Q, hQ⟩
    obtain ⟨v, rfl⟩ := (toRing_bijective hd).surjective Q
    obtain ⟨p, q, rfl⟩ := exists_concat v
    refine ⟨p, q, (toRing_bijective hd).injective ?_⟩
    exact (product_image hd g B p q).trans hQ.symm
  · rintro ⟨p, q, rfl⟩
    exact ⟨toRing (concat p q), product_image hd g B p q⟩

theorem sqNorm_neg {d : ℕ} (v : R d) : sqNorm (-v) = sqNorm v := by
  simp only [sqNorm, Pi.neg_apply, neg_sq]

theorem sqNorm_parallelogram {d : ℕ} (a b : R d) :
    sqNorm (concat (a + b) (a - b)) = 2 * sqNorm a + 2 * sqNorm b := by
  rw [sqNorm_concat]
  simp only [sqNorm, Pi.add_apply, Pi.sub_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Equation `eq:principal-crt-distance`, as an equality of integer squared norms. -/
theorem product_distance {d : ℕ} (g T : R d) (B : ℤ) (p q : R d) :
    sqNorm (product g B p q - lift T) =
      2 * sqNorm (Cyclotomic.mul g (p - q) - (2 : ℤ) • T) +
        2 * B ^ 2 * sqNorm (p + q) := by
  have he : product g B p q - lift T =
      concat (B • (p + q) + (Cyclotomic.mul g (p - q) - (2 : ℤ) • T))
        (B • (p + q) - (Cyclotomic.mul g (p - q) - (2 : ℤ) • T)) := by
    rw [product, lift, concat_sub]
    congr 1 <;> abel
  rw [he, sqNorm_parallelogram, sqNorm_smul]
  ring

@[simp] theorem sqNorm_lift_sub {d : ℕ} (v T : R d) :
    sqNorm (lift v - lift T) = 8 * sqNorm (v - T) := by
  have he : lift v - lift T = concat ((2 : ℤ) • (v - T)) (-((2 : ℤ) • (v - T))) := by
    rw [lift, lift, concat_sub]
    congr 1 <;> abel
  rw [he, sqNorm_concat, sqNorm_neg, sqNorm_smul]
  ring

theorem product_neg {d : ℕ} (g : R d) (B : ℤ) (p : R d) :
    product g B p (-p) = lift (Cyclotomic.mul g p) := by
  unfold product
  rw [add_neg_cancel, smul_zero, zero_add, zero_sub, sub_neg_eq_add,
    ← two_smul ℤ p, Cyclotomic.mul_smul_right]
  rfl

theorem lift_injective {d : ℕ} : Function.Injective (@lift d) := by
  intro v w h
  have he := (concat_injective h).1
  funext i
  have hi := congrFun he i
  change 2 * v i = 2 * w i at hi
  omega

theorem lift_mem {d : ℕ} (hd : 0 < d) (g : R d) (B : ℤ) (v : R d)
    (hv : v ∈ principalIdealLattice g) : lift v ∈ lattice hd g B := by
  obtain ⟨p, rfl⟩ := hv
  exact (mem_lattice_iff hd g B _).mpr ⟨p, -p, product_neg g B p⟩

/-- Paper Lemma `lem:principal-crt`: exactly the small cyclic points arise
uniquely from the original principal ideal, with distances multiplied by 8. -/
theorem small_iff {d : ℕ} (hd : 0 < d) (g T : R d) (B H : ℤ)
    (hB : 4 * H < B ^ 2) (w : R (2 * d)) :
    (w ∈ lattice hd g B ∧ sqNorm (w - lift T) ≤ 8 * H) ↔
      ∃ v : R d, v ∈ principalIdealLattice g ∧ w = lift v ∧ sqNorm (v - T) ≤ H := by
  constructor
  · rintro ⟨hw, hdist⟩
    obtain ⟨p, q, rfl⟩ := (mem_lattice_iff hd g B w).mp hw
    have hr : p + q = 0 := by
      by_contra hne
      have hn := sqNorm_pos hne
      have hz := sqNorm_nonneg (Cyclotomic.mul g (p - q) - (2 : ℤ) • T)
      have hsq := sq_nonneg B
      rw [product_distance] at hdist
      nlinarith
    have hq : q = -p := by
      funext i
      have hi := congrFun hr i
      simp only [Pi.add_apply, Pi.zero_apply] at hi
      simp only [Pi.neg_apply]
      omega
    subst q
    rw [product_neg] at hdist ⊢
    refine ⟨Cyclotomic.mul g p, ⟨p, rfl⟩, rfl, ?_⟩
    rw [sqNorm_lift_sub] at hdist
    omega
  · rintro ⟨v, hv, rfl, hdist⟩
    exact ⟨lift_mem hd g B v hv, by rw [sqNorm_lift_sub]; omega⟩

/-- The small-point correspondence is a bijection, as asserted by the lemma. -/
def smallEquiv {d : ℕ} (hd : 0 < d) (g T : R d) (B H : ℤ) (hB : 4 * H < B ^ 2) :
    {v : R d // v ∈ principalIdealLattice g ∧ sqNorm (v - T) ≤ H} ≃
      {w : R (2 * d) // w ∈ lattice hd g B ∧ sqNorm (w - lift T) ≤ 8 * H} := by
  apply Equiv.ofBijective (fun v => ⟨lift v.val, lift_mem hd g B _ v.property.1,
    by rw [sqNorm_lift_sub]; linarith [v.property.2]⟩)
  constructor
  · intro v w h
    apply Subtype.ext
    exact lift_injective (congrArg Subtype.val h)
  · rintro ⟨w, hw⟩
    obtain ⟨v, hv, rfl, hdist⟩ := (small_iff hd g T B H hB w).mp hw
    exact ⟨⟨v, hv, hdist⟩, rfl⟩

/-- The cyclic multiplication columns are independent whenever the original
multiplication columns are independent and B is nonzero. -/
theorem product_injective {d : ℕ} (g : R d) (B : ℤ)
    (hg : Function.Injective (Cyclotomic.mul g)) (hB : B ≠ 0)
    {p q p' q' : R d} (h : product g B p q = product g B p' q') :
    p = p' ∧ q = q' := by
  obtain ⟨hlo, hhi⟩ := concat_injective h
  have hr : p + q = p' + q' := by
    funext i
    apply mul_left_cancel₀ hB
    have hl := congrFun hlo i
    have hh := congrFun hhi i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hl hh ⊢
    linarith
  have hz : p - q = p' - q' := by
    apply hg
    funext i
    have hl := congrFun hlo i
    have hh := congrFun hhi i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hl hh ⊢
    linarith
  constructor <;> funext i
  · have hri := congrFun hr i
    have hzi := congrFun hz i
    simp only [Pi.add_apply, Pi.sub_apply] at hri hzi
    omega
  · have hri := congrFun hr i
    have hzi := congrFun hz i
    simp only [Pi.add_apply, Pi.sub_apply] at hri hzi
    omega

/-- Multiplication by the cyclic generator, transported to coefficients. -/
def mulHom {d : ℕ} (hd : 0 < d) (g : R d) (B : ℤ) : R (2 * d) →+ R (2 * d) where
  toFun v := (coeffEquiv hd).symm (toRing (generator hd g B) * coeffEquiv hd v)
  map_zero' := by rw [map_zero, MulZeroClass.mul_zero, map_zero]
  map_add' a b := by rw [map_add, _root_.mul_add, map_add]

@[simp] theorem mulHom_concat {d : ℕ} (hd : 0 < d) (g : R d) (B : ℤ) (p q : R d) :
    mulHom hd g B (concat p q) = product g B p q := by
  apply (coeffEquiv hd).injective
  change coeffEquiv hd ((coeffEquiv hd).symm
    (toRing (generator hd g B) * coeffEquiv hd (concat p q))) = coeffEquiv hd (product g B p q)
  rw [LinearEquiv.apply_symm_apply, coeffEquiv_apply, coeffEquiv_apply]
  exact (product_image hd g B p q).symm

theorem mulHom_injective {d : ℕ} (hd : 0 < d) (g : R d) (B : ℤ)
    (hg : Function.Injective (Cyclotomic.mul g)) (hB : B ≠ 0) :
    Function.Injective (mulHom hd g B) := by
  intro a b hab
  obtain ⟨p, q, rfl⟩ := exists_concat a
  obtain ⟨p', q', rfl⟩ := exists_concat b
  rw [mulHom_concat, mulHom_concat] at hab
  obtain ⟨rfl, rfl⟩ := product_injective g B hg hB hab
  rfl

theorem mulHom_range {d : ℕ} (hd : 0 < d) (g : R d) (B : ℤ) :
    (mulHom hd g B).range = lattice hd g B := by
  ext w
  rw [AddMonoidHom.mem_range, mem_lattice_iff]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨p, q, rfl⟩ := exists_concat a
    exact ⟨p, q, (mulHom_concat hd g B p q).symm.trans ha⟩
  · rintro ⟨p, q, rfl⟩
    exact ⟨concat p q, mulHom_concat hd g B p q⟩

/-- A full integer basis of the actual principal cyclic ideal. -/
def multiplicationBasis {d : ℕ} (hd : 0 < d) (g : R d) (B : ℤ)
    (hg : Function.Injective (Cyclotomic.mul g)) (hB : B ≠ 0) :
    Module.Basis (Fin (2 * d)) ℤ (lattice hd g B) := by
  let e : R (2 * d) ≃+ (mulHom hd g B).range :=
    AddEquiv.ofBijective (mulHom hd g B).rangeRestrict
      ⟨(fun _ _ h => mulHom_injective hd g B hg hB (congrArg Subtype.val h)),
        (mulHom hd g B).rangeRestrict_surjective⟩
  let b := (Pi.basisFun ℤ (Fin (2 * d))).map e.toIntLinearEquiv
  exact (mulHom_range hd g B) ▸ b

/-- Full rank for every nonzero power-of-two cyclotomic generator.
The plus/minus block proof above needs only `B ≠ 0`. -/
def principalMultiplicationBasis {d : ℕ} (hd : ∃ k, d = 2 ^ k)
    (g : R d) (hg : g ≠ 0) (B : ℤ) (hB : B ≠ 0) :
    Module.Basis (Fin (2 * d)) ℤ (lattice (power_two_pos hd) g B) :=
  multiplicationBasis (power_two_pos hd) g B (Cyclotomic.mul_injective hd hg) hB

/-- In particular the paper's separation condition supplies a full basis. -/
theorem principal_full_rank {d : ℕ} (hd : ∃ k, d = 2 ^ k)
    (g : R d) (hg : g ≠ 0) (B H : ℤ) (hH : 0 ≤ H) (hB : 4 * H < B ^ 2) :
    Nonempty (Module.Basis (Fin (2 * d)) ℤ (lattice (power_two_pos hd) g B)) := by
  exact ⟨principalMultiplicationBasis hd g hg B (by intro h; subst B; norm_num at hB; omega)⟩

/-- Transfer any integral lower bound through the separated lift. -/
theorem lower_bound {d : ℕ} (hd : 0 < d) (g T : R d) (B H : ℤ)
    (hB : 4 * H < B ^ 2)
    (hmin : ∀ v ∈ principalIdealLattice g, H ≤ sqNorm (v - T)) :
    ∀ w ∈ lattice hd g B, 8 * H ≤ sqNorm (w - lift T) := by
  intro w hw
  by_cases hdist : sqNorm (w - lift T) ≤ 8 * H
  · obtain ⟨v, hv, rfl, _⟩ := (small_iff hd g T B H hB w).mp ⟨hw, hdist⟩
    rw [sqNorm_lift_sub]
    linarith [hmin v hv]
  · omega

theorem cvp_iff {d : ℕ} (hd : 0 < d) (g T : R d) (B H : ℤ) (hB : 4 * H < B ^ 2) :
    CVPYes (lattice hd g B) (lift T) (8 * H) ↔ CVPYes (principalIdealLattice g) T H := by
  constructor
  · rintro ⟨w, hw, hdist⟩
    obtain ⟨v, hv, _, hdist'⟩ := (small_iff hd g T B H hB w).mp ⟨hw, hdist⟩
    exact ⟨v, hv, hdist'⟩
  · rintro ⟨v, hv, hdist⟩
    exact ⟨lift v, lift_mem hd g B v hv, by rw [sqNorm_lift_sub]; omega⟩

theorem minimum_lift {d : ℕ} (hd : 0 < d) (g T : R d) (B H : ℤ)
    (hB : 4 * H < B ^ 2) (hmin : MinimumSquaredDistance (principalIdealLattice g) T H) :
    MinimumSquaredDistance (lattice hd g B) (lift T) (8 * H) := by
  constructor
  · obtain ⟨v, hv, hdist⟩ := hmin.1
    exact ⟨lift v, lift_mem hd g B v hv, by rw [sqNorm_lift_sub, hdist]⟩
  · exact lower_bound hd g T B H hB hmin.2

/-- The paper's integer penalty 2 ceil(sqrt(H)) + 1. -/
def penalty (H : ℤ) : ℤ := 2 * (ReductionData.ceilSqrt H.toNat : ℤ) + 1

theorem penalty_sq_gt (H : ℤ) (hH : 0 ≤ H) : 4 * H < (penalty H)^2 := by
  have hn := (ReductionData.ceilSqrt_le_iff H.toNat (ReductionData.ceilSqrt H.toNat)).mp le_rfl
  have hs : H ≤ (ReductionData.ceilSqrt H.toNat : ℤ)^2 := by
    have hn' : (H.toNat : ℤ) ≤ (ReductionData.ceilSqrt H.toNat : ℤ)^2 := by
      exact_mod_cast hn
    simpa only [Int.toNat_of_nonneg hH] using hn'
  dsimp [penalty]
  have hz : (0 : ℤ) ≤ ReductionData.ceilSqrt H.toNat := by positivity
  nlinarith

end IdealCVP.Cyclic

namespace IdealCVP
open IdealCVP.Cyclotomic

namespace X3CInstance

theorem cvp_dimension_pos (I : X3CInstance) : 0 < (x3cToCVP I).d := by
  obtain ⟨k, hk⟩ := (x3cToCVP I).power_two
  rw [hk]
  positivity

def cyclicPenalty (I : X3CInstance) : ℤ := Cyclic.penalty ((x3cToCVP I).Δ + 4)

theorem cyclicPenalty_sq_gt (I : X3CInstance) :
    4 * ((x3cToCVP I).Δ + 4) < I.cyclicPenalty ^ 2 :=
  Cyclic.penalty_sq_gt _ (by have := (x3cToCVP I).Δ_nonneg; omega)

def cyclicLattice (I : X3CInstance) : AddSubgroup (R (2 * (x3cToCVP I).d)) :=
  Cyclic.lattice I.cvp_dimension_pos (x3cToCVP I).g I.cyclicPenalty

def cyclicGenerator (I : X3CInstance) : R (2 * (x3cToCVP I).d) :=
  Cyclic.generator I.cvp_dimension_pos (x3cToCVP I).g I.cyclicPenalty

def cyclicTarget (I : X3CInstance) : R (2 * (x3cToCVP I).d) :=
  Cyclic.lift (x3cToCVP I).T

/-- Full rank: precisely 2d independent integer multiplication columns. -/
def cyclicBasis (I : X3CInstance) :
    Module.Basis (Fin (2 * (x3cToCVP I).d)) ℤ I.cyclicLattice :=
  Cyclic.multiplicationBasis I.cvp_dimension_pos (x3cToCVP I).g I.cyclicPenalty
    (Cyclotomic.mul_injective (x3cToCVP I).power_two (x3cToCVP I).g_ne_zero) (by
      have hp := I.cyclicPenalty_sq_gt
      have hΔ := (x3cToCVP I).Δ_nonneg
      intro hz
      rw [hz] at hp
      norm_num at hp
      omega)

end X3CInstance

/-- The actual cyclic generator, target, and squared threshold, in dimension 2d. -/
def x3cToCyclicCVP (I : X3CInstance) :
    R (2 * (x3cToCVP I).d) × R (2 * (x3cToCVP I).d) × ℤ :=
  (I.cyclicGenerator, I.cyclicTarget, 8 * (x3cToCVP I).Δ)

theorem x3c_cyclic_power_two (I : X3CInstance) : ∃ k, 2 * (x3cToCVP I).d = 2 ^ k := by
  obtain ⟨k, hk⟩ := (x3cToCVP I).power_two
  exact ⟨k + 1, by rw [hk, pow_succ]; omega⟩

/-- Theorem `thm:cyclic-cvp`, mathematical decision correctness. -/
theorem x3c_cyclic_correct (I : X3CInstance) :
    I.HasExactCover ↔ CVPYes I.cyclicLattice I.cyclicTarget (8 * (x3cToCVP I).Δ) := by
  apply (x3c_correct I).trans
  exact (Cyclic.cvp_iff I.cvp_dimension_pos (x3cToCVP I).g (x3cToCVP I).T
    I.cyclicPenalty (x3cToCVP I).Δ (by have := I.cyclicPenalty_sq_gt; omega)).symm

theorem x3c_cyclic_yes_gap (I : X3CInstance) (hy : I.HasExactCover) :
    MinimumSquaredDistance I.cyclicLattice I.cyclicTarget (8 * (x3cToCVP I).Δ) :=
  Cyclic.minimum_lift I.cvp_dimension_pos (x3cToCVP I).g (x3cToCVP I).T
    I.cyclicPenalty (x3cToCVP I).Δ (by have := I.cyclicPenalty_sq_gt; omega)
    (x3c_yes_gap I hy)

theorem x3c_cyclic_no_gap (I : X3CInstance) (hn : ¬ I.HasExactCover) :
    ∀ w ∈ I.cyclicLattice, 8 * (x3cToCVP I).Δ + 32 ≤ sqNorm (w - I.cyclicTarget) := by
  have h := Cyclic.lower_bound I.cvp_dimension_pos (x3cToCVP I).g (x3cToCVP I).T
    I.cyclicPenalty ((x3cToCVP I).Δ + 4) I.cyclicPenalty_sq_gt (x3c_no_gap I hn)
  intro w hw
  have hi := h w hw
  change 8 * (x3cToCVP I).Δ + 32 ≤ sqNorm (w - Cyclic.lift (x3cToCVP I).T)
  nlinarith

end IdealCVP
