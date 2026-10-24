import IdealCVP.GeneralFullRank
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Exact cyclotomic module-SIVP

The scalar field is the genuine rational polynomial quotient. Norms are
ordinary integral coefficient norms. Minima are stated with attainment and
universal lower bounds, without an infimum convention.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace IdealCVP.ModuleSIVP
open IdealCVP IdealCVP.Cyclotomic Polynomial

abbrev K (d : ℕ) := AdjoinRoot ((X : Polynomial ℚ) ^ d + 1)

variable {d : ℕ} [Fact (∃ k, d = 2 ^ k)]

instance integralDomain : IsDomain (QuotRing d) := quotRing_isDomain (Fact.out)
instance rationalIrreducible : Fact (Irreducible ((X : Polynomial ℚ) ^ d + 1)) :=
  ⟨modulus_irreducible_rat (Fact.out)⟩

theorem dimension_pos : 0 < d := power_two_pos (Fact.out)

/-- The natural embedding of the integral quotient into the rational quotient. -/
def scalarMap : QuotRing d →+* K d :=
  AdjoinRoot.map (Int.castRingHom ℚ) (modulus d) (X ^ d + 1)
    (by simp [modulus])

/-- Rational monomial coefficient basis. -/
def rationalBasis : Module.Basis (Fin d) ℚ (K d) :=
  (AdjoinRoot.powerBasis'
    (show ((X : Polynomial ℚ) ^ d + 1).Monic by
      simpa using (Polynomial.monic_X_pow_add_C (1 : ℚ)
        (by have := dimension_pos (d := d); omega)))).basis.reindex
    (finCongr (by simp))

@[simp] theorem rationalBasis_apply (i : Fin d) :
    rationalBasis i = AdjoinRoot.root ((X : Polynomial ℚ) ^ d + 1) ^ i.val := by
  rw [rationalBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

theorem scalarMap_toQuot (a : R d) :
    scalarMap (toQuot a) = rationalBasis.equivFun.symm (fun i => (a i : ℚ)) := by
  simp [toQuot, Module.Basis.equivFun_symm_apply, scalarMap, Algebra.smul_def]

theorem scalarMap_injective : Function.Injective (scalarMap (d := d)) := by
  intro x y h
  obtain ⟨a, rfl⟩ := (toQuot_bijective dimension_pos).surjective x
  obtain ⟨b, rfl⟩ := (toQuot_bijective dimension_pos).surjective y
  rw [scalarMap_toQuot, scalarMap_toQuot] at h
  have hh := rationalBasis.equivFun.symm.injective h
  congr 1
  funext i
  exact_mod_cast congrFun hh i

/-- Coefficient squared norm on the actual integral quotient. -/
def normSq (x : QuotRing d) : ℤ := sqNorm ((quotEquiv dimension_pos).symm x)

theorem normSq_nonneg (x : QuotRing d) : 0 ≤ normSq x := sqNorm_nonneg _
@[simp] theorem normSq_toQuot (a : R d) : normSq (toQuot a) = sqNorm a := by
  rw [← quotEquiv_apply dimension_pos]
  exact congrArg sqNorm ((quotEquiv dimension_pos).symm_apply_apply a)
@[simp] theorem normSq_zero : normSq (0 : QuotRing d) = 0 := by simp [normSq]
@[simp] theorem normSq_neg (x : QuotRing d) : normSq (-x) = normSq x := by
  simp [normSq, sqNorm, map_neg]
theorem normSq_pos {x : QuotRing d} (hx : x ≠ 0) : 1 ≤ normSq x := by
  apply sqNorm_pos
  intro h
  apply hx
  exact (quotEquiv dimension_pos).symm.injective (by simpa using h)
theorem normSq_int_mul (Q : ℤ) (x : QuotRing d) :
    normSq ((Q : QuotRing d) * x) = Q ^ 2 * normSq x := by
  rw [← zsmul_eq_mul]
  simp only [normSq, map_smul, sqNorm_smul]

def vectorNormSq (v : QuotRing d × QuotRing d) : ℤ := normSq v.1 + normSq v.2

/-- The `2d` ordinary integer coefficients of a module vector. -/
def coefficientVector (v : QuotRing d × QuotRing d) : (Fin d ⊕ Fin d) → ℤ :=
  Cyclotomic.pair ((quotEquiv dimension_pos).symm v.1)
    ((quotEquiv dimension_pos).symm v.2)

theorem vectorNormSq_eq_coefficients (v : QuotRing d × QuotRing d) :
    vectorNormSq v = sqNorm (coefficientVector v) :=
  (sqNorm_pair _ _).symm

def fieldVector (v : QuotRing d × QuotRing d) : K d × K d :=
  (scalarMap v.1, scalarMap v.2)

/-- Honest independence over `ℚ[X]/(X^d+1)`. -/
def Independent (u v : QuotRing d × QuotRing d) : Prop :=
  LinearIndependent (K d) ![fieldVector u, fieldVector v]

/-- The determinant criterion used by the decision problem is equivalent to
field-linear independence. -/
theorem independent_iff (u v : QuotRing d × QuotRing d) :
    Independent u v ↔ u.1 * v.2 - u.2 * v.1 ≠ 0 := by
  have field_criterion (x y : K d × K d) :
      LinearIndependent (K d) ![x, y] ↔ x.1 * y.2 - x.2 * y.1 ≠ 0 := by
    rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    constructor
    · rintro ⟨hy, hxy⟩ hz
      by_cases h1 : y.1 = 0
      · have h2 : y.2 ≠ 0 := by intro h; apply hy; exact Prod.ext h1 h
        have hx : x.1 = 0 := by simpa [h1, h2] using hz
        apply hxy (x.2 / y.2)
        apply Prod.ext
        · simp [h1, hx]
        · simp [h2]
      · apply hxy (x.1 / y.1)
        apply Prod.ext
        · simp [h1]
        · change x.1 / y.1 * y.2 = x.2
          apply (div_mul_eq_mul_div ..).trans
          apply (div_eq_iff h1).mpr
          linear_combination hz
    · intro h
      constructor
      · rintro rfl; simp at h
      · intro c hc
        have h1 := congrArg Prod.fst hc
        have h2 := congrArg Prod.snd hc
        change c * y.1 = x.1 at h1
        change c * y.2 = x.2 at h2
        apply h
        rw [← h1, ← h2]
        ring
  rw [Independent, field_criterion]
  change scalarMap u.1 * scalarMap v.2 - scalarMap u.2 * scalarMap v.1 ≠ 0 ↔ _
  rw [← map_mul, ← map_mul, ← map_sub]
  exact not_congr (map_eq_zero_iff _ scalarMap_injective)

/-- The lower triangular completion map. -/
def completionMap (Q : ℤ) (g T : QuotRing d) :
    (QuotRing d × QuotRing d) →ₗ[QuotRing d] (QuotRing d × QuotRing d) where
  toFun ab := ((Q : QuotRing d) * ab.1, T * ab.1 + g * ab.2)
  map_add' a b := by ext <;> dsimp <;> ring
  map_smul' c a := by ext <;> dsimp <;> ring

/-- `M_{Q,g,T}` as a genuine module, hence also an additive subgroup. -/
def completion (Q : ℤ) (g T : QuotRing d) : Submodule (QuotRing d) (QuotRing d × QuotRing d) :=
  (completionMap Q g T).range

theorem mem_completion (Q : ℤ) (g T : QuotRing d) (v : QuotRing d × QuotRing d) :
    v ∈ completion Q g T ↔ ∃ a b, v = ((Q : QuotRing d) * a, T * a + g * b) := by
  constructor
  · rintro ⟨⟨a,b⟩, h⟩; exact ⟨a,b,h.symm⟩
  · rintro ⟨a,b,rfl⟩; exact ⟨(a,b),rfl⟩

theorem completionMap_injective (Q : ℤ) (hQ : Q ≠ 0) (g T : QuotRing d) (hg : g ≠ 0) :
    Function.Injective (completionMap Q g T) := by
  have hQc : (Q : QuotRing d) ≠ 0 := by
    intro h
    have hh := congrArg scalarMap h
    simp only [map_intCast, map_zero] at hh
    exact hQ (by exact_mod_cast hh)
  intro a b h
  have ha : a.1 = b.1 := mul_left_cancel₀ hQc (congrArg Prod.fst h)
  have hb : a.2 = b.2 := by
    apply mul_left_cancel₀ hg
    have hh := congrArg Prod.snd h
    change T * a.1 + g * a.2 = T * b.1 + g * b.2 at hh
    simpa [ha] using hh
  exact Prod.ext ha hb

/-- The two displayed columns form an `R_d`-basis. -/
def completionBasis (Q : ℤ) (hQ : Q ≠ 0) (g T : QuotRing d) (hg : g ≠ 0) :
    Module.Basis (Fin 2) (QuotRing d) (completion Q g T) :=
  (Pi.basisFun (QuotRing d) (Fin 2)).map
    ((LinearEquiv.finTwoArrow (QuotRing d) (QuotRing d)).trans
      (LinearEquiv.ofBijective (completionMap Q g T).rangeRestrict
        ⟨(fun _ _ h => completionMap_injective Q hQ g T hg (congrArg Subtype.val h)),
          (by rintro ⟨v, a, rfl⟩; exact ⟨a, rfl⟩)⟩))

/-- Decision version of the squared second field-linear successive minimum. -/
def SecondMinimumSq (M : Submodule (QuotRing d) (QuotRing d × QuotRing d)) (Γ : ℤ) : Prop :=
  ∃ u ∈ M, ∃ v ∈ M, Independent u v ∧ vectorNormSq u ≤ Γ ∧ vectorNormSq v ≤ Γ

/-- Exact value: attainment and the universal bound for all independent pairs. -/
def ExactSecondMinimumSq (M : Submodule (QuotRing d) (QuotRing d × QuotRing d)) (r : ℤ) : Prop :=
  (∃ u ∈ M, ∃ v ∈ M, Independent u v ∧ max (vectorNormSq u) (vectorNormSq v) = r) ∧
  ∀ u ∈ M, ∀ v ∈ M, Independent u v → r ≤ max (vectorNormSq u) (vectorNormSq v)

/-- An integral vector of squared norm one has one coefficient equal to
`1` or `-1` and all other coefficients zero. -/
theorem sqNorm_one_monomial (a : R d) (ha : sqNorm a = 1) :
    ∃ j : Fin d, a = Cyclotomic.monomial j 1 ∨ a = -(Cyclotomic.monomial j 1) := by
  classical
  have hne : a ≠ 0 := by intro h; simp [h] at ha
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra h
    apply hne
    funext i
    simpa using (not_exists.mp h i)
  have hjle : a j ^ 2 ≤ sqNorm a :=
    Finset.single_le_sum (fun i _ => sq_nonneg (a i)) (Finset.mem_univ j)
  have hjval : a j = 1 ∨ a j = -1 := by
    have : a j ≤ -1 ∨ 1 ≤ a j := by omega
    rcases this with h | h <;> (first | left; nlinarith | right; nlinarith)
  have hjsq : a j ^ 2 = 1 := by rcases hjval with h | h <;> rw [h] <;> norm_num
  have hsum : ∑ i ∈ (Finset.univ : Finset (Fin d)).erase j, a i ^ 2 = 0 := by
    have hh := Finset.sum_erase_add (Finset.univ : Finset (Fin d))
      (fun i => a i ^ 2) (Finset.mem_univ j)
    change _ + _ = sqNorm a at hh
    omega
  have hz (i : Fin d) (hi : i ≠ j) : a i = 0 := by
    have hh := Finset.single_le_sum (fun i _ => sq_nonneg (a i))
      (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
    rw [hsum] at hh
    nlinarith [sq_nonneg (a i)]
  refine ⟨j, ?_⟩
  rcases hjval with hjv | hjv
  · left; funext i; by_cases hi : i = j <;> simp [Cyclotomic.monomial, hi, hjv, hz]
  · right; funext i; by_cases hi : i = j <;> simp [Cyclotomic.monomial, hi, hjv, hz]

@[simp] theorem toQuot_monomial (j : Fin d) :
    toQuot (Cyclotomic.monomial j 1) = AdjoinRoot.root (modulus d) ^ j.val := by
  classical
  simp [toQuot, Cyclotomic.monomial]

/-- The root is a unit even over the integral quotient. -/
theorem root_isUnit : IsUnit (AdjoinRoot.root (modulus d)) := by
  apply IsUnit.of_mul_eq_one (-(AdjoinRoot.root (modulus d) ^ (d - 1)))
  rw [_root_.mul_neg, ← pow_succ', Nat.sub_add_cancel (dimension_pos (d := d)), root_pow_dimension]
  simp

/-- The `±y^j` case supplies both an integral inverse and an isometry. -/
theorem normSq_one_unit_isometry {a : QuotRing d} (ha : normSq a = 1) :
    IsUnit a ∧ ∀ x : QuotRing d, normSq (a * x) = normSq x := by
  obtain ⟨v, rfl⟩ := (toQuot_bijective dimension_pos).surjective a
  rw [normSq_toQuot] at ha
  obtain ⟨j, hv | hv⟩ := sqNorm_one_monomial v ha
  · subst v
    constructor
    · rw [toQuot_monomial]; exact (root_isUnit (d := d)).pow _
    · intro x
      obtain ⟨w, rfl⟩ := (toQuot_bijective dimension_pos).surjective x
      rw [← toQuot_mul dimension_pos, normSq_toQuot, normSq_toQuot]
      exact sqNorm_monomial_mul j w
  · subst v
    have hneg : toQuot (-(Cyclotomic.monomial j 1)) = -toQuot (Cyclotomic.monomial j 1) := by
      simp [toQuot]
    rw [hneg]
    constructor
    · rw [toQuot_monomial]; exact ((root_isUnit (d := d)).pow _).neg
    · intro x
      rw [_root_.neg_mul, normSq_neg]
      obtain ⟨w, rfl⟩ := (toQuot_bijective dimension_pos).surjective x
      rw [← toQuot_mul dimension_pos, normSq_toQuot, normSq_toQuot]
      exact sqNorm_monomial_mul j w

/-- Minimum distance in quotient coordinates, retaining the ideal multiplier. -/
def MinimumDistanceSq (g T : QuotRing d) (δ : ℤ) : Prop :=
  (∃ b, normSq (T - g * b) = δ) ∧ ∀ b, δ ≤ normSq (T - g * b)

theorem minimumDistance_nonneg {g T : QuotRing d} {δ : ℤ}
    (h : MinimumDistanceSq g T δ) : 0 ≤ δ := by
  obtain ⟨b, hb⟩ := h.1
  rw [← hb]
  exact normSq_nonneg _

theorem minimumDistance_le_target {g T : QuotRing d} {δ : ℤ}
    (h : MinimumDistanceSq g T δ) : δ ≤ normSq T := by
  simpa using h.2 0

/-- Existence follows from the well-ordering of the integral squared norms. -/
theorem exists_minimumDistance (g T : QuotRing d) : ∃ δ, MinimumDistanceSq g T δ := by
  classical
  let P : ℕ → Prop := fun n => ∃ b, normSq (T - g * b) = (n : ℤ)
  have hp : ∃ n, P n := ⟨(normSq T).toNat, 0, by simp [Int.toNat_of_nonneg (normSq_nonneg T)]⟩
  refine ⟨(Nat.find hp : ℤ), ?_⟩
  constructor
  · exact Nat.find_spec hp
  · intro b
    have hb : P (normSq (T - g * b)).toNat :=
      ⟨b, (Int.toNat_of_nonneg (normSq_nonneg _)).symm⟩
    have hh := Nat.find_min' hp hb
    exact_mod_cast (show (Nat.find hp : ℤ) ≤ normSq (T - g * b) by
      simpa only [Int.toNat_of_nonneg (normSq_nonneg _)] using (Int.ofNat_le.mpr hh))

@[simp] theorem normSq_one : normSq (1 : QuotRing d) = 1 := by
  have h := normSq_toQuot (Cyclotomic.monomial (⟨0, dimension_pos⟩ : Fin d) 1)
  simpa [sqNorm, Cyclotomic.monomial] using h

@[simp] theorem normSq_int (Q : ℤ) : normSq (Q : QuotRing d) = Q ^ 2 := by
  simpa using normSq_int_mul Q (1 : QuotRing d)

theorem intCast_ne_zero {Q : ℤ} (hQ : Q ≠ 0) : (Q : QuotRing d) ≠ 0 := by
  intro h
  have hh := congrArg scalarMap h
  simp only [map_intCast, map_zero] at hh
  exact hQ (by exact_mod_cast hh)

/-- Every vector outside the vertical field line has the required lower bound. -/
theorem outside_lower_bound (Q : ℤ) (g T : QuotRing d) {δ : ℤ}
    (hQT : normSq T < Q ^ 2) (hmin : MinimumDistanceSq g T δ)
    (a b : QuotRing d) (ha : a ≠ 0) :
    Q ^ 2 + δ ≤ vectorNormSq ((Q : QuotRing d) * a, T * a + g * b) := by
  change _ ≤ normSq ((Q : QuotRing d) * a) + normSq (T * a + g * b)
  rw [normSq_int_mul]
  by_cases hnorm : normSq a = 1
  · obtain ⟨hu, hiso⟩ := normSq_one_unit_isometry hnorm
    obtain ⟨c, hc⟩ := hu.exists_right_inv
    have he : T * a + g * b = a * (T - g * (-c * b)) := by
      calc
        T * a + g * b = T * a + g * b * (a * c) := by rw [hc, mul_one]
        _ = _ := by ring
    rw [he, hiso, hnorm]
    have := hmin.2 (-c * b)
    omega
  · have htwo : 2 ≤ normSq a := by have := normSq_pos ha; omega
    have hδ := minimumDistance_le_target hmin
    have hn := normSq_nonneg (T * a + g * b)
    have hQ : 0 ≤ Q ^ 2 := sq_nonneg Q
    nlinarith

/-- Any field-independent pair contains a vector outside the vertical line. -/
theorem pair_lower_bound (Q : ℤ) (g T : QuotRing d) {δ : ℤ}
    (hQT : normSq T < Q ^ 2) (hmin : MinimumDistanceSq g T δ) :
    ∀ u ∈ completion Q g T, ∀ v ∈ completion Q g T,
      Independent u v → Q ^ 2 + δ ≤ max (vectorNormSq u) (vectorNormSq v) := by
  intro u hu v hv huv
  obtain ⟨a,b,rfl⟩ := (mem_completion Q g T u).mp hu
  obtain ⟨c,e,rfl⟩ := (mem_completion Q g T v).mp hv
  by_cases ha : a = 0
  · have hc : c ≠ 0 := by
      intro hc
      rw [independent_iff] at huv
      simp [ha, hc] at huv
    exact (outside_lower_bound Q g T hQT hmin c e hc).trans (le_max_right _ _)
  · exact (outside_lower_bound Q g T hQT hmin a b ha).trans (le_max_left _ _)

/-- Paper Lemma `lem:module-completion`, exact squared minimum.
`completionBasis` supplies its freeness and the two stated basis columns. -/
theorem module_completion (Q : ℤ) (hQ : 0 < Q) (g T : QuotRing d) (hg : g ≠ 0)
    (hQT : normSq T < Q ^ 2) (hQg : normSq g < Q ^ 2) {δ : ℤ}
    (hmin : MinimumDistanceSq g T δ) :
    ExactSecondMinimumSq (completion Q g T) (Q ^ 2 + δ) := by
  refine ⟨?_, pair_lower_bound Q g T hQT hmin⟩
  obtain ⟨b,hb⟩ := hmin.1
  let u : QuotRing d × QuotRing d := ((Q : QuotRing d), T - g * b)
  let v : QuotRing d × QuotRing d := (0,g)
  have hu : u ∈ completion Q g T := by
    apply (mem_completion Q g T u).mpr
    exact ⟨1, -b, by dsimp [u]; ext <;> simp [sub_eq_add_neg]⟩
  have hv : v ∈ completion Q g T := by
    apply (mem_completion Q g T v).mpr
    exact ⟨0, 1, by simp [v]⟩
  have huv : Independent u v := by
    rw [independent_iff]
    simpa [u,v] using mul_ne_zero (intCast_ne_zero (ne_of_gt hQ)) hg
  refine ⟨u,hu,v,hv,huv,?_⟩
  have hun : vectorNormSq u = Q ^ 2 + δ := by simp [vectorNormSq, u, hb]
  have hvn : vectorNormSq v = normSq g := by simp [vectorNormSq, v]
  rw [hun, hvn, max_eq_left]
  have := minimumDistance_nonneg hmin
  omega

/-- The attained minimum gives the exact decision predicate. -/
theorem secondMinimumSq_iff {M : Submodule (QuotRing d) (QuotRing d × QuotRing d)}
    {r Γ : ℤ} (h : ExactSecondMinimumSq M r) : SecondMinimumSq M Γ ↔ r ≤ Γ := by
  constructor
  · rintro ⟨u,hu,v,hv,hi,hn1,hn2⟩
    exact (h.2 u hu v hv hi).trans (max_le hn1 hn2)
  · intro hr
    obtain ⟨u,hu,v,hv,hi,he⟩ := h.1
    exact ⟨u,hu,v,hv,hi, (le_max_left _ _).trans (he.le.trans hr),
      (le_max_right _ _).trans (he.le.trans hr)⟩

theorem normSq_residual (g T b : R d) :
    normSq (toQuot T - toQuot g * toQuot b) = sqNorm (mul g b - T) := by
  rw [← toQuot_mul dimension_pos]
  have he : toQuot T - toQuot (mul g b) = toQuot (T - mul g b) := by
    rw [← quotEquiv_apply dimension_pos T,
      ← quotEquiv_apply dimension_pos (mul g b),
      ← quotEquiv_apply dimension_pos (T - mul g b)]
    exact ((quotEquiv dimension_pos).map_sub T (mul g b)).symm
  rw [he, normSq_toQuot]
  unfold sqNorm
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

/-- Transfer the existing coefficient minimum into the actual quotient ring. -/
theorem minimumDistance_of_coeff {g T : R d} {δ : ℤ}
    (h : MinimumSquaredDistance (principalIdealLattice g) T δ) :
    MinimumDistanceSq (toQuot g) (toQuot T) δ := by
  constructor
  · obtain ⟨v,hv,hd⟩ := h.1
    obtain ⟨b,rfl⟩ := (mem_principalIdealLattice g v).mp hv
    exact ⟨toQuot b, (normSq_residual g T b).trans hd⟩
  · intro b
    obtain ⟨b,rfl⟩ := (toQuot_bijective dimension_pos).surjective b
    rw [normSq_residual]
    exact h.2 _ ⟨b,rfl⟩

/-- The paper's integer scale `1 + ceil(sqrt(max(‖T‖², ‖g‖²)))`. -/
def completionScale (g T : R d) : ℤ :=
  1 + (ReductionData.ceilSqrt (max (sqNorm T) (sqNorm g)).toNat : ℤ)

theorem completionScale_pos (g T : R d) : 0 < completionScale g T := by
  unfold completionScale
  positivity

theorem completionScale_bounds (g T : R d) :
    sqNorm T < completionScale g T ^ 2 ∧ sqNorm g < completionScale g T ^ 2 := by
  let m := max (sqNorm T) (sqNorm g)
  have hm : 0 ≤ m := le_trans (sqNorm_nonneg T) (le_max_left _ _)
  have hh := (ReductionData.ceilSqrt_le_iff m.toNat
    (ReductionData.ceilSqrt m.toNat)).mp le_rfl
  have hh' : m ≤ (ReductionData.ceilSqrt m.toNat : ℤ) ^ 2 := by
    have hh'' : (m.toNat : ℤ) ≤ (ReductionData.ceilSqrt m.toNat : ℤ) ^ 2 := by
      exact_mod_cast hh
    simpa only [Int.toNat_of_nonneg hm] using hh''
  have hn : 0 ≤ (ReductionData.ceilSqrt m.toNat : ℤ) := by positivity
  have h1 : sqNorm T ≤ m := le_max_left _ _
  have h2 : sqNorm g ≤ m := le_max_right _ _
  change sqNorm T < (1 + (ReductionData.ceilSqrt m.toNat : ℤ)) ^ 2 ∧
    sqNorm g < (1 + (ReductionData.ceilSqrt m.toNat : ℤ)) ^ 2
  constructor <;> nlinarith

/-- The two columns are literally `(Q,T)` and `(0,g)`. -/
theorem completionBasis_columns (Q : ℤ) (hQ : Q ≠ 0) (g T : QuotRing d) (hg : g ≠ 0) :
    (completionBasis Q hQ g T hg 0).val = ((Q : QuotRing d), T) ∧
    (completionBasis Q hQ g T hg 1).val = (0,g) := by
  constructor
  · simp only [completionBasis, Module.Basis.map_apply, LinearEquiv.trans_apply,
      LinearEquiv.finTwoArrow_apply, Pi.basisFun_apply]
    change ((Q : QuotRing d) * 1, T * 1 + g * 0) = _
    simp
  · simp only [completionBasis, Module.Basis.map_apply, LinearEquiv.trans_apply,
      LinearEquiv.finTwoArrow_apply, Pi.basisFun_apply]
    change ((Q : QuotRing d) * 0, T * 0 + g * 1) = _
    simp

end IdealCVP.ModuleSIVP

namespace IdealCVP
open IdealCVP.Cyclotomic ModuleSIVP

/-- Definition `def:module-sivp`: a free rank-two integral cyclotomic module,
an explicit basis, and a nonnegative squared threshold. -/
structure ModuleSIVPInstance where
  d : ℕ
  power_two : ∃ k, d = 2 ^ k
  module : Submodule (QuotRing d) (QuotRing d × QuotRing d)
  basis : Module.Basis (Fin 2) (QuotRing d) module
  Γ : ℤ
  Γ_nonneg : 0 ≤ Γ

def ModuleSIVPInstance.Yes (J : ModuleSIVPInstance) : Prop :=
  letI : Fact (∃ k, J.d = 2 ^ k) := ⟨J.power_two⟩
  SecondMinimumSq J.module J.Γ

def ModuleSIVPInstance.ExactMinimum (J : ModuleSIVPInstance) (r : ℤ) : Prop :=
  letI : Fact (∃ k, J.d = 2 ^ k) := ⟨J.power_two⟩
  ExactSecondMinimumSq J.module r

def ModuleSIVPInstance.LowerBound (J : ModuleSIVPInstance) (r : ℤ) : Prop :=
  letI : Fact (∃ k, J.d = 2 ^ k) := ⟨J.power_two⟩
  ∀ u ∈ J.module, ∀ v ∈ J.module, Independent u v →
    r ≤ max (vectorNormSq u) (vectorNormSq v)

/-- Complete any principal CVP instance by the paper's lower triangular basis. -/
def PrincipalCVPInstance.toModuleSIVP (I : PrincipalCVPInstance) : ModuleSIVPInstance := by
  letI : Fact (∃ k, I.d = 2 ^ k) := ⟨I.power_two⟩
  let Q := completionScale I.g I.T
  have hg : toQuot I.g ≠ 0 := by
    intro h
    exact I.g_ne_zero ((toQuot_bijective dimension_pos).injective
      (h.trans (toQuot_zero _).symm))
  exact {
    d := I.d
    power_two := I.power_two
    module := completion Q (toQuot I.g) (toQuot I.T)
    basis := completionBasis Q (ne_of_gt (completionScale_pos I.g I.T)) _ _ hg
    Γ := Q ^ 2 + I.Δ
    Γ_nonneg := add_nonneg (sq_nonneg Q) I.Δ_nonneg }

/-- General CVP-to-module completion correctness, before specializing to X3C. -/
theorem PrincipalCVPInstance.module_exact (I : PrincipalCVPInstance) {δ : ℤ}
    (hmin : MinimumSquaredDistance (principalIdealLattice I.g) I.T δ) :
    I.toModuleSIVP.ExactMinimum (completionScale I.g I.T ^ 2 + δ) := by
  letI : Fact (∃ k, I.d = 2 ^ k) := ⟨I.power_two⟩
  have hg : toQuot I.g ≠ 0 := by
    intro h
    exact I.g_ne_zero ((toQuot_bijective dimension_pos).injective
      (h.trans (toQuot_zero _).symm))
  apply module_completion _ (completionScale_pos I.g I.T) _ _ hg
  · rw [normSq_toQuot]; exact (completionScale_bounds I.g I.T).1
  · rw [normSq_toQuot]; exact (completionScale_bounds I.g I.T).2
  · exact minimumDistance_of_coeff hmin

/-- The explicit X3C-to-module-SIVP instance of `thm:module-sivp`. -/
def x3cToModuleSIVP (I : X3CInstance) : ModuleSIVPInstance := (x3cToCVP I).toModuleSIVP

/-- YES instances attain exactly `Γ = Q² + Δ`. -/
theorem x3c_module_sivp_yes (I : X3CInstance) (hy : I.HasExactCover) :
    (x3cToModuleSIVP I).ExactMinimum (x3cToModuleSIVP I).Γ :=
  (x3cToCVP I).module_exact (x3c_yes_gap I hy)

/-- NO instances have squared second minimum at least `Γ + 4`. -/
theorem x3c_module_sivp_no (I : X3CInstance) (hn : ¬ I.HasExactCover) :
    (x3cToModuleSIVP I).LowerBound ((x3cToModuleSIVP I).Γ + 4) := by
  let C := x3cToCVP I
  letI : Fact (∃ k, C.d = 2 ^ k) := ⟨C.power_two⟩
  obtain ⟨δ,hmin⟩ := exists_minimumDistance (toQuot C.g) (toQuot C.T)
  have hδ : C.Δ + 4 ≤ δ := by
    obtain ⟨b,hb⟩ := hmin.1
    obtain ⟨b,rfl⟩ := (toQuot_bijective dimension_pos).surjective b
    rw [normSq_residual] at hb
    rw [← hb]
    exact x3c_no_gap I hn _ ⟨b,rfl⟩
  have hQT : normSq (toQuot C.T) < completionScale C.g C.T ^ 2 := by
    rw [normSq_toQuot]; exact (completionScale_bounds C.g C.T).1
  intro u hu v hv hi
  have hl := pair_lower_bound (completionScale C.g C.T) (toQuot C.g) (toQuot C.T)
    hQT hmin u hu v hv hi
  change completionScale C.g C.T ^ 2 + C.Δ + 4 ≤ _
  omega

/-- Mathematical reduction correctness; no complexity-class assertion. -/
theorem x3c_module_sivp_correct (I : X3CInstance) :
    I.HasExactCover ↔ (x3cToModuleSIVP I).Yes := by
  letI : Fact (∃ k, (x3cToModuleSIVP I).d = 2 ^ k) := ⟨(x3cToModuleSIVP I).power_two⟩
  constructor
  · intro hy
    exact (secondMinimumSq_iff (x3c_module_sivp_yes I hy)).mpr le_rfl
  · intro hy
    by_contra hn
    obtain ⟨u,hu,v,hv,hi,hn1,hn2⟩ := hy
    have hl := x3c_module_sivp_no I hn u hu v hv hi
    have hh := max_le hn1 hn2
    omega

end IdealCVP
