import Rank2ModuleSVP.ReductionAux

/-! The integral rank-two reduction of paper v2, Sections 4.3 and 5. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Rank2ModuleSVP
noncomputable section
open scoped BigOperators
open Checker Polynomial
variable {q : ℕ} [NeZero q]

private theorem red_intCast_inj {a b : ℤ}
    (ha : -(q : ℤ) < 2*a) (ha' : 2*a < q)
    (hb : -(q : ℤ) < 2*b) (hb' : 2*b < q)
    (he : (a : ZMod q) = b) : a = b := by
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub a b q).mp he
  have hab : |b-a| < (q : ℤ) := by rw [abs_lt]; omega
  by_contra hh
  have hn : b-a ≠ 0 := by omega
  have hle : (q : ℤ) ≤ |b-a| :=
    Int.le_of_dvd (abs_pos.mpr hn) ((dvd_abs (q : ℤ) (b-a)).mpr hd)
  omega

variable (I : IdealCVP.X3CInstance) (s : IdealCVP.SidonPositions I.n)

theorem red_alphaStar_small (hoff : 4*tau I s*(3*I.q) < q) :
    2*alphaStar I s < q := by
  have hM : 1 ≤ 3*I.q := by have := I.q_pos; omega
  have hm := Nat.mul_le_mul_left (4*tau I s) hM
  simp only [mul_one] at hm
  have ht : tau I s = 2*alphaStar I s+1 := rfl
  omega

theorem red_alpha_injective (hoff : 4*tau I s*(3*I.q) < q) :
    Function.Injective (fun j => (s.α j : ZMod q)) := by
  intro j l he
  apply s.strictMono.injective
  have hs := red_alphaStar_small I s hoff
  have hj := alpha_le_alphaStar I s j
  have hl := alpha_le_alphaStar I s l
  have hjq : s.α j < q := by omega
  have hlq : s.α l < q := by omega
  have hh := congrArg ZMod.val he
  simpa only [ZMod.val_natCast_of_lt hjq, ZMod.val_natCast_of_lt hlq] using hh

theorem red_difference_injective (hoff : 4*tau I s*(3*I.q) < q)
    (j l j' l' : Fin I.n) (hjl : j ≠ l) (hj'l' : j' ≠ l')
    (he : (s.α l : ZMod q)-s.α j = (s.α l' : ZMod q)-s.α j') :
    j = j' ∧ l = l' := by
  apply s.differences j l j' l' hjl hj'l'
  have hs : 2*(alphaStar I s : ℤ) < q := by
    exact_mod_cast red_alphaStar_small I s hoff
  have hj : (s.α j : ℤ) ≤ alphaStar I s := by exact_mod_cast alpha_le_alphaStar I s j
  have hl : (s.α l : ℤ) ≤ alphaStar I s := by exact_mod_cast alpha_le_alphaStar I s l
  have hj' : (s.α j' : ℤ) ≤ alphaStar I s := by exact_mod_cast alpha_le_alphaStar I s j'
  have hl' : (s.α l' : ℤ) ≤ alphaStar I s := by exact_mod_cast alpha_le_alphaStar I s l'
  exact red_intCast_inj (q := q) (by nlinarith [Nat.cast_nonneg (α := ℤ) (s.α l)])
    (by nlinarith [Nat.cast_nonneg (α := ℤ) (s.α j)])
    (by nlinarith [Nat.cast_nonneg (α := ℤ) (s.α l')])
    (by nlinarith [Nat.cast_nonneg (α := ℤ) (s.α j')]) (by simpa using he)

def redPositions : Finset (ZMod q) := Finset.univ.image fun j => (s.α j : ZMod q)
def redOffsets : Finset (ZMod q) := D_wit I s ∪ D_bad I s

theorem redPositions_card (hoff : 4*tau I s*(3*I.q) < q) :
    (redPositions (q := q) I s).card = I.n := by
  rw [redPositions, Finset.card_image_of_injective _ (red_alpha_injective I s hoff)]
  simp

theorem redOffsets_card (hoff : 4*tau I s*(3*I.q) < q) :
    (redOffsets (q := q) I s).card ≤ 100*(redPositions (q := q) I s).card^2+100 := by
  have hb := bad_card_bound (q := q) I s
  have hw : (D_wit (q := q) I s).card ≤ I.n^2 := by
    apply Finset.card_image_le.trans
    exact (Finset.card_filter_le _ _).trans_eq (by simp [pow_two])
  have hu := Finset.card_union_le (D_wit (q := q) I s) (D_bad I s)
  rw [redPositions_card I s hoff]
  dsimp [redOffsets]
  rw [incidence_count] at hb
  nlinarith

theorem redOffsets_nonzero (hoff : 4*tau I s*(3*I.q) < q) :
    (0 : ZMod q) ∉ redOffsets I s := by
  classical
  intro hz
  rcases Finset.mem_union.mp hz with hw | hb
  · obtain ⟨⟨j,l⟩, hjl, he⟩ := Finset.mem_image.mp hw
    have hn : j ≠ l := (Finset.mem_filter.mp hjl).2
    exact hn ((red_alpha_injective I s hoff) (sub_eq_zero.mp he).symm)
  · exact (row_shift_bad_separation I s hoff).1 hb

/-- Theorem 4.4 specialized to the actual checker positions and offsets. -/
theorem red_admissible_representative (hWan : WanPowerSumEstimates)
    [Fact q.Prime] {k : ℕ} (hk : redK0 ≤ k) (hpow : (2*k)^redC0 ≤ q)
    (hn : I.n+2 ≤ Nat.sqrt k) (hoff : 4*tau I s*(3*I.q) < q)
    (u : Fin k → ZMod q)
    (hu : u ⟨0, by have hk0 : 100000000 ≤ k := (le_max_left _ _).trans hk; omega⟩ =
      (cntH k : ZMod q))
    (ξ : Fin I.n → ℤ) (hξ : ∀ j, ξ j = 0 ∨ ξ j = 1) :
    ∃ x : Coeff ℤ q, IsBinary x ∧ syndrome k x = u ∧
      (∑ a, x a) = (cntH k : ℤ) ∧
      (∀ j, x (s.α j) = ξ j) ∧ Clean I s (fun a => (x a : ℚ)) := by
  classical
  let P := redPositions (q := q) I s
  let D := redOffsets (q := q) I s
  let η : Coeff ℤ q := fun a => if ha : ∃ j, (s.α j : ZMod q) = a then ξ ha.choose else 0
  have hηj (j : Fin I.n) : η (s.α j) = ξ j := by
    have hj : ∃ l, (s.α l : ZMod q) = s.α j := ⟨j, rfl⟩
    simp only [η, dite_eq_left hj]
    congr 1
    exact (red_alpha_injective I s hoff) hj.choose_spec
  have hη : ∀ a ∈ P, η a = 0 ∨ η a = 1 := by
    intro a ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    rw [hηj]
    exact hξ j
  let forbidden : ZMod q → ZMod q → Prop := fun a b =>
    (b-a ∈ D_bad I s) ∨
      (∃ j l : Fin I.n, j ≠ l ∧ b-a = (s.α l : ZMod q)-s.α j ∧ a ≠ s.α j)
  have hforb : ∀ a b, forbidden a b → b-a ∈ D ∧ (a ∉ P ∨ b ∉ P) := by
    intro a b hab
    have hd : b-a ∈ D := by
      rcases hab with hb | ⟨j,l,hjl,he,ha⟩
      · exact Finset.mem_union_right _ hb
      · apply Finset.mem_union_left
        rw [he]
        exact Finset.mem_image.mpr ⟨(j,l), by simp [hjl], rfl⟩
    refine ⟨hd, ?_⟩
    by_contra hbad
    push Not at hbad
    obtain ⟨j', _, hj'⟩ := Finset.mem_image.mp hbad.1
    obtain ⟨l', _, hl'⟩ := Finset.mem_image.mp hbad.2
    have hne : j' ≠ l' := by
      intro he
      have : b-a = 0 := by rw [← hj', ← hl', he, sub_self]
      exact redOffsets_nonzero I s hoff (this ▸ hd)
    rcases hab with hb | ⟨j,l,hjl,he,ha⟩
    · have hw : b-a ∈ D_wit I s := Finset.mem_image.mpr
        ⟨(j',l'), by simp [hne], by simp [hj', hl']⟩
      exact Finset.disjoint_left.mp (row_shift_bad_separation I s hoff).2 hb hw
    · have he' : (s.α l' : ZMod q)-s.α j' = (s.α l : ZMod q)-s.α j := by
        simpa [hj', hl'] using he
      have hh := red_difference_injective I s hoff j' l' j l hne hjl he'
      exact ha (hj'.symm.trans (congrArg (fun j => (s.α j : ZMod q)) hh.1))
  obtain ⟨hcnt, hsep, hcntq, hkq⟩ := red_regime hk hpow
  obtain ⟨x, hx, hz⟩ := admissible_representative hWan (Fact.out : q.Prime) hcnt hcntq
    u P D η (by dsimp [P]; rw [redPositions_card I s hoff]; exact hn)
    (redOffsets_card I s hoff) (redOffsets_nonzero I s hoff) hη hu forbidden hforb
  obtain ⟨hb, hs, hh, hp⟩ := (mem_completions _ _ _ _ _ _).mp hx
  refine ⟨x, hb, hs, hh, ?_, ?_, ?_⟩
  · intro j
    exact (hp _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)).trans (hηj j)
  · intro j l hjl
    unfold correlation
    rw [Finset.sum_eq_single (s.α j : ZMod q)]
    · congr 2
      congr 1
      abel
    · intro a _ ha
      have hh := hz a (a+((s.α l : ZMod q)-s.α j))
        (Or.inr ⟨j,l,hjl,by abel,ha⟩)
      simpa only [Int.cast_mul, Int.cast_zero] using congrArg (fun z : ℤ => (z : ℚ)) hh
    · simp
  · intro d hd
    unfold correlation
    apply Finset.sum_eq_zero
    intro a _
    have hh := hz a (a+d) (Or.inl (by simpa using hd))
    simpa only [Int.cast_mul, Int.cast_zero] using congrArg (fun z : ℤ => (z : ℚ)) hh

/-- Corollary 4.5: the prescribed clean representative lies in the centre coset. -/
theorem red_coset_representative (hWan : WanPowerSumEstimates)
    [Fact q.Prime] {k : ℕ} (hk : redK0 ≤ k) (hpow : (2*k)^redC0 ≤ q)
    (hn : I.n+2 ≤ Nat.sqrt k) (hoff : 4*tau I s*(3*I.q) < q)
    (ξ : Fin I.n → ℤ) (hξ : ∀ j, ξ j = 0 ∨ ξ j = 1) :
    ∃ x : Coeff ℤ q, IsBinary x ∧ (∑ a, x a) = (cntH k : ℤ) ∧
      classOf x-sepCenter k ∈ ramifiedIdeal k ∧
      (∀ j, x (s.α j) = ξ j) ∧ Clean I s (fun a => (x a : ℚ)) := by
  obtain ⟨hcnt, hsep, hcntq, hkq⟩ := red_regime hk hpow
  have hk0 : 100000000 ≤ k := hcnt
  let c := robustCenterCoeffs (q := q) k (sepWeight k)
  obtain ⟨hc, hsum⟩ := sepCenter_representative (q := q) k hsep hkq
  obtain ⟨x, hb, hs, hh, hx, hclean⟩ := red_admissible_representative I s hWan hk hpow hn hoff
    (syndrome k c) (by simpa [syndrome, c, ← Int.cast_sum, cntH_eq_sepWeight] using
      (congrArg (fun z : ℤ => (z : ZMod q)) hsum)) ξ hξ
  refine ⟨x, hb, hh, ?_, hx, hclean⟩
  rw [← hc]
  apply (ramified_coset_syndrome k (by omega) (by omega) c (classOf x)).mpr
  refine ⟨x, ⟨rfl, hs, ?_⟩, ?_⟩
  · simpa only [cntH_eq_sepWeight] using hh.trans hsum.symm
  · intro z hz
    exact classOf_injective_fixed_sum hz.1 (hz.2.2.trans (by
      simpa only [cntH_eq_sepWeight] using hsum.trans hh.symm))

/-- Equation (21), with an integral representative and the integral checker. -/
theorem red_checker_bounds (x : Coeff ℤ q) (h : ℕ) (hx : IsBinary x)
    (hh : ∑ a, x a = (h : ℤ)) (hhpos : 1 ≤ h)
    (hc : Clean I s (fun a => (x a : ℚ))) :
    let T := B₀ (q := q) I h+2*kappa (q := q) I h*
      (∑ i, (rowValue I s (fun a => (x a : ℚ)) i-1)^2)
    T ≤ ((normSq (U I s h*classOf x-V I s) : ℤ) : ℚ)/(Q I h : ℚ)^2 ∧
      ((normSq (U I s h*classOf x-V I s) : ℤ) : ℚ)/(Q I h : ℚ)^2 ≤ T+kappa (q := q) I h/8 := by
  dsimp only
  rw [checker_score_int I s x h hx hh hhpos, E_eq_zero_of_clean I s _ hc]
  have hR := remainder_nonneg I s h (fun a => (x a : ℚ))
  have hx' : ∀ a, (x a : ℚ) = 0 ∨ (x a : ℚ) = 1 := by
    intro a
    rcases hx a with ha | ha <;> simp [ha]
  have hh' : ∑ a, (x a : ℚ) = (h : ℚ) := by exact_mod_cast hh
  have hR' := remainder_lt I s _ h hx' hh' hhpos
  constructor <;> linarith

/-- Row values are ordinary incidence sums; no cyclotomic fact is used here. -/
theorem red_rowValue (x : Coeff ℚ q) (i : Fin (3*I.q)) :
    rowValue I s x i = ∑ j : Fin I.n, if i ∈ I.triples j then x (s.α j) else 0 := by
  classical
  simp only [rowValue, Incidence, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : i ∈ I.triples j
  · rw [Finset.sum_eq_single ⟨i,hi⟩]
    · simp [hi]
    · intro b _ hb
      have hbi : b.val ≠ i := by intro h; exact hb (Subtype.ext h)
      simp [hbi]
    · simp
  · simp only [hi, ite_false]
    apply Finset.sum_eq_zero
    intro b _
    have hbi : b.val ≠ i := by intro h; exact hi (h ▸ b.property)
    simp [hbi]

theorem red_rowValue_indicator (C : Finset (Fin I.n)) (x : Coeff ℤ q)
    (hx : ∀ j, x (s.α j) = if j ∈ C then 1 else 0) (i : Fin (3*I.q)) :
    rowValue I s (fun a => (x a : ℚ)) i = ((C.filter fun j => i ∈ I.triples j).card : ℚ) := by
  classical
  rw [red_rowValue]
  simp_rw [hx]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero]
  simp_rw [← ite_and]
  simp only [Finset.sum_boole, Finset.filter_and]
  congr 2
  ext j
  simp [and_comm]

theorem red_no_cover_error (hno : ¬ I.HasExactCover) (x : Coeff ℤ q) (hx : IsBinary x) :
    (1 : ℚ) ≤ ∑ i, (rowValue I s (fun a => (x a : ℚ)) i-1)^2 := by
  classical
  let C := Finset.univ.filter fun j : Fin I.n => x (s.α j) = 1
  have hxi : ∀ j, x (s.α j) = if j ∈ C then 1 else 0 := by
    intro j
    rcases hx (s.α j) with hz | ho
    · simp [C, hz]
    · simp [C, ho]
  have hnot : ¬ I.IsExactCover C := fun hc => hno ⟨C,hc⟩
  obtain ⟨i, hi⟩ : ∃ i, (C.filter fun j => i ∈ I.triples j).card ≠ 1 := by
    simpa [IdealCVP.X3CInstance.IsExactCover] using hnot
  have hsq : (1 : ℚ) ≤ (rowValue I s (fun a => (x a : ℚ)) i-1)^2 := by
    rw [red_rowValue_indicator I s C x hxi]
    have hz : (1 : ℤ) ≤ (((C.filter fun j => i ∈ I.triples j).card : ℤ)-1)^2 := by
      have hne : ((C.filter fun j => i ∈ I.triples j).card : ℤ) ≠ 1 := by exact_mod_cast hi
      have hh : ((C.filter fun j => i ∈ I.triples j).card : ℤ) ≤ 0 ∨
          2 ≤ ((C.filter fun j => i ∈ I.triples j).card : ℤ) := by omega
      rcases hh with hh | hh <;> nlinarith
    exact_mod_cast hz
  exact hsq.trans (Finset.single_le_sum (fun j _ => sq_nonneg (rowValue I s (fun a => (x a : ℚ)) j-1)) (Finset.mem_univ i))

theorem red_pi_pow_ne_zero [Fact q.Prime] (k : ℕ) (hkq : k < q-1) :
    (pi : IntegerRing q)^k ≠ 0 := by
  intro hz
  let P : ℤ[X] := (Polynomial.X-1)^k
  have hP : P ≠ 0 := pow_ne_zero k (Polynomial.X_sub_C_ne_zero (1 : ℤ))
  have he : cyclotomicEval (q := q) P = 0 := by
    simp only [P, map_pow, map_sub, cyclotomicEval_X, map_one]
    rw [show (monomial (1 : ZMod q) : IntegerRing q)-1 = -pi by simp [pi], neg_pow (pi : IntegerRing q) k, hz, mul_zero]
  have hd := Polynomial.natDegree_le_of_dvd ((cyclotomicEval_eq_zero_iff P).mp he) hP
  have hdeg : P.natDegree = k := by
    change ((Polynomial.X-Polynomial.C (1 : ℤ))^k).natDegree = k
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  rw [hdeg, Polynomial.natDegree_cyclotomic, Nat.totient_prime (Fact.out : q.Prime)] at hd
  omega

theorem red_scalar_ne_zero (a : ℕ) (ha : 0 < a) (v : IntegerRing q) (hv : v ≠ 0) :
    (a : IntegerRing q)*v ≠ 0 := by
  intro hz
  have he := congrArg normSq hz
  rw [red_normSq_nat_mul, normSq_zero] at he
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hv' : 0 < normSq v := lt_of_le_of_ne (normSq_nonneg v)
    (Ne.symm ((normSq_eq_zero_iff v).not.mpr hv))
  nlinarith

theorem redDet_ne_zero [Fact q.Prime] {k : ℕ}
    (hk : redK0 ≤ k) (hpow : (2*k)^redC0 ≤ q) :
    determinant (redM1 (q := q) I s k) (redM2 I s k) ≠ 0 := by
  obtain ⟨hcnt,hsep,hcntq,hkq⟩ := red_regime hk hpow
  have hk0 : 100000000 ≤ k := hcnt
  have hp := red_pi_pow_ne_zero (q := q) k (by omega)
  have hQ := redQ_pos I hk
  have hg : 0 < redGamma k := by have := (redGamma_bounds hk).1; omega
  have hu : U I s (cntH k)*(pi : IntegerRing q)^k ≠ 0 := by
    intro hz
    have hh := checker_U_norm_lower_int I s (cntH k) ((pi : IntegerRing q)^k)
    rw [hz, normSq_zero] at hh
    have hn : 0 < normSq ((pi : IntegerRing q)^k) :=
      lt_of_le_of_ne (normSq_nonneg _) (Ne.symm ((normSq_eq_zero_iff _).not.mpr hp))
    have hQ' : (0 : ℤ) < Q I (cntH k) := by exact_mod_cast hQ
    nlinarith
  have he : determinant (redM1 (q := q) I s k) (redM2 I s k) =
      -(((Q I (cntH k)*redGamma k : ℕ) : IntegerRing q)*(U I s (cntH k)*(pi : IntegerRing q)^k)) := by
    simp [determinant, redM1, redM2]
    ring
  rw [he, neg_ne_zero]
  exact red_scalar_ne_zero (q := q) _ (Nat.mul_pos hQ hg) _ hu

/-- Completeness, including the strict inequality in Theorem 5.2. -/
theorem red_completeness (hWan : WanPowerSumEstimates) [Fact q.Prime]
    {k : ℕ} (hk : redK0 ≤ k) (hpow : (2*k)^redC0 ≤ q)
    (hn : I.n+2 ≤ Nat.sqrt k) (hoff : 4*tau I s*(3*I.q) < q)
    (hyes : I.HasExactCover) :
    ∃ z w : IntegerRing q, moduleVector (redM1 I s k) (redM2 I s k) z w ≠ 0 ∧
      pairNormSq (moduleVector (redM1 I s k) (redM2 I s k) z w) < redS (q := q) I k := by
  classical
  obtain ⟨C,hC⟩ := hyes
  let ξ : Fin I.n → ℤ := fun j => if j ∈ C then 1 else 0
  have hξ : ∀ j, ξ j = 0 ∨ ξ j = 1 := by intro j; simp only [ξ]; split_ifs <;> simp
  obtain ⟨x,hb,hh,hcos,hfix,hclean⟩ := red_coset_representative I s hWan hk hpow hn hoff ξ hξ
  obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hcos
  have hy : z*(pi : IntegerRing q)^k+1*sepCenter k = classOf x := by rw [mul_comm z, ← hz]; ring
  have hk0 : 100000000 ≤ k := (le_max_left _ _).trans hk
  have hhpos : 1 ≤ cntH k := by have := (cntH_bounds k).1; omega
  have hQ := redQ_pos I hk
  have hQ' : (0 : ℚ) < Q I (cntH k) := by exact_mod_cast hQ
  have hκ := (red_kappa_bounds (q := q) I hk).1
  have hg : 0 < redGamma k := by have := (redGamma_bounds hk).1; omega
  have hone : (1 : IntegerRing q) ≠ 0 := by
    have hq2 := (Fact.out : q.Prime).two_le
    intro he
    have he' := congrArg normSq he
    rw [red_normSq_one, normSq_zero] at he'
    omega
  have hvne : moduleVector (redM1 I s k) (redM2 I s k) z 1 ≠ 0 := by
    intro he
    have h2 := congrArg Prod.snd he
    rw [red_moduleVector] at h2
    simp only [Prod.snd_zero, Prod.snd, mul_one, neg_eq_zero] at h2
    exact red_scalar_ne_zero (q := q) _ (Nat.mul_pos hQ hg) 1 hone (by simpa using h2)
  refine ⟨z,1,hvne,?_⟩
  have hrows : ∀ i, rowValue I s (fun a => (x a : ℚ)) i = 1 := by
    intro i
    rw [red_rowValue_indicator I s C x hfix, hC i]
    norm_num
  have hbnd := (red_checker_bounds I s x (cntH k) hb hh hhpos hclean).2
  simp only [hrows, sub_self, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero,
    mul_zero, add_zero] at hbnd
  have hbnd' := (div_le_iff₀ (sq_pos_of_pos hQ')).mp hbnd
  have hn : ((pairNormSq (moduleVector (redM1 I s k) (redM2 I s k) z 1) : ℤ) : ℚ) =
      ((normSq (U I s (cntH k)*classOf x-V I s) : ℤ) : ℚ)+
        (Q I (cntH k) : ℚ)^2*(redF k q : ℚ) := by
    rw [red_moduleVector_norm, hy, mul_one, red_normSq_one]
    simp only [redF, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub,
      Int.cast_natCast, Int.cast_one]
    ring
  have hS := redS_eq (q := q) I hk
  have hlt : ((pairNormSq (moduleVector (redM1 I s k) (redM2 I s k) z 1) : ℤ) : ℚ) < redS (q := q) I k := by
    rw [hn, hS]
    nlinarith [mul_pos (sq_pos_of_pos hQ') hκ]
  exact_mod_cast hlt

/-- Squared norm of (22), expressed in integral scalar arithmetic. -/
def redCost (k : ℕ) (y w : IntegerRing q) : ℤ :=
  normSq (U I s (cntH k)*y-V I s*w)+
    (Q I (cntH k) : ℤ)^2*(redGamma k : ℤ)^2*normSq w

theorem red_signed_isometry {w : IntegerRing q} (hw : IsSignedMonomial w)
    (y : IntegerRing q) : normSq (w*y) = normSq y := by
  obtain ⟨j, rfl | rfl⟩ := hw
  · exact normSq_monomial_mul j y
  · exact normSq_neg_monomial_mul j y

theorem red_signed_inverse {w : IntegerRing q} (hw : IsSignedMonomial w) :
    ∃ t : IntegerRing q, IsSignedMonomial t ∧ t*w = 1 := by
  obtain ⟨j, rfl | rfl⟩ := hw
  · refine ⟨monomial (-j), ⟨-j, Or.inl rfl⟩, ?_⟩
    rw [← monomial_add, neg_add_cancel, monomial_zero]
  · refine ⟨-monomial (-j), ⟨-j, Or.inr rfl⟩, ?_⟩
    have he : (-monomial (-j) : IntegerRing q)*(-monomial j) = monomial (-j)*monomial j := by ring
    rw [he, ← monomial_add, neg_add_cancel, monomial_zero]

theorem red_root_normalization {k : ℕ} (y w : IntegerRing q)
    (hw : IsSignedMonomial w) (hcos : y-w*sepCenter k ∈ ramifiedIdeal k) :
    ∃ u : IntegerRing q, u-sepCenter k ∈ ramifiedIdeal k ∧
      redCost I s k y w = normSq (U I s (cntH k)*u-V I s)+
        (Q I (cntH k) : ℤ)^2*redF k q := by
  obtain ⟨t,ht,htw⟩ := red_signed_inverse hw
  refine ⟨t*y, ?_, ?_⟩
  · have h := (ramifiedIdeal k).mul_mem_left t hcos
    have he : t*(y-w*sepCenter k) = t*y-sepCenter k := by
      calc
        _ = t*y-(t*w)*sepCenter k := by ring
        _ = _ := by rw [htw, one_mul]
    rwa [he] at h
  · have he : t*(U I s (cntH k)*y-V I s*w) = U I s (cntH k)*(t*y)-V I s := by
      calc
        _ = U I s (cntH k)*(t*y)-V I s*(t*w) := by ring
        _ = _ := by rw [htw, mul_one]
    have hn := red_signed_isometry ht (U I s (cntH k)*y-V I s*w)
    rw [he] at hn
    unfold redCost redF
    rw [← hn, normSq_signedMonomial hw]
    ring

theorem red_soundness_cost [Fact q.Prime] {k : ℕ}
    (hk : redK0 ≤ k) (hpow : (2*k)^redC0 ≤ q) (hno : ¬ I.HasExactCover)
    (y w : IntegerRing q) (hcos : y-w*sepCenter k ∈ ramifiedIdeal k)
    (hne : y ≠ 0 ∨ w ≠ 0) : redS (q := q) I k < redCost I s k y w := by
  classical
  obtain ⟨hcnt,hsep,hcntq,hkq⟩ := red_regime hk hpow
  have hk0 : 100000000 ≤ k := hcnt
  have hhpos : 1 ≤ cntH k := by have := (cntH_bounds k).1; omega
  have hQ : (0 : ℚ) < Q I (cntH k) := by exact_mod_cast redQ_pos I hk
  have hQ2 : (0 : ℚ) < (Q I (cntH k) : ℚ)^2 := sq_pos_of_pos hQ
  have hν := redNu_bounds I hk
  have hνp : (0 : ℚ) < 1-redNu I k := by linarith [hν.2.2]
  have hκ := (red_kappa_bounds (q := q) I hk).1
  have hSq := redS_eq (q := q) I hk
  have hcost : ((redCost I s k y w : ℤ) : ℚ) =
      ((normSq (U I s (cntH k)*y-V I s*w) : ℤ) : ℚ)+
        (Q I (cntH k) : ℚ)^2*(redGamma k : ℚ)^2*((normSq w : ℤ) : ℚ) := by
    simp only [redCost, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  suffices (redS (q := q) I k : ℚ) < (redCost I s k y w : ℚ) by exact_mod_cast this
  by_cases hw0 : w = 0
  · have hy0 : y ≠ 0 := hne.resolve_right (not_not.mpr hw0)
    have hyI : y ∈ ramifiedIdeal k := by simpa only [hw0, zero_mul, sub_zero] using hcos
    have hy := ramifiedIdeal_minimum k (by omega) hkq y hyI hy0
    have hU := checker_U_norm_lower_int I s (cntH k) y
    have hy' : (2 : ℚ)*k*q ≤ ((normSq y : ℤ) : ℚ) := by exact_mod_cast hy
    have hU' : (Q I (cntH k) : ℚ)^2*((normSq y : ℤ) : ℚ) ≤
        ((normSq (U I s (cntH k)*y) : ℤ) : ℚ) := by exact_mod_cast hU
    have hm := mul_le_mul_of_nonneg_left hy' hQ2.le
    have hu := red_threshold_upper (q := q) I hk
    have hL : 49*(k : ℚ)*q/25 < 2*(k : ℚ)*q := by
      have : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
      have : (0 : ℚ) < q := by exact_mod_cast NeZero.pos q
      nlinarith
    have hs := mul_lt_mul_of_pos_left (hu.trans hL) hQ2
    rw [hSq, hcost, hw0]
    simp only [mul_zero, sub_zero, normSq_zero, Int.cast_zero, add_zero]
    nlinarith
  by_cases hroot : IsSignedMonomial w
  · obtain ⟨u,huI,huval⟩ := red_root_normalization I s y w hroot hcos
    let c := robustCenterCoeffs (q := q) k (sepWeight k)
    obtain ⟨hc,hcsum⟩ := sepCenter_representative (q := q) k hsep hkq
    obtain ⟨x,⟨hxu,hxs,hxsum⟩,_⟩ :=
      (ramified_coset_syndrome k (by omega) (by omega) c u).mp (by change u-classOf (robustCenterCoeffs k (sepWeight k)) ∈ ramifiedIdeal k; rw [hc]; exact huI)
    have hxh : ∑ a, x a = (cntH k : ℤ) := by simpa only [cntH_eq_sepWeight] using hxsum.trans hcsum
    by_cases hxb : IsBinary x
    · have hxQ : ∀ a, (x a : ℚ) = 0 ∨ (x a : ℚ) = 1 := by
        intro a
        rcases hxb a with h | h <;> simp [h]
      have hhQ : ∑ a, (x a : ℚ) = (cntH k : ℚ) := by exact_mod_cast hxh
      have hcheck := checker_lower I s (fun a => (x a : ℚ)) (cntH k) hxQ hhQ hhpos
      rw [← rationalize_classOf] at hcheck
      change _ ≤ normSq (rationalize (U I s (cntH k))*rationalize (classOf x)-rationalize (V I s)) / _ at hcheck
      rw [← map_mul, ← map_sub, normSq_rationalize, hxu] at hcheck
      have herr := red_no_cover_error I s hno x hxb
      have hc' := (le_div_iff₀ hQ2).mp hcheck
      have herr' := mul_le_mul_of_nonneg_left herr (show (0 : ℚ) ≤ 2*kappa (q := q) I (cntH k) by positivity)
      have hcc : B₀ (q := q) I (cntH k)+2*kappa (q := q) I (cntH k) ≤
          B₀ (q := q) I (cntH k)+2*kappa (q := q) I (cntH k)*
            (∑ i, (rowValue I s (fun a => (x a : ℚ)) i-1)^2) := by linarith
      have hc'' := mul_le_mul_of_nonneg_right hcc hQ2.le
      rw [huval]
      push_cast
      rw [hSq]
      nlinarith [mul_pos hQ2 hκ]
    · have hshell := binary_shell x (cntH k) hxh hxb
      rw [hxu] at hshell
      have hshell' : (cntH k : ℚ)*(q-cntH k)+2*q ≤ ((normSq u : ℤ) : ℚ) := by exact_mod_cast hshell
      have hstab := red_global_stability_int I s hk u 1
      rw [red_normSq_one] at hstab
      simp only [mul_one, Int.cast_sub, Int.cast_natCast, Int.cast_one] at hstab
      have hF : (redGamma k : ℚ)^2*((q : ℚ)-1) = (redF k q : ℚ) := by simp [redF]
      simp only [mul_assoc] at hstab
      rw [hF] at hstab
      have hmargin := red_nonbinary_margin (q := q) I hk
      have hm := mul_lt_mul_of_pos_left hmargin hQ2
      have hlo := mul_le_mul_of_nonneg_left hshell' (mul_pos hQ2 hνp).le
      rw [hSq, huval]
      push_cast
      nlinarith
  by_cases hwsmall : normSq w ≤ 3*q
  · have hy := robust_center k (sepWeight k) hsep hkq w y hw0 hwsmall hcos
    have hy' : (k : ℚ)*q/5 < ((normSq y : ℤ) : ℚ) := by
      have h : (2 : ℚ)*k*q < 10*((normSq y : ℤ) : ℚ) := by exact_mod_cast hy
      linarith
    have hw := (second_shell w hw0).resolve_left hroot
    have hw' : (2 : ℚ)*q-4 ≤ ((normSq w : ℤ) : ℚ) := by exact_mod_cast hw
    have hg : (0 : ℚ) ≤ (redGamma k : ℚ)^2 := sq_nonneg _
    have hlo : (k : ℚ)*q/5+(redGamma k : ℚ)^2*(2*q-4) ≤
        ((normSq y : ℤ) : ℚ)+(redGamma k : ℚ)^2*((normSq w : ℤ) : ℚ) := by
      nlinarith [mul_le_mul_of_nonneg_left hw' hg]
    have hm := mul_le_mul_of_nonneg_left hlo (mul_pos hQ2 hνp).le
    have hstab := red_global_stability_int I s hk y w
    have hmargin := mul_lt_mul_of_pos_left (red_small_multiplier_margin I hk hpow) hQ2
    rw [hSq, hcost]
    linarith
  · have hw : 3*q < normSq w := lt_of_not_ge hwsmall
    have hw' : (3 : ℚ)*q < ((normSq w : ℤ) : ℚ) := by exact_mod_cast hw
    have hn : (0 : ℚ) ≤ ((normSq (U I s (cntH k)*y-V I s*w) : ℤ) : ℚ) := by exact_mod_cast normSq_nonneg (U I s (cntH k)*y-V I s*w)
    have hg : (0 : ℚ) < (redGamma k : ℚ)^2 := by
      have : (0 : ℚ) < redGamma k := by have h := (redGamma_bounds hk).1; exact_mod_cast (show 0 < redGamma k by omega)
      exact sq_pos_of_pos this
    have hm := mul_lt_mul_of_pos_left hw' (mul_pos hQ2 hg)
    have hmargin := mul_lt_mul_of_pos_left (red_large_multiplier_margin I hk hpow) hQ2
    have hF : (redF k q : ℚ) = (redGamma k : ℚ)^2*((q : ℚ)-1) := by simp [redF]
    rw [hF] at hmargin
    rw [hSq, hcost]
    nlinarith

/-- Soundness, with a strict lower bound for every nonzero module vector. -/
theorem red_soundness [Fact q.Prime] {k : ℕ}
    (hk : redK0 ≤ k) (hpow : (2*k)^redC0 ≤ q) (hno : ¬ I.HasExactCover)
    (z w : IntegerRing q)
    (hne : moduleVector (redM1 I s k) (redM2 I s k) z w ≠ 0) :
    redS (q := q) I k < pairNormSq (moduleVector (redM1 I s k) (redM2 I s k) z w) := by
  let y := z*(pi : IntegerRing q)^k+w*sepCenter k
  have hcos : y-w*sepCenter k ∈ ramifiedIdeal k := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨z, ?_⟩
    dsimp [y]
    ring
  have hyw : y ≠ 0 ∨ w ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    rw [red_moduleVector]
    change (U I s (cntH k)*y-V I s*w,_) = 0
    simp [h.1,h.2]
  have h := red_soundness_cost I s hk hpow hno y w hcos hyw
  simpa only [red_moduleVector_norm, redCost, y] using h

/-- Paper v2 Theorem 5.2: the integral rank-two module exactly encodes X3C. -/
theorem exact_X3C_encoding (hWan : WanPowerSumEstimates) [Fact q.Prime]
    {k : ℕ} (hk : redK0 ≤ k) (hpow : (2*k)^redC0 ≤ q)
    (hn : I.n+2 ≤ Nat.sqrt k) (hoff : 4*tau I s*(3*I.q) < q) :
    I.HasExactCover ↔ SVPYes (redM1 (q := q) I s k) (redM2 I s k) (redS (q := q) I k) := by
  constructor
  · intro hyes
    obtain ⟨z,w,hne,hlt⟩ := red_completeness I s hWan hk hpow hn hoff hyes
    exact ⟨z,w,hne,hlt.le⟩
  · intro hv
    by_contra hno
    obtain ⟨z,w,hne,hbound⟩ := hv
    exact (red_soundness I s hk hpow hno z w hne).not_ge hbound

/-- Corollary 4.5, bundling the coset, prescribed bits, admissibility, and (21). -/
theorem red_corollary_4_5 (hWan : WanPowerSumEstimates) [Fact q.Prime]
    {k : ℕ} (hk : redK0 ≤ k) (hpow : (2*k)^redC0 ≤ q)
    (hn : I.n+2 ≤ Nat.sqrt k) (hoff : 4*tau I s*(3*I.q) < q)
    (ξ : Fin I.n → ℤ) (hξ : ∀ j, ξ j = 0 ∨ ξ j = 1) :
    ∃ x : Coeff ℤ q, IsBinary x ∧ (∑ a, x a) = (cntH k : ℤ) ∧
      classOf x-sepCenter k ∈ ramifiedIdeal k ∧ (∀ j, x (s.α j) = ξ j) ∧
      Clean I s (fun a => (x a : ℚ)) ∧
      (let T := B₀ (q := q) I (cntH k)+2*kappa (q := q) I (cntH k)*
        (∑ i, (rowValue I s (fun a => (x a : ℚ)) i-1)^2)
       T ≤ ((normSq (U I s (cntH k)*classOf x-V I s) : ℤ) : ℚ)/(Q I (cntH k) : ℚ)^2 ∧
       ((normSq (U I s (cntH k)*classOf x-V I s) : ℤ) : ℚ)/(Q I (cntH k) : ℚ)^2 ≤
         T+kappa (q := q) I (cntH k)/8) := by
  obtain ⟨x,hb,hh,hcos,hfix,hclean⟩ := red_coset_representative I s hWan hk hpow hn hoff ξ hξ
  have hk0 : 100000000 ≤ k := (le_max_left _ _).trans hk
  have hhpos : 1 ≤ cntH k := by have := (cntH_bounds k).1; omega
  exact ⟨x,hb,hh,hcos,hfix,hclean,red_checker_bounds I s x (cntH k) hb hh hhpos hclean⟩

/-- Completeness also gives a positive threshold whenever an exact cover exists. -/
theorem redS_pos_of_cover (hWan : WanPowerSumEstimates) [Fact q.Prime]
    {k : ℕ} (hk : redK0 ≤ k) (hpow : (2*k)^redC0 ≤ q)
    (hn : I.n+2 ≤ Nat.sqrt k) (hoff : 4*tau I s*(3*I.q) < q)
    (hyes : I.HasExactCover) : 0 < redS (q := q) I k := by
  obtain ⟨z,w,hne,hlt⟩ := red_completeness I s hWan hk hpow hn hoff hyes
  have hnorm : 0 ≤ pairNormSq (moduleVector (redM1 I s k) (redM2 I s k) z w) :=
    add_nonneg (normSq_nonneg _) (normSq_nonneg _)
  exact hnorm.trans_lt hlt

end
end Rank2ModuleSVP
