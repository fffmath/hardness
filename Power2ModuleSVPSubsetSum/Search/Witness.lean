import Power2ModuleSVPSubsetSum.Reduction.Correctness

/-! # Witness bijection and recovery

Paper: `paper/power2svp-subsetsum.pdf`, Corollary 4.3.

For the coefficient model of `Reduction.positiveReduce`, satisfying Boolean assignments times
signed monomials biject with nonzero module vectors of norm at most `M`. This also counts those
vectors, including when there are no satisfying assignments. The result actually allows arbitrary
natural weights, so in particular applies to the paper's positive-weight instances.

`recover` is an executable signed shift and coefficient test on supplied multipliers `(a,b)`.
Its correctness is proved for every short nonzero vector. The equivalence uses classical choice
only to package the bijection; no polynomial-time TM certificate, or algorithm recovering
multipliers from a vector by linear algebra, is asserted here.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Power2ModuleSVPSubsetSum.Search
open Power2ModuleSVP IdealCVP.Cyclotomic Reduction

/-- The paper's signed monomial set `U_n`, represented by its coefficient arrays. -/
def SignedUnits (n : ℕ) := {b : Coeff n // SignedMonomial b}

/-- Sign and exponent specify a signed monomial; `false` means positive. -/
def signedUnit (n : ℕ) (p : Fin n × Bool) : SignedUnits n :=
  ⟨if p.2 then -monomial p.1 1 else monomial p.1 1, by
    cases p.2 <;> exact ⟨p.1, by simp⟩⟩

/-- Distinct signs and exponents specify distinct coefficient arrays. -/
theorem signedUnit_bijective (n : ℕ) : Function.Bijective (signedUnit n) := by
  constructor
  · rintro ⟨i, s⟩ ⟨j, t⟩ h
    have he := congrArg Subtype.val h
    have hi := congrFun he i
    have hj : i = j := by
      by_contra hij
      cases s <;> cases t <;> simp [signedUnit, monomial, hij] at hi
    subst j
    have hs : s = t := by
      cases s <;> cases t
      · rfl
      · have hi' := congrFun he i
        norm_num [signedUnit, monomial] at hi'
      · have hi' := congrFun he i
        norm_num [signedUnit, monomial] at hi'
      · rfl
    exact Prod.ext rfl hs
  · rintro ⟨b, i, hb | hb⟩
    · exact ⟨(i, false), Subtype.ext (by simpa [signedUnit] using hb.symm)⟩
    · exact ⟨(i, true), Subtype.ext (by simpa [signedUnit] using hb.symm)⟩

/-- The `2n` signs and exponents enumerate exactly `U_n`. -/
noncomputable def signedUnitEquiv (n : ℕ) : (Fin n × Bool) ≃ SignedUnits n :=
  Equiv.ofBijective (signedUnit n) (signedUnit_bijective n)

noncomputable instance (n : ℕ) : Fintype (SignedUnits n) :=
  Fintype.ofEquiv (Fin n × Bool) (signedUnitEquiv n)

/-- There are exactly `2n` signed monomials. -/
theorem card_signedUnits (n : ℕ) : Fintype.card (SignedUnits n) = 2 * n := by
  rw [← Fintype.card_congr (signedUnitEquiv n)]
  simp [Nat.mul_comm]

/-- The adjoint is the inverse of a signed monomial. -/
theorem signed_inverse {n : ℕ} (hn : 0 < n) {b : Coeff n} (hb : SignedMonomial b) :
    mul (star b) b = coeffOne hn := by
  obtain ⟨i, rfl | rfl⟩ := hb <;>
    simp only [star_neg, star_monomial, coeff_mul_neg_left, mul_neg, neg_neg] <;>
    rw [IdealCVP.Cyclotomic.mul_comm, monomial_mul_inv]

/-- Cancellation by a signed monomial in the coefficient model. -/
theorem signed_mul_injective {n : ℕ} (hn : 0 < n) {b : Coeff n}
    (hb : SignedMonomial b) : Function.Injective (mul b) := by
  intro a a' h
  have he := congrArg (mul (star b)) h
  simpa only [← coeff_mul_assoc hn, signed_inverse hn hb, mul_coeffOne] using he

/-- The full gadget map has unique multipliers, proved directly from its two coordinates. -/
theorem gadget_multipliers_injective (w : List ℕ) (B : ℕ) :
    Function.Injective
      (fun p : Coeff (2 * halfDegree w.length) × Coeff (2 * halfDegree w.length) =>
        moduleVector (gadgetA w B) (gadgetB w B) p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ he
  dsimp only at he
  simp only [gadgetA, gadgetB, model_vector] at he
  have hM : (0 : ℤ) < (gadget w B).M := by exact_mod_cast gadget_M_pos w B
  have hz : (2 : ℤ) • a - mul (gadgetU w B) b =
      (2 : ℤ) • a' - mul (gadgetU w B) b' := by
    ext i
    have hi := congrFun (congrArg Prod.snd he) i
    change ((gadget w B).M : ℤ) * _ = ((gadget w B).M : ℤ) * _ at hi
    exact mul_left_cancel₀ (ne_of_gt hM) hi
  have hp := congrArg Prod.fst he
  rw [hz] at hp
  have hb : b = b' := Rigidity.Q_add_V_mul_injective
    (by have := two_le_halfDegree w.length; omega)
    (gadgetH w B) (gadgetV w B) (sub_right_injective hp)
  have ha : a = a' := by
    rw [hb] at hz
    ext i
    have hi := congrFun hz i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi
    omega
  exact Prod.ext ha hb

/-- Boolean solutions, with the paper's indexed assignment semantics. -/
def Satisfying (w : List ℕ) (B : ℕ) :=
  {ξ : Fin w.length → Bool //
    (∑ j : Fin w.length, (w.get j : ℤ) * (if ξ j then 1 else 0)) = (B : ℤ)}

instance (w : List ℕ) (B : ℕ) : Fintype (Satisfying w B) :=
  inferInstanceAs (Fintype {ξ : Fin w.length → Bool //
    (∑ j : Fin w.length, (w.get j : ℤ) * (if ξ j then 1 else 0)) = (B : ℤ)})

/-- Nonzero short vectors in the actual output module, rather than multiplier witnesses. -/
def ShortVectors (w : List ℕ) (B : ℕ) :=
  {v : Coeff (2 * halfDegree w.length) × Coeff (2 * halfDegree w.length) //
    v ≠ 0 ∧ (∃ a b, moduleVector (gadgetA w B) (gadgetB w B) a b = v) ∧
      pairSup v ≤ (gadget w B).M}

/-- Recover the assignment by multiplying by `b⁻¹` and testing the first `s` coefficients.
This total executable function also accepts multipliers outside the short-vector promise. -/
def recover (w : List ℕ) (a b : Coeff (2 * halfDegree w.length)) : Fin w.length → Bool :=
  fun j => decide (mul (star b) a
    ⟨j.val, lt_of_lt_of_le j.isLt (length_le_outputDegree w.length)⟩ = 1)

/-- Reading a normalized Boolean word recovers every bit. -/
theorem recover_of_normalized (w : List ℕ) (a b : Coeff (2 * halfDegree w.length))
    (ξ : Fin w.length → Bool)
    (ha : mul (star b) a = booleanWord (length_le_outputDegree w.length) ξ) :
    recover w a b = ξ := by
  funext j
  simp only [recover, ha, booleanWord, dite_eq_left j.isLt]
  cases ξ j <;> simp

/-- Recovery inverts a signed shift of every Boolean assignment. -/
theorem recover_signed_boolean (w : List ℕ) (ξ : Fin w.length → Bool)
    (b : SignedUnits (2 * halfDegree w.length)) :
    recover w (mul b.val (booleanWord (length_le_outputDegree w.length) ξ)) b.val = ξ := by
  apply recover_of_normalized
  rw [← coeff_mul_assoc (degree_dyadic w.length).pos,
    signed_inverse (degree_dyadic w.length).pos b.property,
    mul_coeffOne]

/-- Soundness with the actual normalized multiplier, rather than just equality of norms. -/
theorem short_normalized_assignment (w : List ℕ) (B : ℕ)
    (a b : Coeff (2 * halfDegree w.length))
    (hne : moduleVector (gadgetA w B) (gadgetB w B) a b ≠ 0)
    (hshort : pairSup (moduleVector (gadgetA w B) (gadgetB w B) a b) ≤
      (gadget w B).M) :
    ∃ ξ : Satisfying w B,
      mul (star b) a = booleanWord (length_le_outputDegree w.length) ξ.val := by
  have hd := (degree_dyadic w.length).pos
  have hb := short_second_monomial w B a b hne hshort
  obtain ⟨t, _, htb, hn, _⟩ := normalize_signedMonomial hd
    (gadgetA w B) (gadgetB w B) a b hb
  have ht : t = star b := by
    apply signed_mul_injective hd hb
    rw [IdealCVP.Cyclotomic.mul_comm b t, htb,
      IdealCVP.Cyclotomic.mul_comm b (star b), signed_inverse hd hb]
  subst t
  obtain ⟨ξ, hξ, _⟩ := normalized_short_boolean w B _ (hn.le.trans hshort)
  refine ⟨⟨ξ, ?_⟩, hξ⟩
  apply (boolean_vector_short_iff w B ξ).mp
  rw [← hξ]
  exact hn.le.trans hshort

/-- Executable recovery is correct on every short nonzero vector, and reconstructs `a`. -/
theorem recover_correct (w : List ℕ) (B : ℕ) (a b : Coeff (2 * halfDegree w.length))
    (hne : moduleVector (gadgetA w B) (gadgetB w B) a b ≠ 0)
    (hshort : pairSup (moduleVector (gadgetA w B) (gadgetB w B) a b) ≤
      (gadget w B).M) :
    (∑ j : Fin w.length, (w.get j : ℤ) * (if recover w a b j then 1 else 0)) = (B : ℤ) ∧
      a = mul b (booleanWord (length_le_outputDegree w.length) (recover w a b)) := by
  obtain ⟨ξ, hξ⟩ := short_normalized_assignment w B a b hne hshort
  rw [recover_of_normalized w a b ξ.val hξ]
  refine ⟨ξ.property, ?_⟩
  rw [← hξ, ← coeff_mul_assoc (degree_dyadic w.length).pos,
    IdealCVP.Cyclotomic.mul_comm b (star b),
    signed_inverse (degree_dyadic w.length).pos (short_second_monomial w B a b hne hshort),
    mul_coeffOne]

/-- The map `(ξ,b) ↦ b G(a_ξ,1)`, with the short-vector codomain proved. -/
def witnessVector (w : List ℕ) (B : ℕ)
    (p : Satisfying w B × SignedUnits (2 * halfDegree w.length)) : ShortVectors w B :=
  ⟨pairMul p.2.val (moduleVector (gadgetA w B) (gadgetB w B)
    (booleanWord (length_le_outputDegree w.length) p.1.val)
    (coeffOne (degree_dyadic w.length).pos)), by
    refine ⟨(Reduction.SignedMonomial.pairMul_ne_zero_iff p.2.property _).mpr
      (boolean_vector_ne_zero w B p.1.val), ?_, ?_⟩
    · exact ⟨mul p.2.val (booleanWord (length_le_outputDegree w.length) p.1.val),
        mul p.2.val (coeffOne (degree_dyadic w.length).pos),
        moduleVector_mul (degree_dyadic w.length).pos _ _ _ _ _⟩
    · rw [Reduction.SignedMonomial.pairSup_mul p.2.property]
      exact (boolean_vector_short_iff w B p.1.val).mpr p.1.property⟩

/-- Corollary 4.3: the displayed witness map is bijective. -/
theorem witnessVector_bijective (w : List ℕ) (B : ℕ) :
    Function.Bijective (witnessVector w B) := by
  have hd := (degree_dyadic w.length).pos
  have hv (p : Satisfying w B × SignedUnits (2 * halfDegree w.length)) :
      (witnessVector w B p).val = moduleVector (gadgetA w B) (gadgetB w B)
        (mul p.2.val (booleanWord (length_le_outputDegree w.length) p.1.val)) p.2.val := by
    change pairMul p.2.val _ = _
    rw [← moduleVector_mul hd, mul_coeffOne_right]
  constructor
  · intro p q he
    have he' := congrArg Subtype.val he
    rw [hv, hv] at he'
    have hm := @gadget_multipliers_injective w B
      (mul p.2.val (booleanWord (length_le_outputDegree w.length) p.1.val), p.2.val)
      (mul q.2.val (booleanWord (length_le_outputDegree w.length) q.1.val), q.2.val) he'
    have hb := congrArg Prod.snd hm
    have ha := congrArg Prod.fst hm
    dsimp only at hb ha
    rw [hb] at ha
    have hξ := booleanWord_injective (length_le_outputDegree w.length)
      (signed_mul_injective hd q.2.property ha)
    exact Prod.ext (Subtype.ext hξ) (Subtype.ext hb)
  · intro v
    obtain ⟨a, b, hab⟩ := v.property.2.1
    have hne : moduleVector (gadgetA w B) (gadgetB w B) a b ≠ 0 :=
      hab.symm ▸ v.property.1
    have hshort : pairSup (moduleVector (gadgetA w B) (gadgetB w B) a b) ≤
        (gadget w B).M := hab.symm ▸ v.property.2.2
    have hb := short_second_monomial w B a b hne hshort
    obtain ⟨hξ, ha⟩ := recover_correct w B a b hne hshort
    refine ⟨(⟨recover w a b, hξ⟩, ⟨b, hb⟩), Subtype.ext ?_⟩
    rw [hv]
    dsimp only
    rw [← ha, hab]

/-- Corollary 4.3 as an equivalence of finite types. -/
noncomputable def witnessEquiv (w : List ℕ) (B : ℕ) :
    (Satisfying w B × SignedUnits (2 * halfDegree w.length)) ≃ ShortVectors w B :=
  Equiv.ofBijective (witnessVector w B) (witnessVector_bijective w B)

noncomputable instance (w : List ℕ) (B : ℕ) : Fintype (ShortVectors w B) :=
  Fintype.ofEquiv _ (witnessEquiv w B)

/-- Exactly `2n N_sol` nonzero vectors lie inside radius `M`. -/
theorem card_shortVectors (w : List ℕ) (B : ℕ) :
    Fintype.card (ShortVectors w B) =
      2 * degree w.length * Fintype.card (Satisfying w B) := by
  rw [← Fintype.card_congr (witnessEquiv w B), Fintype.card_prod, card_signedUnits]
  exact Nat.mul_comm _ _

end Power2ModuleSVPSubsetSum.Search
