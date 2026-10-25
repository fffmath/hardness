import IdealCVP.Complexity.X3CList
import IdealCVP.Complexity.CompileFastPolyTime

/-! # Polynomial-time X3C verification with Boolean selection lists -/

namespace IdealCVP

open Turing.MultiTapeTM Cslib.Complexity
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

namespace X3CList

/-- Check that each indexed triple has three distinct labels in the universe. -/
def wellFormedCheck (x : X3CList) : Bool :=
  x.2.all fun t => decide (ValidTriple x.1 t)

@[simp] theorem wellFormedCheck_eq (x : X3CList) :
    wellFormedCheck x = true ↔ x.WellFormed := by
  simp [wellFormedCheck, WellFormed]

/-- Count selected indexed triples incident to a given universe label. -/
def coverCount (x : X3CList) (w : List Bool) (u : ℕ) : ℕ :=
  (List.range x.2.length).countP fun j =>
    incident u (x.2.getD j (0, 0, 0)) && w.getD j false

theorem coverCount_eq (x : X3CList) (w : List Bool) (u : ℕ) :
    (coverCount x w u : ℤ) = ∑ j : Fin x.2.length,
      bit (incident u x.2[j.val]) * bit (w.getD j.val false) := by
  rw [coverCount, Fast.count_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [List.getD_eq_getElem _ _ j.isLt]
  cases incident u x.2[j.val] <;> cases w.getD j.val false <;> rfl

/-- Verify a Boolean exact-cover certificate, including its length and input validity. -/
def check (p : X3CList × List Bool) : Bool :=
  wellFormedCheck p.1 && decide (p.2.length = p.1.2.length) &&
    (List.range (3 * p.1.1)).all fun u => decide (coverCount p.1 p.2 u = 1)

/-- The Boolean checker accepts exactly valid selections covering every element once. -/
theorem check_eq (x : X3CList) (w : List Bool) : check (x, w) = true ↔
    x.WellFormed ∧ w.length = x.2.length ∧ ∀ u : Fin (3 * x.1),
      (∑ j : Fin x.2.length,
        bit (incident u.val x.2[j.val]) * bit (w.getD j.val false)) = 1 := by
  simp only [check, Bool.and_eq_true, wellFormedCheck_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, and_assoc]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro h u
    rw [← coverCount_eq, h u.val u.isLt]
    rfl
  · intro h u hu
    exact_mod_cast (coverCount_eq x w u).trans (h ⟨u, hu⟩)

attribute [local irreducible] List.getD

@[fun_prop] theorem poly_incident : ComputableTidilyInPolyTime
    (fun p : ℕ × X3CTriple => incident p.1 p.2)
    (encPair encNat encX3CTriple) encBool := by
  unfold incident encX3CTriple
  fun_prop

/-- Validity of three binary labels is decidable in native polynomial time. -/
@[fun_prop] theorem poly_validTriple : ComputableTidilyInPolyTime
    (fun p : ℕ × X3CTriple => decide (ValidTriple p.1 p.2))
    (encPair encNat encX3CTriple) encBool := by
  have he : (fun p : ℕ × X3CTriple => decide (ValidTriple p.1 p.2)) =
      (fun p => decide (p.2.1 < 3 * p.1) && (decide (p.2.2.1 < 3 * p.1) &&
        (decide (p.2.2.2 < 3 * p.1) && (decide (p.2.1 ≠ p.2.2.1) &&
          (decide (p.2.1 ≠ p.2.2.2) && decide (p.2.2.1 ≠ p.2.2.2)))))) := by
    funext p
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rfl
  rw [he]
  let ein := encPair encNat encX3CTriple
  have ha : ComputableTidilyInPolyTime (fun p : ℕ × X3CTriple => p.2.1) ein encNat :=
    (snd _ _).fst'
  have hb : ComputableTidilyInPolyTime (fun p : ℕ × X3CTriple => p.2.2.1) ein encNat :=
    (snd _ _).snd'.fst'
  have hc : ComputableTidilyInPolyTime (fun p : ℕ × X3CTriple => p.2.2.2) ein encNat :=
    (snd _ _).snd'.snd'
  have hq : ComputableTidilyInPolyTime (fun p : ℕ × X3CTriple => 3 * p.1) ein encNat :=
    binary_mul.comp ((const 3).prod (fst _ _))
  exact bool_and' (binary_lt' ha hq) (bool_and' (binary_lt' hb hq)
    (bool_and' (binary_lt' hc hq) (bool_and' (decide_ne ha hb)
      (bool_and' (decide_ne ha hc) (decide_ne hb hc)))))

@[fun_prop] theorem poly_wellFormedCheck : ComputableTidilyInPolyTime
    wellFormedCheck encX3C encBool := by
  unfold wellFormedCheck
  apply allWithInput (encA := encX3CTriple)
  · exact snd encUnary (encList encX3CTriple)
  · have hp : ComputableTidilyInPolyTime
        (fun p : X3CList × X3CTriple => (p.1.1, p.2))
        (encPair encX3C encX3CTriple) (encPair encNat encX3CTriple) :=
      (unary_to_binary.comp (fst _ _).fst').prod (snd _ _)
    exact poly_validTriple.comp hp

@[fun_prop] theorem poly_coverCount : ComputableTidilyInPolyTime
    (fun p : (X3CList × List Bool) × ℕ => coverCount p.1.1 p.1.2 p.2)
    (encPair (encPair encX3C (encList encBool)) encUnary) encUnary := by
  unfold coverCount
  apply countPWithInput (encA := encUnary)
  · unfold encX3C
    fun_prop
  · have hi : ComputableTidilyInPolyTime
        (fun p : ((X3CList × List Bool) × ℕ) × ℕ =>
          incident p.1.2 (p.1.1.1.2.getD p.2 (0, 0, 0)))
        (encPair (encPair (encPair encX3C (encList encBool)) encUnary) encUnary)
        encBool := by
      have hp : ComputableTidilyInPolyTime
          (fun p : ((X3CList × List Bool) × ℕ) × ℕ =>
            (p.1.2, p.1.1.1.2.getD p.2 (0, 0, 0)))
          (encPair (encPair (encPair encX3C (encList encBool)) encUnary) encUnary)
          (encPair encNat encX3CTriple) := by
        apply ComputableTidilyInPolyTime.prod
        · exact unary_to_binary.comp (fst _ _).snd'
        · unfold encX3C
          fun_prop
      exact poly_incident.comp hp
    apply bool_and' hi
    fun_prop

/-- The complete Boolean-list X3C verifier runs in native polynomial time. -/
@[fun_prop] theorem poly_check : ComputableTidilyInPolyTime check
    (encPair encX3C (encList encBool)) encBool := by
  unfold check encX3C
  fun_prop

end X3CList

/-- The list X3C language is exactly the language accepted by the certificate checker. -/
theorem x3cLang_iff_exists_check (x : X3CList) :
    x ∈ X3CLang ↔ ∃ w : List Bool, X3CList.check (x, w) = true := by
  constructor
  · rintro ⟨hw, ξ, hξ⟩
    refine ⟨List.ofFn ξ, (X3CList.check_eq x _).mpr ⟨hw, List.length_ofFn, ?_⟩⟩
    simpa [List.getD_eq_getElem?_getD] using hξ
  · rintro ⟨w, hw⟩
    obtain ⟨hx, _, h⟩ := (X3CList.check_eq x w).mp hw
    exact ⟨hx, (fun j => w.getD j.val false), h⟩

/-- A selection bit per indexed triple, with framing included in its bound. -/
theorem x3c_mem_NP : X3CLang ∈ NP encX3C := by
  have he : X3CLang = {x | ∃ w : List Bool, X3CList.check (x, w) = true} := by
    ext x
    exact x3cLang_iff_exists_check x
  rw [he]
  apply mem_NP_of_witness (p := 3 * Polynomial.X) Decoder.bool.list
    X3CList.poly_check (fun _ _ => Iff.rfl)
  intro x w hw
  refine ⟨w, hw, ?_⟩
  have hwlen := ((X3CList.check_eq x w).mp hw).2.1
  have hlen : (encList encBool w).length ≤ 3 * w.length := by
    calc
      _ ≤ w.length * (2 * 1 + 1) := length_encList_le encBool w
        (fun b _ => by cases b <;> decide)
      _ = _ := by omega
  have hin : x.2.length ≤ (encX3C x).length :=
    (length_le_length_encList encX3CTriple x.2).trans
      (length_le_encPair_right encUnary (encList encX3CTriple) x)
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  exact hlen.trans (Nat.mul_le_mul_left 3 (by omega))

end IdealCVP
