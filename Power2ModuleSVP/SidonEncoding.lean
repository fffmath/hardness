import Power2ModuleSVP.Sidon
import Mathlib.Algebra.Polynomial.Reverse
import Power2ModuleSVP.BooleanSourcePadding
import Power2ModuleSVP.SidonReciprocal
import Mathlib.Tactic

/-!
# Finite sparse source data

Explicit finite exponent sets implement the construction of `prop:sidon-source`.
The use of a Finset for the support makes the coefficient alphabet manifest;
the row-classification proof is in `BooleanSourceAffine`.
-/
namespace Power2ModuleSVP
namespace SparseEncoding
open Polynomial
open scoped BigOperators

abbrev Clauses (v r : ℕ) := Fin r → Finset (Fin v)

def WellFormed {v r : ℕ} (C : Clauses v r) : Prop := ∀ j, (C j).card = 3

def Satisfiable {v r : ℕ} (C : Clauses v r) : Prop :=
  ∃ b : Fin v → Bool, ∀ j, ∑ i ∈ C j, (if b i then (1 : ℤ) else 0) = 1

/-- A strict odd-prime choice with a safe convention on tiny inputs. -/
theorem existsPositionPrime (v : ℕ) :
    ∃ ell, ell.Prime ∧ 2 < ell ∧ v < ell ∧ ell < 2 * max v 2 := by
  obtain ⟨ell,hp,ho,hl,hu⟩ := Sidon.exists_prime_interval (v := max v 2) (by omega)
  exact ⟨ell,hp,ho,by omega,hu⟩

def positionPrime (v : ℕ) : ℕ := Nat.find (existsPositionPrime v)

theorem positionPrime_spec (v : ℕ) :
    (positionPrime v).Prime ∧ 2 < positionPrime v ∧ v < positionPrime v ∧
      positionPrime v < 2 * max v 2 := Nat.find_spec (existsPositionPrime v)

def B (ell v : ℕ) := Sidon.bound ell v
def delta (ell v : ℕ) := 4 * B ell v + 1
/-- `j` is zero-based; this is the paper's `U_(j+1)`. -/
def cluster (ell v j : ℕ) := (j+1) * delta ell v
def T (ell v r : ℕ) := (4*r+1) * delta ell v

def originalRow {r : ℕ} (j : Fin (2*r)) : Fin r := ⟨j.val / 2, by omega⟩

/-- The unreflected cluster exponents. Duplicates from the same clause list
are discarded exactly as membership in a clause is a finite set. -/
def lowerSupport {v r : ℕ} (C : Clauses v r) (ell : ℕ) : Finset ℕ :=
  Finset.univ.biUnion fun j : Fin (2*r) =>
    (C (originalRow j)).image fun i => cluster ell v j.val - Sidon.position ell i

/-- Reflect every lower exponent and include the constant and leading guards. -/
def support {v r : ℕ} (C : Clauses v r) (ell : ℕ) : Finset ℕ :=
  {0, T ell v r} ∪ lowerSupport C ell ∪
    (lowerSupport C ell).image (T ell v r - ·)

/-- Polynomial interpretation. The finite set itself is the executable output. -/
noncomputable def P {v r : ℕ} (C : Clauses v r) (ell : ℕ) : ℤ[X] :=
  ∑ k ∈ support C ell, X^k

/-- Permitted input coordinates. -/
def positions (ell v : ℕ) : Finset ℕ := Finset.univ.image (Sidon.position ell : Fin v → ℕ)

/-- Minkowski sum of the permitted inputs and the polynomial support. -/
def touched {v r : ℕ} (C : Clauses v r) (ell : ℕ) : Finset ℕ :=
  (positions ell v).biUnion fun a => (support C ell).image (a + ·)

/-- Even copies, using the paper's one-based numbering. -/
def negativeRows (ell v r : ℕ) : Finset ℕ :=
  Finset.univ.image fun h : Fin r => cluster ell v (2*h.val+1)

/-- The negative case has priority, including on malformed inputs. -/
def translation {v r : ℕ} (C : Clauses v r) (ell z : ℕ) : ℤ :=
  if z ∈ negativeRows ell v r then -1 else if z ∈ touched C ell then 0 else 1

theorem translation_alphabet {v r : ℕ} (C : Clauses v r) (ell z : ℕ) :
    translation C ell z = -1 ∨ translation C ell z = 0 ∨ translation C ell z = 1 := by
  unfold translation
  split_ifs <;> simp

theorem coeff_P {v r : ℕ} (C : Clauses v r) (ell z : ℕ) :
    (P C ell).coeff z = if z ∈ support C ell then 1 else 0 := by
  classical
  simp [P, coeff_X_pow]

theorem coeff_P_nonneg {v r : ℕ} (C : Clauses v r) (ell z : ℕ) :
    0 ≤ (P C ell).coeff z := by rw [coeff_P]; split_ifs <;> norm_num

theorem coeff_P_bit {v r : ℕ} (C : Clauses v r) (ell z : ℕ) :
    (P C ell).coeff z = 0 ∨ (P C ell).coeff z = 1 := by
  rw [coeff_P]; split_ifs <;> simp

theorem T_pos (ell v r : ℕ) : 0 < T ell v r := by
  unfold T delta
  positivity

theorem T_odd (ell v r : ℕ) : T ell v r % 2 = 1 := by
  simp [T, delta, Nat.add_mod, Nat.mul_mod]

theorem lower_bounds {v r : ℕ} (C : Clauses v r) {ell : ℕ} (hell : 0 < ell)
    {k : ℕ} (hk : k ∈ lowerSupport C ell) :
    B ell v < k ∧ k ≤ 2*r*delta ell v := by
  obtain ⟨j,_,hk⟩ := Finset.mem_biUnion.mp hk
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
  have ha := Sidon.position_le_bound hell i
  have hj := j.isLt
  dsimp [cluster]
  have hd : delta ell v = 4*B ell v+1 := rfl
  have hmul := Nat.mul_le_mul_right (delta ell v) (show j.val+1 ≤ 2*r by omega)
  have hmul' := Nat.mul_le_mul_right (delta ell v) (show 1 ≤ j.val+1 by omega)
  dsimp [B] at *
  omega

theorem support_bounds {v r : ℕ} (C : Clauses v r) {ell : ℕ} (hell : 0 < ell)
    {k : ℕ} (hk : k ∈ support C ell) : k ≤ T ell v r := by
  simp only [support, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image] at hk
  rcases hk with ((rfl | rfl) | hk) | ⟨a,ha,rfl⟩
  · omega
  · rfl
  · have hb := (lower_bounds C hell hk).2
    dsimp [T]
    nlinarith [Nat.zero_le (delta ell v)]
  · omega

theorem constant_coeff {v r : ℕ} (C : Clauses v r) (ell : ℕ) :
    (P C ell).coeff 0 = 1 := by rw [coeff_P]; simp [support]

theorem leading_coeff {v r : ℕ} (C : Clauses v r) (ell : ℕ) :
    (P C ell).coeff (T ell v r) = 1 := by rw [coeff_P]; simp [support]

theorem degree_P {v r : ℕ} (C : Clauses v r) {ell : ℕ} (hell : 0 < ell) :
    (P C ell).natDegree = T ell v r := by
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [coeff_P, ite_eq_right]
    exact fun h => (not_le.mpr hk) (support_bounds C hell h)
  · exact le_natDegree_of_ne_zero (by rw [leading_coeff]; norm_num)

theorem support_gap {v r : ℕ} (C : Clauses v r) {ell : ℕ} (hell : 0 < ell)
    {k : ℕ} (hk0 : 0 < k) (hkB : k ≤ B ell v) : (P C ell).coeff k = 0 := by
  rw [coeff_P, ite_eq_right]
  intro hk
  simp only [support, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image] at hk
  rcases hk with ((hk | hk) | hk) | ⟨a,ha,hak⟩
  · omega
  · have ht : B ell v < T ell v r := by
      dsimp [T, delta]
      nlinarith
    omega
  · have := (lower_bounds C hell hk).1
    omega
  · have hb := (lower_bounds C hell ha).2
    have ht : 2*r*delta ell v + B ell v < T ell v r := by
      dsimp [T, delta]
      nlinarith
    omega

/-- A prime in the required strict interval. -/
theorem existsExponentPrime {t : ℕ} (ht : 0 < t) :
    ∃ p, p.Prime ∧ 8*t < p ∧ p < 16*t := by
  obtain ⟨p,hp,hl,hu⟩ := Nat.bertrand (8*t) (by omega)
  have hn : p ≠ 16*t := by
    intro he
    have hd : 2 ∣ p := by omega
    have hh := (Nat.dvd_prime hp).mp hd
    rcases hh with hh | hh <;> omega
  exact ⟨p,hp,hl,by omega⟩

def exponentPrime (ell v r : ℕ) := Nat.find (existsExponentPrime (T_pos ell v r))
def L (ell v r : ℕ) := (exponentPrime ell v r + T ell v r) / 2

theorem exponentPrime_spec (ell v r : ℕ) :
    (exponentPrime ell v r).Prime ∧ 8*T ell v r < exponentPrime ell v r ∧
      exponentPrime ell v r < 16*T ell v r :=
  Nat.find_spec (existsExponentPrime (T_pos ell v r))

theorem L_spec (ell v r : ℕ) :
    4*T ell v r < L ell v r ∧
    L ell v r - T ell v r + L ell v r = exponentPrime ell v r ∧
    L ell v r < exponentPrime ell v r - 1 ∧ L ell v r ≤ 9*T ell v r := by
  have hp := exponentPrime_spec ell v r
  have ht := T_pos ell v r
  have hodd := T_odd ell v r
  have hpodd : exponentPrime ell v r % 2 = 1 := by
    have h := hp.1.eq_two_or_odd
    rcases h with h | h
    · omega
    · exact h
  dsimp [L]
  omega

/-- The exact size identity, useful to bound output lengths. -/
theorem T_eq (ell v r : ℕ) : T ell v r = (4*r+1)*(4*B ell v+1) := rfl

/-- An explicit polynomial bound, with the harmless empty-clause convention. -/
theorem size_bound {ell v r : ℕ} (hell : 0 < ell) (hhi : ell < 2*v) :
    L ell v r ≤ 9*(4*r+1)*(16*v^2+8*v+1) := by
  have hb := Sidon.bound_lt hell hhi
  have hm : 4*B ell v+1 ≤ 16*v^2+8*v+1 := by dsimp [B]; omega
  calc
    _ ≤ 9*T ell v r := (L_spec ell v r).2.2.2
    _ = 9*((4*r+1)*(4*B ell v+1)) := rfl
    _ ≤ 9*((4*r+1)*(16*v^2+8*v+1)) :=
      Nat.mul_le_mul_left 9 (Nat.mul_le_mul_left (4*r+1) hm)
    _ = _ := by ring

/-- The support weight is at most the paper's exact weight; equality additionally
uses disjointness of the three exponent families. -/
theorem weight_bound {v r : ℕ} (C : Clauses v r) (ell : ℕ) (hC : WellFormed C) :
    (support C ell).card ≤ 2+12*r := by
  have hl : (lowerSupport C ell).card ≤ 6*r := by
    calc
      _ ≤ ∑ j : Fin (2*r), ((C (originalRow j)).image
          (fun i => cluster ell v j.val - Sidon.position ell i)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin (2*r), 3 := by
        apply Finset.sum_le_sum
        intro j _
        exact (Finset.card_image_le).trans (hC (originalRow j)).le
      _ = _ := by simp; ring
  have h1 := Finset.card_union_le ({0,T ell v r} : Finset ℕ) (lowerSupport C ell)
  have h2 := Finset.card_union_le ({0,T ell v r} ∪ lowerSupport C ell)
    ((lowerSupport C ell).image (T ell v r - ·))
  have h3 := Finset.card_image_le (s := lowerSupport C ell) (f := (T ell v r - ·))
  have h4 : ({0,T ell v r} : Finset ℕ).card ≤ 2 := by
    calc
      _ ≤ ({T ell v r} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  dsimp [support]
  omega

/-- Reflection preserves the finite support. -/
theorem support_closed {v r : ℕ} (C : Clauses v r) {ell : ℕ} (hell : 0 < ell)
    {k : ℕ} (hk : k ∈ support C ell) : T ell v r - k ∈ support C ell := by
  have hbound := support_bounds C hell hk
  simp only [support, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image] at hk ⊢
  rcases hk with ((rfl | rfl) | hk) | ⟨a,ha,rfl⟩
  · exact Or.inl (Or.inl (Or.inr (by omega)))
  · exact Or.inl (Or.inl (Or.inl (by omega)))
  · exact Or.inr ⟨_,hk,rfl⟩
  · have haT : a ≤ T ell v r := support_bounds C hell (by
      unfold support
      exact Finset.mem_union_left _ (Finset.mem_union_right _ ha))
    exact Or.inl (Or.inr (by simpa [Nat.sub_sub_self haT] using ha))

theorem reflection_image {v r : ℕ} (C : Clauses v r) {ell : ℕ} (hell : 0 < ell) :
    (support C ell).image (T ell v r - ·) = support C ell := by
  ext k
  constructor
  · rintro hk
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hk
    exact support_closed C hell ha
  · intro hk
    exact Finset.mem_image.mpr ⟨_, support_closed C hell hk,
      Nat.sub_sub_self (support_bounds C hell hk)⟩

/-- Coefficient-level reciprocity, including the vanishing tail. -/
theorem P_reciprocal {v r : ℕ} (C : Clauses v r) {ell : ℕ} (hell : 0 < ell) :
    (P C ell).reflect (T ell v r) = P C ell := by
  ext k
  rw [coeff_reflect, coeff_P, coeff_P]
  by_cases hk : k ≤ T ell v r
  · rw [revAt_le hk]
    have he : T ell v r - k ∈ support C ell ↔ k ∈ support C ell := by
      constructor
      · intro h
        simpa [Nat.sub_sub_self hk] using support_closed C hell h
      · exact support_closed C hell
    simp only [he]
  · have hr : T ell v r < k := by omega
    rw [revAt_eq_self_of_lt hr]

/-- Every potentially occupied output coordinate lies below `T+B+1`. -/
theorem touched_bound {v r : ℕ} (C : Clauses v r) {ell : ℕ} (hell : 0 < ell)
    {z : ℕ} (hz : z ∈ touched C ell) : z ≤ T ell v r + B ell v := by
  obtain ⟨a,ha,hz⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
  have haB := Sidon.position_le_bound hell i
  have hkT := support_bounds C hell hk
  dsimp [B] at *
  omega

theorem negative_bounds {ell v r z : ℕ} (hz : z ∈ negativeRows ell v r) :
    B ell v < z ∧ z < T ell v r := by
  obtain ⟨h,_,rfl⟩ := Finset.mem_image.mp hz
  have hh := h.isLt
  have hd : 0 < delta ell v := by unfold delta; positivity
  have hm := Nat.mul_le_mul_right (delta ell v) (show 2*h.val+2 ≤ 2*r by omega)
  have hm' := Nat.mul_le_mul_right (delta ell v) (show 1 ≤ 2*h.val+2 by omega)
  have hdelta : delta ell v = 4*B ell v+1 := rfl
  have h2 : 2*r*delta ell v < (4*r+1)*delta ell v :=
    Nat.mul_lt_mul_of_pos_right (by omega) hd
  dsimp [cluster, T]
  constructor
  · nlinarith
  · nlinarith

theorem translation_high {v r : ℕ} (C : Clauses v r) {ell : ℕ} (hell : 0 < ell)
    {z : ℕ} (hz : T ell v r + B ell v < z) : translation C ell z = 1 := by
  have hn : z ∉ negativeRows ell v r := by
    intro h
    have := (negative_bounds h).2
    omega
  have ht : z ∉ touched C ell := by
    intro h
    have := touched_bound C hell h
    omega
  simp [translation, hn, ht]

theorem translation_low {v r : ℕ} (C : Clauses v r) {ell : ℕ} (hell : 0 < ell)
    {z : ℕ} (hz : z ≤ B ell v) (hA : z ∉ positions ell v) : translation C ell z = 1 := by
  have hn : z ∉ negativeRows ell v r := by
    intro h
    have := (negative_bounds h).1
    omega
  have ht : z ∉ touched C ell := by
    intro h
    obtain ⟨a,ha,hz'⟩ := Finset.mem_biUnion.mp h
    obtain ⟨k,hk,hak⟩ := Finset.mem_image.mp hz'
    have hk0 : k = 0 := by
      by_contra hk0
      have hg := support_gap C hell (show 0 < k by omega) (show k ≤ B ell v by omega)
      rw [coeff_P, ite_eq_left hk] at hg
      omega
    subst k
    simp only [add_zero] at hak
    exact hA (hak ▸ ha)
  simp [translation, hn, ht]

/-- A bit polynomial is the canonical degree-bounded representative of a bit vector. -/
def BitPolynomial (len : ℕ) (f : ℤ[X]) : Prop :=
  f.degree < len ∧ ∀ z, f.coeff z = 0 ∨ f.coeff z = 1

/-- The precise Boolean affine equation in the quotient by `X^L+P`. -/
def AffineSolution {v r : ℕ} (C : Clauses v r) (ell : ℕ) (x y : ℤ[X]) : Prop :=
  BitPolynomial (L ell v r) x ∧ BitPolynomial (L ell v r) y ∧
    ∀ z < L ell v r, y.coeff z =
      ((P C ell*x) %ₘ (X^(L ell v r)+P C ell)).coeff z + translation C ell z

/-- `lem:sidon-padding` specialized to the explicit finite source data. -/
theorem encoding_padding {v r : ℕ} (C : Clauses v r) {ell : ℕ} (hell : 0 < ell)
    {x y : ℤ[X]} (h : AffineSolution C ell x y) :
    (∀ z, z ∉ positions ell v → x.coeff z = 0) ∧
      (P C ell*x) %ₘ (X^(L ell v r)+P C ell) = P C ell*x := by
  have hBT : B ell v < T ell v r := by
    dsimp [T, delta]
    nlinarith
  obtain ⟨hx,hy,he⟩ := h
  exact BooleanSource.sidon_padding (T_pos ell v r) hBT
    (by have := (L_spec ell v r).1; omega) (degree_P C hell).le hx.1
    (coeff_P_nonneg C ell)
    (fun z => by rcases hx.2 z with h | h <;> omega)
    (fun z _ => by rcases hy.2 z with h | h <;> omega)
    (constant_coeff C ell) (leading_coeff C ell)
    (fun z hz hzB => support_gap C hell hz hzB)
    (fun z hz _ => translation_high C hell hz)
    (fun z hz hA => translation_low C hell hz hA) he

/-- Rational interpretation for the algebraic separation theorem. -/
noncomputable def rationalP {v r : ℕ} (C : Clauses v r) (ell : ℕ) : ℚ[X] :=
  (P C ell).map (Int.castRingHom ℚ)

/-- The constructed modulus and its actual reciprocal have no common complex zero. -/
theorem encoding_no_common_root {v r : ℕ} (C : Clauses v r) {ell : ℕ}
    (hell : 0 < ell) (a : ℂ) :
    ¬ (aeval a (Sidon.modulus (rationalP C ell) (L ell v r)) = 0 ∧
      aeval a (Sidon.modulus (rationalP C ell) (L ell v r)).reverse = 0) := by
  have hdeg : (rationalP C ell).natDegree ≤ T ell v r := by
    exact (natDegree_map_le).trans (degree_P C hell).le
  have hrec : (rationalP C ell).reflect (T ell v r) = rationalP C ell := by
    rw [rationalP, reflect_map, P_reciprocal C hell]
  have hone : aeval (1 : ℂ) (Sidon.modulus (rationalP C ell) (L ell v r)) ≠ 0 := by
    have he : aeval (1 : ℂ) (Sidon.modulus (rationalP C ell) (L ell v r)) =
        1 + (support C ell).card := by
      simp [Sidon.modulus, rationalP, P, aeval_def, eval_finsetSum]
    rw [he]
    have hn : (0 : ℝ) < 1 + (support C ell).card := by positivity
    intro hz
    have hreal := congrArg Complex.re hz
    simp at hreal
    linarith
  exact Sidon.no_common_root_reverse hdeg (by have := (L_spec ell v r).1; omega)
    hrec (exponentPrime_spec ell v r).1 (L_spec ell v r).2.1
    (L_spec ell v r).2.2.1 hone a

/-- Explicit polynomial bound in the nonempty regime of the reduction. -/
theorem size_bound_nonempty {ell v r : ℕ} (hell : 0 < ell) (hhi : ell < 2*v)
    (_hv : 1 ≤ v) (hr : 1 ≤ r) : L ell v r ≤ 1125*r*v^2 := by
  have h1 : 4*r+1 ≤ 5*r := by omega
  have hv2 : v ≤ v^2 := by nlinarith
  have h2 : 16*v^2+8*v+1 ≤ 25*v^2 := by nlinarith
  calc
    _ ≤ 9*(4*r+1)*(16*v^2+8*v+1) := size_bound hell hhi
    _ ≤ 9*(5*r)*(25*v^2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 9 h1) h2
    _ = _ := by ring

theorem L_ge_64 {ell v r : ℕ} (hB : 4 ≤ B ell v) : 64 ≤ L ell v r := by
  have h1 := (L_spec ell v r).1
  have h2 : 4*B ell v+1 ≤ T ell v r := by
    unfold T delta
    nlinarith
  omega

/-- The executable output consists of finite exponent and coefficient data.
`P` is only its mathematical polynomial interpretation. -/
structure EncodedSource where
  degreeBound : ℕ
  dimension : ℕ
  exponents : Finset ℕ
  offset : List ℤ
  deriving DecidableEq

/-- Deterministic finite-data encoding; `positionPrime` and `exponentPrime`
are searches using decidable primality predicates. -/
def encode {v r : ℕ} (C : Clauses v r) : EncodedSource :=
  let ell := positionPrime v
  ⟨T ell v r,L ell v r,support C ell,
    (List.range (L ell v r)).map (translation C ell)⟩

theorem encode_offset_length {v r : ℕ} (C : Clauses v r) :
    (encode C).offset.length = (encode C).dimension := by simp [encode]

theorem encode_offset_coeff {v r : ℕ} (C : Clauses v r) (i : Fin (encode C).dimension) :
    (encode C).offset[i.val]'(by rw [encode_offset_length]; exact i.isLt) =
      translation C (positionPrime v) i.val := by simp [encode]

end SparseEncoding
end Power2ModuleSVP
