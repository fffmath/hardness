import Rank2ModuleSVP.Problem

/-! Executable prime-cyclotomic arithmetic for the membership verifier.
All stored ring elements have `q-1` power-basis coefficients. -/
namespace Rank2ModuleSVP.Membership
open scoped BigOperators
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Lookup in a power-basis list, padded by zero at the omitted coefficient. -/
def coeff (q : ℕ) (a : List ℤ) (i : ℕ) : ℤ :=
  if i < q-1 then a.getD i 0 else 0

/-- Cyclic convolution modulo `X^q-1`. -/
def cyclicCoeff (q : ℕ) (a b : List ℤ) (r : ℕ) : ℤ :=
  ((List.range q).map fun i => coeff q a i * coeff q b ((r+q-i)%q)).sum

/-- Eliminate `X^(q-1)` using `1+X+⋯+X^(q-1)=0`. -/
def mul (q : ℕ) (a b : List ℤ) : List ℤ :=
  (List.range (q-1)).map fun r => cyclicCoeff q a b r - cyclicCoeff q a b (q-1)

def add (q : ℕ) (a b : List ℤ) : List ℤ := IdealCVP.listAdd (q-1) a b

def sub (q : ℕ) (a b : List ℤ) : List ℤ := IdealCVP.listSub (q-1) a b

@[simp] theorem length_mul (q : ℕ) (a b : List ℤ) : (mul q a b).length = q-1 := by
  simp [mul]
@[simp] theorem length_add (q : ℕ) (a b : List ℤ) : (add q a b).length = q-1 := by
  simp [add, IdealCVP.listAdd]
@[simp] theorem length_sub (q : ℕ) (a b : List ℤ) : (sub q a b).length = q-1 := by
  simp [sub, IdealCVP.listSub]

section Semantics
variable {q : ℕ} [NeZero q]

/-- Normalize any cyclic representative by subtracting its last coefficient. -/
def repr (c : Coeff ℤ q) : List ℤ :=
  (List.range (q-1)).map fun (i : ℕ) => c (i : ZMod q) - c ((q-1 : ℕ) : ZMod q)

@[simp] theorem length_repr (c : Coeff ℤ q) : (repr c).length = q-1 := by simp [repr]

theorem powerCoeffs_repr (c : Coeff ℤ q) :
    powerCoeffs (repr c) = fun a => c a - c ((q-1 : ℕ) : ZMod q) := by
  funext a
  unfold powerCoeffs
  split_ifs with ha
  · simp only [repr, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range, ha, ↓reduceIte, Option.map_some, Option.getD_some,
      ZMod.natCast_zmod_val]
  · have hal : a.val = q-1 := by have := a.val_lt; omega
    have he : a = ((q-1 : ℕ) : ZMod q) := by
      rw [← hal, ZMod.natCast_zmod_val]
    simp [he]

theorem powerElement_repr (c : Coeff ℤ q) : powerElement (repr c) = classOf c := by
  rw [powerElement, powerCoeffs_repr]
  simpa only [sub_eq_add_neg] using classOf_add_constant c (-c ((q-1 : ℕ) : ZMod q))

theorem powerElement_surjective : Function.Surjective (powerElement (q := q)) := by
  intro v
  obtain ⟨c, rfl⟩ := classOf_surjective v
  exact ⟨repr c, powerElement_repr c⟩

theorem sum_range_zmod (f : ℕ → ℤ) :
    ((List.range q).map f).sum = ∑ a : ZMod q, f a.val := by
  rw [IdealCVP.list_sum_range, Finset.sum_range]
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

theorem sub_index (a b : ZMod q) : (a-b).val = (a.val+q-b.val)%q := by
  have hb : b.val ≤ a.val+q := by have := b.val_lt; omega
  have he : ((a.val+q-b.val : ℕ) : ZMod q) = a-b := by
    rw [Nat.cast_sub hb, Nat.cast_add, ZMod.natCast_zmod_val,
      ZMod.natCast_self, ZMod.natCast_zmod_val]
    ring
  rw [← he, ZMod.val_natCast]

theorem cyclicCoeff_eq (a b : List ℤ) (r : ZMod q) :
    cyclicCoeff q a b r.val = ∑ i : ZMod q, powerCoeffs a i * powerCoeffs b (r-i) := by
  rw [cyclicCoeff, sum_range_zmod]
  apply Finset.sum_congr rfl
  intro i _
  simp only [powerCoeffs, coeff, sub_index]

theorem powerCoeffs_mul (a b : List ℤ) :
    powerCoeffs (mul q a b) = fun r =>
      (∑ i : ZMod q, powerCoeffs a i * powerCoeffs b (r-i)) -
      (∑ i : ZMod q, powerCoeffs a i * powerCoeffs b (((q-1 : ℕ) : ZMod q)-i)) := by
  have hl : (((q-1 : ℕ) : ZMod q)).val = q-1 :=
    ZMod.val_natCast_of_lt (by have := NeZero.pos q; omega)
  funext r
  rw [← cyclicCoeff_eq, ← cyclicCoeff_eq, hl]
  unfold powerCoeffs
  split_ifs with hr
  · simp only [mul, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range, hr, ↓reduceIte, Option.map_some, Option.getD_some]
  · have : r.val = q-1 := by have := r.val_lt; omega
    simp [this]

/-- Executable multiplication agrees with multiplication in the quotient ring. -/
theorem powerElement_mul (a b : List ℤ) :
    powerElement (q := q) (mul q a b) = powerElement a * powerElement b := by
  change classOf (powerCoeffs (mul q a b)) = classOf (powerCoeffs a) * classOf (powerCoeffs b)
  rw [powerCoeffs_mul]
  let f : Coeff ℤ q := fun r => ∑ i : ZMod q, powerCoeffs a i * powerCoeffs b (r-i)
  change classOf (fun r => f r - f ((q-1 : ℕ) : ZMod q)) = _
  calc
    _ = classOf f := by
      simpa only [sub_eq_add_neg] using classOf_add_constant f (-f ((q-1 : ℕ) : ZMod q))
    _ = _ := (classOf_mul (powerCoeffs a) (powerCoeffs b)).symm

theorem powerElement_add (a b : List ℤ) :
    powerElement (q := q) (add q a b) = powerElement a + powerElement b := by
  rw [powerElement, powerElement, powerElement, ← classOf_add]
  congr 1
  funext r
  simp only [powerCoeffs, add, IdealCVP.listAdd, Pi.add_apply]
  split_ifs with h <;>
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range, h, ↓reduceIte, Option.map_some, Option.getD_some,
      add_zero]

theorem powerElement_sub (a b : List ℤ) :
    powerElement (q := q) (sub q a b) = powerElement a - powerElement b := by
  rw [powerElement, powerElement, powerElement, ← classOf_sub]
  congr 1
  funext r
  simp only [powerCoeffs, sub, IdealCVP.listSub, Pi.sub_apply]
  split_ifs with h <;>
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range, h, ↓reduceIte, Option.map_some, Option.getD_some,
      sub_zero]

end Semantics

/-- Canonical squared norm, computed by integer arithmetic on padded lists. -/
def norm (q : ℕ) (a : List ℤ) : ℤ :=
  (q : ℤ) * ((List.range q).map fun i => (coeff q a i)^2).sum -
    (((List.range q).map fun i => coeff q a i).sum)^2

def pairNorm (q : ℕ) (a : List ℤ × List ℤ) : ℤ := norm q a.1 + norm q a.2

section Semantics
variable {q : ℕ} [NeZero q]

theorem norm_eq (a : List ℤ) : norm q a = normSq (powerElement (q := q) a) := by
  rw [powerElement, normSq_classOf, coeffNormSq_eq]
  simp only [norm, sum_range_zmod, coeff, powerCoeffs]

theorem pairNorm_eq (a : List ℤ × List ℤ) :
    pairNorm q a = pairNormSq (powerPair (q := q) a) := by
  simp only [pairNorm, pairNormSq, powerPair, norm_eq]

/-- The omitted coefficient is zero, so a power-basis coefficient is at most
the canonical norm. This is the short-vector half of the certificate bound. -/
theorem powerCoeffs_abs_le_norm (a : List ℤ) (i : ZMod q) :
    |powerCoeffs a i| ≤ norm q a := by
  classical
  let last : ZMod q := ((q-1 : ℕ) : ZMod q)
  have hl : last.val = q-1 :=
    ZMod.val_natCast_of_lt (by have := NeZero.pos q; omega)
  have hz : powerCoeffs a last = 0 := by simp [powerCoeffs, hl]
  rw [norm_eq, powerElement, normSq_classOf]
  by_cases hi : i.val < q-1
  · have hmem : last ∈ Finset.univ.filter (fun b : ZMod q => i.val < b.val) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hl, hi]
    have h₁ := Finset.single_le_sum
      (s := Finset.univ.filter (fun b : ZMod q => i.val < b.val))
      (f := fun b => (powerCoeffs a i - powerCoeffs a b)^2)
      (fun b _ => sq_nonneg _) hmem
    have h₂ := Finset.single_le_sum (s := Finset.univ)
      (f := fun r : ZMod q => ∑ b ∈ Finset.univ.filter (fun b : ZMod q => r.val < b.val),
        (powerCoeffs a r - powerCoeffs a b)^2)
      (fun r _ => Finset.sum_nonneg (fun b _ => sq_nonneg _)) (Finset.mem_univ i)
    rw [hz, sub_zero] at h₁
    rw [← coeffNormSq_pairs] at h₂
    exact (IdealCVP.int_abs_le_sq _).trans (h₁.trans h₂)
  · simp only [powerCoeffs, if_neg hi, abs_zero]
    exact coeffNormSq_nonneg _

/-- Every ring element has a length-`q-1` representative bounded by its norm. -/
theorem exists_norm_bounded_rep (v : IntegerRing q) :
    ∃ a : List ℤ, a.length = q-1 ∧ powerElement a = v ∧
      ∀ z ∈ a, |z| ≤ normSq v := by
  obtain ⟨c, rfl⟩ := classOf_surjective v
  refine ⟨repr c, length_repr c, powerElement_repr c, ?_⟩
  intro z hz
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hz
  have hi' : i < q-1 := by simpa only [length_repr] using hi
  have hil : i < q := by omega
  have hb := powerCoeffs_abs_le_norm (repr c) (i : ZMod q)
  rw [norm_eq, powerElement_repr] at hb
  simpa only [powerCoeffs, ZMod.val_natCast_of_lt hil, if_pos hi',
    List.getD_eq_getElem _ _ hi, he] using hb

theorem pairNormSq_pos_iff (v : IntegerRing q × IntegerRing q) :
    0 < pairNormSq v ↔ v ≠ 0 := by
  have h₁ := normSq_nonneg v.1
  have h₂ := normSq_nonneg v.2
  have he : pairNormSq v = 0 ↔ v = 0 := by
    rw [pairNormSq, add_eq_zero_iff_of_nonneg h₁ h₂,
      normSq_eq_zero_iff, normSq_eq_zero_iff]
    constructor
    · rintro ⟨h₁,h₂⟩
      exact Prod.ext h₁ h₂
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hn : 0 ≤ pairNormSq v := add_nonneg h₁ h₂
  constructor
  · intro h hz
    exact (ne_of_gt h) (he.mpr hz)
  · intro h
    have hne : pairNormSq v ≠ 0 := fun hz => h (he.mp hz)
    omega
end Semantics

/-- Trial division is polynomial because `q` is stored in unary. -/
def primeCheck (q : ℕ) : Bool :=
  decide (2 ≤ q) && (List.range q).all (fun d => decide (d < 2 ∨ q % d ≠ 0))

theorem primeCheck_eq (q : ℕ) : primeCheck q = true ↔ q.Prime := by
  rw [primeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Nat.prime_def_lt']
  simp only [List.mem_range, decide_eq_true_eq, Nat.dvd_iff_mod_eq_zero]
  constructor
  · rintro ⟨hq, hd⟩
    exact ⟨hq, fun d hd₂ hdq => (hd d hdq).resolve_left (by omega)⟩
  · rintro ⟨hq, hd⟩
    exact ⟨hq, fun d hdq => by by_cases hh : d < 2; exact Or.inl hh; exact Or.inr (hd d (by omega) hdq)⟩

/-- Integral determinant in the prime power basis. -/
def det (q : ℕ) (a b : List ℤ × List ℤ) : List ℤ :=
  sub q (mul q a.1 b.2) (mul q a.2 b.1)

theorem det_eq {q : ℕ} [NeZero q] (a b : List ℤ × List ℤ) :
    powerElement (q := q) (det q a b) = determinant (powerPair a) (powerPair b) := by
  simp only [det, powerElement_sub, powerElement_mul, determinant, powerPair]

/-- All syntactic and algebraic promises are checked, including malformed dimensions. -/
def wellFormedCheck (x : SVPInput) : Bool :=
  primeCheck x.q && decide (x.q % 4 = 3) &&
    decide (x.m₁.1.length = x.q-1) && decide (x.m₁.2.length = x.q-1) &&
    decide (x.m₂.1.length = x.q-1) && decide (x.m₂.2.length = x.q-1) &&
    decide (norm x.q (det x.q x.m₁ x.m₂) ≠ 0) && decide (0 ≤ x.threshold)

theorem wellFormedCheck_eq (x : SVPInput) : wellFormedCheck x = true ↔ x.WellFormed := by
  simp only [wellFormedCheck, Bool.and_eq_true, decide_eq_true_eq, primeCheck_eq, and_assoc]
  constructor
  · rintro ⟨hp, hmod, h₁, h₂, h₃, h₄, hdet, hS⟩
    letI : NeZero x.q := ⟨hp.ne_zero⟩
    refine ⟨hp, hmod, h₁, h₂, h₃, h₄, ?_, hS⟩
    simpa only [norm_eq, ne_eq, normSq_eq_zero_iff, det_eq] using hdet
  · rintro ⟨hp, hmod, h₁, h₂, h₃, h₄, hdet, hS⟩
    letI : NeZero x.q := ⟨hp.ne_zero⟩
    refine ⟨hp, hmod, h₁, h₂, h₃, h₄, ?_, hS⟩
    simpa only [norm_eq, ne_eq, normSq_eq_zero_iff, det_eq] using hdet

/-- Reconstruct a vector from two power-basis ring multipliers. -/
def product (x : SVPInput) (c : List ℤ × List ℤ) : List ℤ × List ℤ :=
  (add x.q (mul x.q c.1 x.m₁.1) (mul x.q c.2 x.m₂.1),
   add x.q (mul x.q c.1 x.m₁.2) (mul x.q c.2 x.m₂.2))

theorem product_eq (x : SVPInput) [NeZero x.q] (c : List ℤ × List ℤ) :
    powerPair (q := x.q) (product x c) = moduleVector (q := x.q) (powerPair x.m₁) (powerPair x.m₂)
      (powerElement c.1) (powerElement c.2) := by
  simp only [powerPair, product, powerElement_add, powerElement_mul, moduleVector]

/-- A total, executable SVP certificate checker. -/
def verifier (p : SVPInput × (List ℤ × List ℤ)) : Bool :=
  wellFormedCheck p.1 && decide (p.2.1.length = p.1.q-1) &&
    decide (p.2.2.length = p.1.q-1) && decide (0 < pairNorm p.1.q (product p.1 p.2)) &&
    decide (pairNorm p.1.q (product p.1 p.2) ≤ p.1.threshold)

theorem verifier_spec (x : SVPInput) (hw : x.WellFormed) (c : List ℤ × List ℤ) :
    verifier (x,c) = true ↔
      letI : NeZero x.q := ⟨(SVPInput.prime hw).ne_zero⟩
      c.1.length = x.q-1 ∧ c.2.length = x.q-1 ∧
        moduleVector (q := x.q) (powerPair x.m₁) (powerPair x.m₂)
          (powerElement c.1) (powerElement c.2) ≠ 0 ∧
        pairNormSq (moduleVector (q := x.q) (powerPair x.m₁) (powerPair x.m₂)
          (powerElement c.1) (powerElement c.2)) ≤ x.threshold := by
  letI : NeZero x.q := ⟨(SVPInput.prime hw).ne_zero⟩
  simp only [verifier, Bool.and_eq_true, decide_eq_true_eq, wellFormedCheck_eq,
    pairNorm_eq, pairNormSq_pos_iff, product_eq, and_assoc, hw, true_and]

/-- Exact verifier characterization of the semantic language, without resource assumptions. -/
theorem moduleSVP_iff_exists_check (x : SVPInput) :
    x ∈ ModuleSVPLang ↔ ∃ c, verifier (x,c) = true := by
  constructor
  · rintro ⟨hw, z, w, hv, hn⟩
    letI : NeZero x.q := ⟨(SVPInput.prime hw).ne_zero⟩
    obtain ⟨a, ha⟩ := classOf_surjective z
    obtain ⟨b, hb⟩ := classOf_surjective w
    refine ⟨(repr a, repr b), (verifier_spec x hw _).mpr ?_⟩
    simpa only [length_repr, powerElement_repr, ha, hb] using
      (show (x.q-1 = x.q-1) ∧ (x.q-1 = x.q-1) ∧ _ from ⟨rfl, rfl, hv, hn⟩)
  · rintro ⟨c, hc⟩
    have hw : x.WellFormed := by
      have hh := hc
      simp only [verifier, Bool.and_eq_true] at hh
      exact (wellFormedCheck_eq x).mp hh.1.1.1.1
    letI : NeZero x.q := ⟨(SVPInput.prime hw).ne_zero⟩
    obtain ⟨_, _, hv, hn⟩ := (verifier_spec x hw c).mp hc
    exact ⟨hw, powerElement c.1, powerElement c.2, hv, hn⟩

end Rank2ModuleSVP.Membership
