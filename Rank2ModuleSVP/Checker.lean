import Rank2ModuleSVP.CheckerAux
import IdealCVP.Sidon
import IdealCVP.X3C

/-! The separated-offset X3C checker, in coefficient coordinates. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

namespace Rank2ModuleSVP.Checker
open scoped BigOperators
open Rank2ModuleSVP
noncomputable section

/-- Incidences retain the indices of repeated sets in the X3C input. -/
abbrev Incidence (I : IdealCVP.X3CInstance) :=
  Σ j : Fin I.n, {i : Fin (3*I.q) // i ∈ I.triples j}

variable (I : IdealCVP.X3CInstance)

instance incidenceFintype : Fintype (Incidence I) := inferInstance

def W : ℕ := Fintype.card (Incidence I)

theorem incidence_count : W I = 3*I.n := by
  classical
  simp [W, Incidence, Fintype.card_sigma, I.triple_card, Nat.mul_comm]

theorem rows_le_incidence_count
    (hcover : ∀ i : Fin (3*I.q), ∃ j, i ∈ I.triples j) : 3*I.q ≤ W I := by
  classical
  let f : Fin (3*I.q) → Incidence I := fun i =>
    ⟨(hcover i).choose, ⟨i, (hcover i).choose_spec⟩⟩
  have hf : Function.Injective f := by
    intro i j h
    exact congrArg (fun e : Incidence I => e.2.val) h
  simpa only [Fintype.card_fin, W] using Fintype.card_le_of_injective f hf

private theorem incidence_ext {e f : Incidence I}
    (hc : e.1 = f.1) (hr : e.2.val = f.2.val) : e = f := by
  rcases e with ⟨j,i,hi⟩
  rcases f with ⟨k,r,hr'⟩
  dsimp at hc hr
  subst k
  subst r
  rfl

/-- The exact last (and largest) Sidon witness position α⋆. -/
def alphaStar (p : IdealCVP.SidonPositions I.n) : ℕ :=
  p.α ⟨I.n-1, by have := I.n_pos; omega⟩

theorem alpha_le_alphaStar (p : IdealCVP.SidonPositions I.n) (j : Fin I.n) :
    p.α j ≤ alphaStar I p := by
  apply p.strictMono.monotone
  change j.val ≤ I.n-1
  have := j.isLt
  omega

def tau (p : IdealCVP.SidonPositions I.n) : ℕ := 2*(alphaStar I p)+1

def beta (p : IdealCVP.SidonPositions I.n) (i : Fin (3*I.q)) : ℤ :=
  (tau I p : ℤ) * (i.val+1)

def offsetInt (p : IdealCVP.SidonPositions I.n) (e : Incidence I) : ℤ :=
  beta I p e.2.val - p.α e.1

def d {q : ℕ} (p : IdealCVP.SidonPositions I.n) (e : Incidence I) : ZMod q :=
  (offsetInt I p e : ZMod q)

def D_wit {q : ℕ} (p : IdealCVP.SidonPositions I.n) : Finset (ZMod q) := by
  classical
  exact ((Finset.univ : Finset (Fin I.n × Fin I.n)).filter
    (fun t => t.1 ≠ t.2)).image (fun t => (p.α t.2 : ZMod q) - (p.α t.1 : ZMod q))

def D_bad {q : ℕ} (p : IdealCVP.SidonPositions I.n) : Finset (ZMod q) := by
  classical
  let es := (Finset.univ : Finset (Incidence I × Incidence I))
  exact ((es.filter (fun t => t.1.2.val ≠ t.2.2.val)).image
    (fun t => d I p t.1 - d I p t.2)) ∪
    (es.image (fun t => d I p t.1 + d I p t.2))

theorem bad_card_bound {q : ℕ} (p : IdealCVP.SidonPositions I.n) :
    (D_bad (q := q) I p).card ≤ 2*(W I)^2 := by
  classical
  apply (Finset.card_union_le _ _).trans
  have h₁ := Finset.card_image_le (s := (Finset.univ : Finset
    (Incidence I × Incidence I)).filter (fun t => t.1.2.val ≠ t.2.2.val))
    (f := fun t => d (q := q) I p t.1 - d I p t.2)
  have h₂ := Finset.card_image_le (s := (Finset.univ : Finset
    (Incidence I × Incidence I)))
    (f := fun t => d (q := q) I p t.1 + d I p t.2)
  have h₃ := Finset.card_filter_le (s := (Finset.univ : Finset
    (Incidence I × Incidence I))) (p := fun t => t.1.2.val ≠ t.2.2.val)
  simp only [Finset.card_univ, Fintype.card_prod] at h₁ h₂ h₃
  dsimp [D_bad]
  unfold W
  nlinarith

theorem offset_bounds (p : IdealCVP.SidonPositions I.n) (e : Incidence I) :
    ((alphaStar I p) : ℤ)+1 ≤ offsetInt I p e ∧
    offsetInt I p e ≤ (tau I p : ℤ)*(3*I.q) := by
  have ha : (p.α e.1 : ℤ) ≤ (alphaStar I p) := by exact_mod_cast alpha_le_alphaStar I p e.1
  have hi := e.2.val.isLt
  have hi' : (e.2.val.val : ℤ)+1 ≤ 3*I.q := by exact_mod_cast hi
  have hτ : (tau I p : ℤ) = 2*(alphaStar I p)+1 := by simp [tau]
  dsimp [offsetInt, beta]
  constructor
  · rw [hτ]; nlinarith [Nat.cast_nonneg (α := ℤ) e.2.val.val]
  · have := mul_le_mul_of_nonneg_left hi' (show (0 : ℤ) ≤ tau I p by positivity)
    nlinarith [Nat.cast_nonneg (α := ℤ) (p.α e.1)]

private theorem intCast_inj_short {q : ℕ} {a b : ℤ}
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


theorem offsetInt_injective (p : IdealCVP.SidonPositions I.n) :
    Function.Injective (offsetInt I p) := by
  intro e f hef
  have he := alpha_le_alphaStar I p e.1
  have hf := alpha_le_alphaStar I p f.1
  have hτ : (tau I p : ℤ) = 2*(alphaStar I p)+1 := by simp [tau]
  have hr : e.2.val = f.2.val := by
    apply Fin.ext
    have := Nat.cast_nonneg (α := ℤ) (p.α e.1)
    have := Nat.cast_nonneg (α := ℤ) (p.α f.1)
    have he' : (p.α e.1 : ℤ) ≤ (alphaStar I p) := by exact_mod_cast he
    have hf' : (p.α f.1 : ℤ) ≤ (alphaStar I p) := by exact_mod_cast hf
    dsimp [offsetInt, beta] at hef
    rw [hτ] at hef
    by_contra hn
    have hn' : (e.2.val.val : ℤ) ≠ f.2.val.val := by exact_mod_cast hn
    rcases lt_or_gt_of_ne hn' with h | h
    · have hh : (e.2.val.val : ℤ)+1 ≤ f.2.val.val := by omega
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2*(alphaStar I p)+1 by positivity)
        (show (0 : ℤ) ≤ f.2.val.val-e.2.val.val-1 by omega)]
    · have hh : (f.2.val.val : ℤ)+1 ≤ e.2.val.val := by omega
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2*(alphaStar I p)+1 by positivity)
        (show (0 : ℤ) ≤ e.2.val.val-f.2.val.val-1 by omega)]
  have hc : e.1 = f.1 := by
    apply p.strictMono.injective
    dsimp [offsetInt] at hef
    rw [hr] at hef
    exact_mod_cast (show (p.α e.1 : ℤ) = p.α f.1 by omega)
  exact incidence_ext I hc hr

private theorem cross_difference_large (p : IdealCVP.SidonPositions I.n)
    (e f : Incidence I) (h : e.2.val ≠ f.2.val) :
    ((alphaStar I p) : ℤ) < offsetInt I p e - offsetInt I p f ∨
      offsetInt I p e - offsetInt I p f < -((alphaStar I p) : ℤ) := by
  have he : (p.α e.1 : ℤ) ≤ (alphaStar I p) := by exact_mod_cast alpha_le_alphaStar I p e.1
  have hf : (p.α f.1 : ℤ) ≤ (alphaStar I p) := by exact_mod_cast alpha_le_alphaStar I p f.1
  have he0 := Nat.cast_nonneg (α := ℤ) (p.α e.1)
  have hf0 := Nat.cast_nonneg (α := ℤ) (p.α f.1)
  have hn : (e.2.val.val : ℤ) ≠ f.2.val.val := by
    intro hh; apply h; apply Fin.ext; exact_mod_cast hh
  have hτ : (tau I p : ℤ) = 2*(alphaStar I p)+1 := by simp [tau]
  dsimp [offsetInt, beta]
  rw [hτ]
  rcases lt_or_gt_of_ne hn with h | h
  · right
    have hm := mul_nonneg (show (0 : ℤ) ≤ 2*(alphaStar I p)+1 by positivity)
      (show (0 : ℤ) ≤ f.2.val.val-e.2.val.val-1 by omega)
    nlinarith
  · left
    have hm := mul_nonneg (show (0 : ℤ) ≤ 2*(alphaStar I p)+1 by positivity)
      (show (0 : ℤ) ≤ e.2.val.val-f.2.val.val-1 by omega)
    nlinarith

/-- The two signed offsets for each incidence are nonzero and all distinct. -/
theorem row_shift_signed_separation {q : ℕ} (p : IdealCVP.SidonPositions I.n)
    (hq : 4*tau I p*(3*I.q) < q) :
    (∀ e : Incidence I, d (q := q) I p e ≠ 0) ∧
    Function.Injective (fun t : Bool × Incidence I =>
      if t.1 then d (q := q) I p t.2 else -d I p t.2) := by
  have hq₀ : 4*(tau I p : ℤ)*(3*I.q) < q := by exact_mod_cast hq
  have hq' : 4*((tau I p : ℤ)*(3*I.q)) < q := by nlinarith [hq₀]
  have hb (e : Incidence I) := offset_bounds I p e
  have hshort (e : Incidence I) : -(q : ℤ) < 2*offsetInt I p e ∧
      2*offsetInt I p e < q := by
    have := hb e
    constructor <;> nlinarith
  constructor
  · intro e he
    have hz : (offsetInt I p e : ZMod q) = (0 : ℤ) := by
      simpa only [d, Int.cast_zero] using he
    have hh := intCast_inj_short (q := q) (hshort e).1 (hshort e).2
      (by omega) (by omega) hz
    have := hb e
    omega
  · rintro ⟨b,e⟩ ⟨c,f⟩ he
    cases b <;> cases c
    · simp only [Bool.false_eq_true, ↓reduceIte, neg_inj] at he
      have hh := intCast_inj_short (q := q) (hshort e).1 (hshort e).2
        (hshort f).1 (hshort f).2 he
      simp [offsetInt_injective I p hh]
    · simp only [Bool.false_eq_true, ↓reduceIte] at he
      have he' : ((-offsetInt I p e : ℤ) : ZMod q) = offsetInt I p f := by
        simpa [d] using he
      have hh := intCast_inj_short (q := q) (a := -offsetInt I p e)
        (by have := hshort e; omega) (by have := hshort e; omega)
        (hshort f).1 (hshort f).2 he'
      have := hb e; have := hb f; omega
    · simp only [Bool.false_eq_true, ↓reduceIte] at he
      have he' : (offsetInt I p e : ZMod q) = (-offsetInt I p f : ℤ) := by
        simpa [d] using he
      have hh := intCast_inj_short (q := q) (hshort e).1 (hshort e).2
        (by have := hshort f; omega) (by have := hshort f; omega) he'
      have := hb e; have := hb f; omega
    · simp only [↓reduceIte] at he
      have hh := intCast_inj_short (q := q) (hshort e).1 (hshort e).2
        (hshort f).1 (hshort f).2 he
      simp [offsetInt_injective I p hh]

private theorem bad_representative {q : ℕ} (p : IdealCVP.SidonPositions I.n)
    (z : ZMod q) (hz : z ∈ D_bad I p) :
    ∃ a : ℤ, (a : ZMod q) = z ∧
      -(2*(tau I p : ℤ)*(3*I.q)) ≤ a ∧ a ≤ 2*(tau I p : ℤ)*(3*I.q) ∧
      (((alphaStar I p) : ℤ) < a ∨ a < -((alphaStar I p) : ℤ)) := by
  classical
  simp only [D_bad, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and] at hz
  rcases hz with ⟨⟨e,f⟩, h, rfl⟩ | ⟨⟨e,f⟩, _, rfl⟩
  · refine ⟨offsetInt I p e-offsetInt I p f, by simp [d], ?_, ?_,
      cross_difference_large I p e f h⟩
    all_goals have := offset_bounds I p e; have := offset_bounds I p f; nlinarith
  · refine ⟨offsetInt I p e+offsetInt I p f, by simp [d], ?_, ?_, Or.inl ?_⟩
    all_goals have := offset_bounds I p e; have := offset_bounds I p f; nlinarith

/-- Bad offsets are nonzero and disjoint from every witness offset. -/
theorem row_shift_bad_separation {q : ℕ} (p : IdealCVP.SidonPositions I.n)
    (hq : 4*tau I p*(3*I.q) < q) :
    0 ∉ D_bad (q := q) I p ∧ Disjoint (D_bad (q := q) I p) (D_wit I p) := by
  classical
  have hq₀ : 4*(tau I p : ℤ)*(3*I.q) < q := by exact_mod_cast hq
  have hq' : 4*((tau I p : ℤ)*(3*I.q)) < q := by nlinarith [hq₀]
  have hM : (0 : ℤ) < 3*I.q := by have := I.q_pos; positivity
  have hcB : ((alphaStar I p) : ℤ) ≤ (tau I p : ℤ)*(3*I.q) := by
    have ht : (tau I p : ℤ) = 2*(alphaStar I p)+1 := by simp [tau]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ tau I p by positivity)
      (show (0 : ℤ) ≤ 3*I.q-1 by omega)]
  constructor
  · intro hz
    obtain ⟨a, ha, hlo, hhi, hlarge⟩ := bad_representative I p 0 hz
    have hh := intCast_inj_short (q := q) (a := a) (b := 0)
      (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
      (by simpa only [Int.cast_zero] using ha)
    rcases hlarge with h | h <;> omega
  · apply Finset.disjoint_left.mpr
    intro z hz hw
    obtain ⟨a, ha, hlo, hhi, hlarge⟩ := bad_representative I p z hz
    simp only [D_wit, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hw
    obtain ⟨⟨j,k⟩, _, hk⟩ := hw
    have hj : (p.α j : ℤ) ≤ (alphaStar I p) := by exact_mod_cast alpha_le_alphaStar I p j
    have hk' : (p.α k : ℤ) ≤ (alphaStar I p) := by exact_mod_cast alpha_le_alphaStar I p k
    have hj0 := Nat.cast_nonneg (α := ℤ) (p.α j)
    have hk0 := Nat.cast_nonneg (α := ℤ) (p.α k)
    have he : (a : ZMod q) = ((p.α k : ℤ)-p.α j : ℤ) := by
      rw [ha, ← hk]; simp
    have hh := intCast_inj_short (q := q) (a := a) (b := (p.α k : ℤ)-p.α j)
      (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith) he
    rcases hlarge with h | h <;> omega
/-- Paper lem. row-shift-separation, with an explicit cardinality bound. -/
theorem row_shift_separation {q : ℕ} (p : IdealCVP.SidonPositions I.n)
    (hq : 4*tau I p*(3*I.q) < q) :
    (∀ e : Incidence I, d (q := q) I p e ≠ 0) ∧
    Function.Injective (fun t : Bool × Incidence I =>
      if t.1 then d (q := q) I p t.2 else -d I p t.2) ∧
    0 ∉ D_bad (q := q) I p ∧ Disjoint (D_bad (q := q) I p) (D_wit I p) ∧
    (D_bad (q := q) I p).card ≤ 2*(W I)^2 := by
  obtain ⟨hn,hi⟩ := row_shift_signed_separation I p hq
  obtain ⟨hz,hd⟩ := row_shift_bad_separation I p hq
  exact ⟨hn,hi,hz,hd,bad_card_bound I p⟩


section Correlations
variable {q : ℕ} [NeZero q]

/-- The cyclic correlation at offset d. -/
def correlation (x : Coeff ℚ q) (d : ZMod q) : ℚ := ∑ a, x a*x (a+d)

theorem correlation_neg (x : Coeff ℚ q) (d : ZMod q) :
    correlation x (-d) = correlation x d := by
  have he := Equiv.sum_comp (Equiv.addRight d)
    (fun a => x a*x (a-d))
  change (∑ a, x (a+d)*x (a+d-d)) = ∑ a, x a*x (a-d) at he
  simp only [add_sub_cancel_right] at he
  unfold correlation
  simpa only [sub_eq_add_neg, mul_comm] using he.symm

theorem correlation_shift (x : Coeff ℚ q) (r s : ZMod q) :
    (∑ a, x (a-r)*x (a-s)) = correlation x (r-s) := by
  have he := Equiv.sum_comp (Equiv.addRight r)
    (fun a => x (a-r)*x (a-s))
  change (∑ a, x (a+r-r)*x (a+r-s)) = ∑ a, x (a-r)*x (a-s) at he
  rw [← he]
  simp only [add_sub_cancel_right, add_sub_assoc, correlation]

theorem inner_shift_pair (x : Coeff ℚ q) (r s : ZMod q) :
    inner (monomial r*classOf x) (monomial s*classOf x) =
      (q : ℚ)*correlation x (r-s)-(∑ a, x a)^2 := by
  rw [monomial_mul_classOf, monomial_mul_classOf, inner_classOf]
  have hs (b : ZMod q) : (∑ a, x (a-b)) = ∑ a, x a :=
    Equiv.sum_comp (Equiv.subRight b) x
  simp only [canonicalForm, shiftCoeff, correlation_shift, hs, pow_two]

theorem correlation_zero_binary (x : Coeff ℚ q) (hx : ∀ a, x a = 0 ∨ x a = 1) :
    correlation x 0 = ∑ a, x a := by
  apply Finset.sum_congr rfl
  intro a _
  rcases hx a with h | h <;> simp [h]

/-- Eq. enhanced-clean-correlations, including every ordered witness pair. -/
def Clean (p : IdealCVP.SidonPositions I.n) (x : Coeff ℚ q) : Prop :=
  (∀ j k : Fin I.n, j ≠ k →
    correlation x ((p.α k : ZMod q)-(p.α j : ZMod q)) = x (p.α j)*x (p.α k)) ∧
  (∀ d ∈ D_bad (q := q) I p, correlation x d = 0)

/-- Eq. checker-additional-correlations. Incidence pairs are ordered. The
same-row and cross-row parts are written as a single conditional sum. -/
def E (p : IdealCVP.SidonPositions I.n) (x : Coeff ℚ q) : ℚ :=
  2*(∑ e : Incidence I, ∑ f : Incidence I,
    if e = f then 0 else
      if e.2.val = f.2.val then
        correlation x (d I p e-d I p f)-x (p.α e.1)*x (p.α f.1)
      else correlation x (d I p e-d I p f)) +
  2*(∑ e : Incidence I, ∑ f : Incidence I,
    correlation x (d I p e+d I p f))

theorem correlation_nonneg (x : Coeff ℚ q) (hx : ∀ a, 0 ≤ x a) (d : ZMod q) :
    0 ≤ correlation x d :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (hx _) (hx _))

theorem witness_product_le_correlation (x : Coeff ℚ q) (hx : ∀ a, 0 ≤ x a)
    (a b : ZMod q) : x a*x b ≤ correlation x (b-a) := by
  have hh := Finset.single_le_sum
    (s := (Finset.univ : Finset (ZMod q)))
    (f := fun t => x t*x (t+(b-a)))
    (fun t _ => mul_nonneg (hx t) (hx _)) (Finset.mem_univ a)
  rw [show a+(b-a) = b by abel] at hh
  exact hh


theorem same_row_difference (p : IdealCVP.SidonPositions I.n)
    (e f : Incidence I) (h : e.2.val = f.2.val) :
    d (q := q) I p e-d I p f = (p.α f.1 : ZMod q)-(p.α e.1 : ZMod q) := by
  dsimp [d, offsetInt]
  rw [h]
  push_cast
  ring

theorem E_nonneg (p : IdealCVP.SidonPositions I.n) (x : Coeff ℚ q)
    (hx : ∀ a, 0 ≤ x a) : 0 ≤ E I p x := by
  classical
  unfold E
  apply add_nonneg
  · apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro e _
    apply Finset.sum_nonneg
    intro f _
    split_ifs with hef hr
    · exact le_rfl
    · rw [same_row_difference I p e f hr]
      exact sub_nonneg.mpr (witness_product_le_correlation x hx _ _)
    · exact correlation_nonneg x hx _
  · apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun e _ => Finset.sum_nonneg
      (fun f _ => correlation_nonneg x hx _))

theorem E_nonneg_binary (p : IdealCVP.SidonPositions I.n) (x : Coeff ℚ q)
    (hx : ∀ a, x a = 0 ∨ x a = 1) : 0 ≤ E I p x := by
  apply E_nonneg I p x
  intro a
  rcases hx a with h | h <;> simp [h]

theorem E_eq_zero_of_clean (p : IdealCVP.SidonPositions I.n) (x : Coeff ℚ q)
    (hx : Clean I p x) : E I p x = 0 := by
  classical
  have hd (e f : Incidence I) (hr : e.2.val ≠ f.2.val) :
      correlation x (d I p e-d I p f) = 0 := by
    apply hx.2
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨(e,f), by simp [hr], rfl⟩
  have hs (e f : Incidence I) : correlation x (d I p e+d I p f) = 0 := by
    apply hx.2
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨(e,f), Finset.mem_univ _, rfl⟩
  unfold E
  have hz (e f : Incidence I) :
      (if e = f then 0 else if e.2.val = f.2.val then
        correlation x (d I p e-d I p f)-x (p.α e.1)*x (p.α f.1)
        else correlation x (d I p e-d I p f)) = 0 := by
    split_ifs with hef hr
    · rfl
    · rw [same_row_difference I p e f hr,
        hx.1 e.1 f.1 (fun hc => hef (incidence_ext I hc hr)), sub_self]
    · exact hd e f hr
  simp only [hz, hs, Finset.sum_const_zero, mul_zero, add_zero]

/-- The rational image of the v2 quadratic checker g (retaining the useful
legacy name p). No separation hypothesis is needed for the algebraic identities. -/
def p (s : IdealCVP.SidonPositions I.n) : RationalRing q :=
  ∑ e : Incidence I, (monomial (d I s e)+monomial (-d I s e))

/-- The incidence row sum (Aξ)ᵢ. -/
def rowValue (s : IdealCVP.SidonPositions I.n) (x : Coeff ℚ q)
    (i : Fin (3*I.q)) : ℚ :=
  ∑ e : Incidence I, if e.2.val = i then x (s.α e.1) else 0

theorem rowValue_sum (s : IdealCVP.SidonPositions I.n) (x : Coeff ℚ q) :
    (∑ i, rowValue I s x i) = ∑ e : Incidence I, x (s.α e.1) := by
  classical
  unfold rowValue
  rw [Finset.sum_comm]
  simp

theorem incidence_selection_sum (s : IdealCVP.SidonPositions I.n) (x : Coeff ℚ q) :
    (∑ e : Incidence I, x (s.α e.1)) = 3*(∑ j, x (s.α j)) := by
  classical
  simp [Incidence, Fintype.sum_sigma, I.triple_card, ← Finset.mul_sum]

theorem rowValue_sq_sum (s : IdealCVP.SidonPositions I.n) (x : Coeff ℚ q) :
    (∑ i, (rowValue I s x i)^2) =
      ∑ e : Incidence I, ∑ f : Incidence I,
        if e.2.val = f.2.val then x (s.α e.1)*x (s.α f.1) else 0 := by
  classical
  have he (e f : Incidence I) :
      (∑ i : Fin (3*I.q),
        (if e.2.val = i then x (s.α e.1) else 0)*
        (if f.2.val = i then x (s.α f.1) else 0)) =
      if e.2.val = f.2.val then x (s.α e.1)*x (s.α f.1) else 0 := by
    by_cases h : e.2.val = f.2.val <;> simp [h, eq_comm, ite_mul]
  unfold rowValue
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext e; rw [Finset.sum_comm]
  simp_rw [he]
  exact Finset.sum_comm

theorem quadratic_incidence_identity (s : IdealCVP.SidonPositions I.n)
    (x : Coeff ℚ q) (hx : ∀ a, x a = 0 ∨ x a = 1) :
    (∑ e : Incidence I, ∑ f : Incidence I,
      if e = f then 0 else if e.2.val = f.2.val then
        x (s.α e.1)*x (s.α f.1) else 0) =
      ∑ i, ((rowValue I s x i)^2-rowValue I s x i) := by
  classical
  have he (e f : Incidence I) :
      (if e.2.val = f.2.val then x (s.α e.1)*x (s.α f.1) else 0) =
      (if e = f then x (s.α e.1) else 0)+
      (if e = f then 0 else if e.2.val = f.2.val then
        x (s.α e.1)*x (s.α f.1) else 0) := by
    by_cases h : e = f
    · subst f
      rcases hx (s.α e.1) with hh | hh <;> simp [hh]
    · simp [h]
  have hh := rowValue_sq_sum I s x
  have hd : (∑ e : Incidence I, ∑ f : Incidence I,
      if e.2.val = f.2.val then x (s.α e.1)*x (s.α f.1) else 0) =
      ∑ e : Incidence I, ∑ f : Incidence I,
        ((if e = f then x (s.α e.1) else 0)+
        (if e = f then 0 else if e.2.val = f.2.val then
          x (s.α e.1)*x (s.α f.1) else 0)) := by
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    exact he e f
  rw [hd] at hh
  simp only [Finset.sum_add_distrib] at hh
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at hh
  rw [Finset.sum_sub_distrib, rowValue_sum]
  linarith

theorem correlations_decomposition (s : IdealCVP.SidonPositions I.n)
    (x : Coeff ℚ q) (hx : ∀ a, x a = 0 ∨ x a = 1) :
    2*(∑ e : Incidence I, ∑ f : Incidence I, correlation x (d I s e-d I s f))+
      2*(∑ e : Incidence I, ∑ f : Incidence I, correlation x (d I s e+d I s f)) =
    2*(W I : ℚ)*(∑ a, x a)+
      2*(∑ i, ((rowValue I s x i)^2-rowValue I s x i))+E I s x := by
  classical
  have he (e f : Incidence I) : correlation x (d I s e-d I s f) =
      (if e = f then (∑ a, x a) else 0)+
      (if e = f then 0 else if e.2.val = f.2.val then
        x (s.α e.1)*x (s.α f.1) else 0)+
      (if e = f then 0 else if e.2.val = f.2.val then
        correlation x (d I s e-d I s f)-x (s.α e.1)*x (s.α f.1)
        else correlation x (d I s e-d I s f)) := by
    by_cases h : e = f
    · subst f; simp [correlation_zero_binary x hx]
    · simp only [h, ↓reduceIte, zero_add]
      split_ifs <;> ring
  have hh := congrArg (fun f : Incidence I → Incidence I → ℚ => ∑ e, ∑ t, f e t)
    (funext fun e => funext fun f => he e f)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, W] at hh
  rw [quadratic_incidence_identity I s x hx] at hh
  unfold E W
  linarith

theorem p_norm_correlations (s : IdealCVP.SidonPositions I.n) (x : Coeff ℚ q) :
    normSq (p (q := q) I s*classOf x) =
      (q : ℚ)*(2*(∑ e : Incidence I, ∑ f : Incidence I,
        correlation x (d I s e-d I s f))+
      2*(∑ e : Incidence I, ∑ f : Incidence I,
        correlation x (d I s e+d I s f)))-
      4*(W I : ℚ)^2*(∑ a, x a)^2 := by
  classical
  have hpair (e f : Incidence I) :
      inner ((monomial (d I s e)+monomial (-d I s e))*classOf x)
        ((monomial (d I s f)+monomial (-d I s f))*classOf x) =
      (q : ℚ)*(2*correlation x (d I s e-d I s f)+
        2*correlation x (d I s e+d I s f))-4*(∑ a, x a)^2 := by
    simp only [add_mul, inner_add_left, inner_add_right, inner_shift_pair]
    rw [show -(d (q := q) I s e)-d I s f = -(d I s e+d I s f) by abel,
      show -(d (q := q) I s e)-(-d I s f) = -(d I s e-d I s f) by abel,
      show d (q := q) I s e-(-d I s f) = d I s e+d I s f by abel]
    simp only [correlation_neg]
    ring
  rw [p, Finset.sum_mul, ← inner_self, inner_sum_left]
  simp_rw [inner_sum_right, hpair]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, W]
  ring

theorem p_conjugate (s : IdealCVP.SidonPositions I.n) :
    conjugate (p (q := q) I s) = p (q := q) I s := by
  classical
  simp only [p, conjugate_sum, conjugate_add, conjugate_monomial, neg_neg]
  congr 1
  funext e
  exact add_comm _ _

theorem binary_norm_rational (x : Coeff ℚ q) (h : ℕ)
    (hx : ∀ a, x a = 0 ∨ x a = 1) (hh : ∑ a, x a = (h : ℚ)) :
    normSq (classOf x) = (h : ℚ)*(q-h) := by
  rw [normSq_classOf, coeffNormSq_eq]
  have hs : (∑ a, x a^2) = ∑ a, x a := by
    apply Finset.sum_congr rfl
    intro a _
    rcases hx a with h | h <;> simp [h]
  rw [hs, hh]
  ring

/-- Section 4.2: the integral, self-conjugate quadratic checker. -/
def g (s : IdealCVP.SidonPositions I.n) : IntegerRing q :=
  ∑ e : Incidence I, (monomial (d I s e)+monomial (-d I s e))

/-- Section 4.2: the integral linear checker. -/
def V (s : IdealCVP.SidonPositions I.n) : IntegerRing q :=
  6 * ∑ j : Fin I.n, monomial (s.α j : ZMod q)

/-- The exact scale in paper v2, Section 4.2. -/
def Q (h : ℕ) : ℕ := 128*(W I)^4*h

/-- The v2 checker is integral and works for every odd prime. -/
def U (s : IdealCVP.SidonPositions I.n) (h : ℕ) : IntegerRing q :=
  (Q I h : IntegerRing q) + (g I s)^2

def gQ (s : IdealCVP.SidonPositions I.n) : RationalRing q := rationalize (g I s)
def VQ (s : IdealCVP.SidonPositions I.n) : RationalRing q := rationalize (V I s)
def UQ (s : IdealCVP.SidonPositions I.n) (h : ℕ) : RationalRing q :=
  rationalize (U I s h)

@[simp] theorem gQ_eq_p (s : IdealCVP.SidonPositions I.n) :
    gQ (q := q) I s = p I s := by simp [gQ, g, p]

@[simp] theorem VQ_eq (s : IdealCVP.SidonPositions I.n) :
    VQ (q := q) I s = (6 : ℚ) • ∑ j : Fin I.n, monomial (s.α j : ZMod q) := by
  rw [show (6 : ℚ) = ((6 : ℕ) : ℚ) by norm_num,
    Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  simp only [VQ, V, map_mul, map_ofNat, map_sum, rationalize_monomial, Nat.cast_ofNat]

theorem UQ_eq (s : IdealCVP.SidonPositions I.n) (h : ℕ) :
    UQ (q := q) I s h = positiveChecker (Q I h) (p I s) := by
  unfold UQ U positiveChecker
  rw [map_add, map_natCast, map_pow, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
  rw [show rationalize (g (q := q) I s) = p I s from gQ_eq_p I s]

theorem g_conjugate (s : IdealCVP.SidonPositions I.n) :
    conjugate (g (q := q) I s) = g I s := by
  classical
  simp only [g, conjugate_sum, conjugate_add, conjugate_monomial, neg_neg]
  congr 1
  funext e
  exact add_comm _ _

theorem W_ge_three : 3 ≤ W I := by rw [incidence_count]; have := I.n_pos; omega

theorem Q_pos (h : ℕ) (hh : 1 ≤ h) : 0 < Q I h := by
  have := W_ge_three I
  unfold Q
  positivity

/-- Lemma 4.2, exact self-adjoint identity for arbitrary elements of K. -/
theorem checker_U_norm_exact (s : IdealCVP.SidonPositions I.n) (h : ℕ)
    (y : RationalRing q) :
    normSq (UQ I s h*y) = (Q I h : ℚ)^2*normSq y +
      2*(Q I h : ℚ)*normSq (p I s*y) + normSq ((p I s)^2*y) := by
  rw [UQ_eq]
  exact positiveChecker_norm_exact _ _ _ (p_conjugate I s)

/-- Lemma 4.2, U bound on all of K. -/
theorem checker_U_norm_lower (s : IdealCVP.SidonPositions I.n) (h : ℕ)
    (y : RationalRing q) :
    (Q I h : ℚ)^2*normSq y ≤ normSq (UQ I s h*y) := by
  rw [UQ_eq]
  exact positiveChecker_norm_lower _ (Nat.cast_nonneg _) _ _ (p_conjugate I s)

/-- The g bound uses exactly 2W monomial isometries. -/
theorem checker_g_norm_bound (s : IdealCVP.SidonPositions I.n) (w : RationalRing q) :
    normSq (p I s*w) ≤ (2*(W I : ℚ))^2*normSq w := by
  classical
  let a : Bool × Incidence I → ZMod q := fun t => if t.1 then d I s t.2 else -d I s t.2
  have he : p (q := q) I s = ∑ t : Bool × Incidence I, monomial (a t) := by
    simp [p, a, Fintype.sum_prod_type, Finset.sum_add_distrib, add_comm]
  rw [he]
  simpa [W, Fintype.card_prod] using normSq_sum_monomial_mul_le Finset.univ a w

/-- Lemma 4.2, V bound on all of K; its total monomial weight is 6n = 2W. -/
theorem checker_V_norm_bound (s : IdealCVP.SidonPositions I.n) (w : RationalRing q) :
    normSq (VQ I s*w) ≤ (2*(W I : ℚ))^2*normSq w := by
  rw [VQ_eq, smul_mul_assoc, normSq_smul]
  have hh := normSq_sum_monomial_mul_le (Finset.univ : Finset (Fin I.n))
    (fun j => (s.α j : ZMod q)) w
  have hW : (W I : ℚ) = 3*(I.n : ℚ) := by exact_mod_cast incidence_count I
  simp only [Finset.card_univ, Fintype.card_fin] at hh
  rw [hW]
  nlinarith

/-- Lemma 4.2, integral U corollary. -/
theorem checker_U_norm_lower_int (s : IdealCVP.SidonPositions I.n) (h : ℕ)
    (y : IntegerRing q) :
    (Q I h : ℤ)^2*normSq y ≤ normSq (U I s h*y) := by
  have hh := checker_U_norm_lower I s h (rationalize y)
  change (Q I h : ℚ)^2*normSq (rationalize y) ≤
    normSq (rationalize (U I s h)*rationalize y) at hh
  rw [← map_mul, normSq_rationalize, normSq_rationalize] at hh
  exact_mod_cast hh

/-- Lemma 4.2, integral V corollary. -/
theorem checker_V_norm_bound_int (s : IdealCVP.SidonPositions I.n) (w : IntegerRing q) :
    normSq (V I s*w) ≤ (2*(W I : ℤ))^2*normSq w := by
  have hh := checker_V_norm_bound I s (rationalize w)
  change normSq (rationalize (V I s)*rationalize w) ≤ _ at hh
  rw [← map_mul, normSq_rationalize, normSq_rationalize] at hh
  exact_mod_cast hh

/-- The coefficient κ in Equations (17)--(18). -/
def kappa (h : ℕ) : ℚ := 2*q/(Q I h)

/-- The nonnegative remainder in Equation (17). -/
def remainder (s : IdealCVP.SidonPositions I.n) (h : ℕ) (x : Coeff ℚ q) : ℚ :=
  normSq ((p I s)^2*classOf x-VQ I s)/(Q I h : ℚ)^2

/-- The baseline in paper v2, Equation (18), independent of x. -/
def B₀ (h : ℕ) : ℚ :=
  (h : ℚ)*(q-h) + kappa I (q := q) h *
    (2*(W I)*h-2*(3*I.q)+(2*(h : ℚ)*(W I)-4*h^2*(W I)^2)/q)

/-- The linear term in the v2 checker formula. -/
theorem linear_checker_inner_v2 (s : IdealCVP.SidonPositions I.n) (x : Coeff ℚ q) :
    inner (classOf x) (VQ I s) =
      2*(q : ℚ)*(∑ i, rowValue I s x i)-2*(∑ a, x a)*(W I) := by
  rw [VQ_eq, inner_smul_right, inner_sum_right]
  simp_rw [inner_classOf_monomial]
  rw [rowValue_sum, incidence_selection_sum, incidence_count]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- Theorem 4.3, Equation (17), with the explicit nonnegative E from (19). -/
theorem checker_score (s : IdealCVP.SidonPositions I.n)
    (x : Coeff ℚ q) (h : ℕ) (hx : ∀ a, x a = 0 ∨ x a = 1)
    (hh : ∑ a, x a = (h : ℚ)) (hhpos : 1 ≤ h) :
    normSq (UQ I s h*classOf x-VQ I s)/(Q I h : ℚ)^2 =
      B₀ (q := q) I h + 2*kappa I (q := q) h*(∑ i, (rowValue I s x i-1)^2) +
        kappa I (q := q) h*E I s x + remainder I s h x := by
  rw [UQ_eq, positiveChecker_value_norm _ _ _ _ (p_conjugate I s),
    binary_norm_rational x h hx hh, p_norm_correlations,
    correlations_decomposition I s x hx, linear_checker_inner_v2]
  unfold B₀ kappa remainder
  rw [hh]
  simp only [Finset.sum_sub_distrib, sub_sq, one_pow, mul_one,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hQ0 : (Q I h : ℚ) ≠ 0 := by exact_mod_cast (Q_pos I h hhpos).ne'
  field_simp
  <;> ring

theorem remainder_nonneg (s : IdealCVP.SidonPositions I.n) (h : ℕ)
    (x : Coeff ℚ q) : 0 ≤ remainder I s h x :=
  div_nonneg (normSq_nonneg _) (sq_nonneg _)

/-- Theorem 4.3's uniform strict remainder estimate. -/
theorem remainder_lt (s : IdealCVP.SidonPositions I.n) (x : Coeff ℚ q) (h : ℕ)
    (hx : ∀ a, x a = 0 ∨ x a = 1) (hh : ∑ a, x a = (h : ℚ))
    (hhpos : 1 ≤ h) : remainder I s h x < kappa I (q := q) h/8 := by
  have hW : (3 : ℚ) ≤ W I := by exact_mod_cast W_ge_three I
  have hh' : (1 : ℚ) ≤ h := by exact_mod_cast hhpos
  have hq : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hQ : (0 : ℚ) < Q I h := by exact_mod_cast Q_pos I h hhpos
  have hg := checker_g_norm_bound I s (p I s*classOf x)
  have hg' := checker_g_norm_bound I s (classOf x)
  rw [binary_norm_rational x h hx hh] at hg'
  have hH : (h : ℚ)*(q-h) ≤ h*q := by nlinarith [sq_nonneg (h : ℚ)]
  have hgg : normSq ((p I s)^2*classOf x) ≤ 16*(W I : ℚ)^4*h*q := by
    have hm := mul_le_mul_of_nonneg_left hg' (sq_nonneg (2*(W I : ℚ)))
    have hm' := mul_le_mul_of_nonneg_left hH (show 0 ≤ (2*(W I : ℚ))^4 by positivity)
    rw [show (p (q := q) I s)^2*classOf x = p I s*(p I s*classOf x) by ring]
    nlinarith [hg, hm, hm']
  have hv := checker_V_norm_bound I s (1 : RationalRing q)
  rw [mul_one, normSq_one] at hv
  have hv' : normSq (VQ (q := q) I s) ≤ 4*(W I : ℚ)^2*q := by
    nlinarith [sq_nonneg (W I : ℚ)]
  have hb := normSq_sub_le_three_halves ((p I s)^2*classOf x) (VQ I s)
  have hsmall : 12*(W I : ℚ)^2 < 8*(W I : ℚ)^4*h := by
    have hW2 : (9 : ℚ) ≤ (W I : ℚ)^2 := by nlinarith
    have hWh : (9 : ℚ) ≤ (W I : ℚ)^2*h := by
      nlinarith [mul_le_mul_of_nonneg_left hh' (sq_nonneg (W I : ℚ))]
    have hm := mul_lt_mul_of_pos_right (show (12 : ℚ) < 8*(W I : ℚ)^2*h by linarith)
      (show 0 < (W I : ℚ)^2 by positivity)
    nlinarith [hm]
  have hnum : normSq ((p I s)^2*classOf x-VQ I s) < (q : ℚ)*(Q I h)/4 := by
    have hm := mul_lt_mul_of_pos_right hsmall hq
    have he : (Q I h : ℚ) = 128*(W I : ℚ)^4*h := by simp [Q]
    rw [he]
    nlinarith [hgg, hv', hb, hm]
  unfold remainder kappa
  apply (div_lt_iff₀ (sq_pos_of_pos hQ)).mpr
  have he : (2*(q : ℚ)/(Q I h)/8)*(Q I h : ℚ)^2 = q*(Q I h)/4 := by
    field_simp
    <;> ring
  rw [he]
  exact hnum

/-- Corollary 4.5's lower bound for every binary vector of weight h. -/
theorem checker_lower (s : IdealCVP.SidonPositions I.n)
    (x : Coeff ℚ q) (h : ℕ) (hx : ∀ a, x a = 0 ∨ x a = 1)
    (hh : ∑ a, x a = (h : ℚ)) (hhpos : 1 ≤ h) :
    B₀ (q := q) I h + 2*kappa I (q := q) h*(∑ i, (rowValue I s x i-1)^2) ≤
      normSq (UQ I s h*classOf x-VQ I s)/(Q I h : ℚ)^2 := by
  rw [checker_score I s x h hx hh hhpos]
  have hE := mul_nonneg (show 0 ≤ kappa I (q := q) h by unfold kappa; positivity)
    (E_nonneg_binary I s x hx)
  have hR := remainder_nonneg I s h x
  linarith

/-- Corollary 4.5's upper bound for admissible representatives. -/
theorem checker_upper_of_clean (s : IdealCVP.SidonPositions I.n)
    (x : Coeff ℚ q) (h : ℕ) (hx : ∀ a, x a = 0 ∨ x a = 1)
    (hh : ∑ a, x a = (h : ℚ)) (hhpos : 1 ≤ h) (hc : Clean I s x) :
    normSq (UQ I s h*classOf x-VQ I s)/(Q I h : ℚ)^2 ≤
      B₀ (q := q) I h + 2*kappa I (q := q) h*(∑ i, (rowValue I s x i-1)^2) + kappa I (q := q) h/8 := by
  rw [checker_score I s x h hx hh hhpos, E_eq_zero_of_clean I s x hc]
  have hR := remainder_lt I s x h hx hh hhpos
  linarith

/-- v2 terminology for the preserved correlation conditions (20). -/
abbrev Admissible (s : IdealCVP.SidonPositions I.n) (x : Coeff ℚ q) : Prop := Clean I s x

/-- Theorem 4.3, bundling Equation (17) and both remainder inequalities. -/
theorem checker_score_bounds (s : IdealCVP.SidonPositions I.n)
    (x : Coeff ℚ q) (h : ℕ) (hx : ∀ a, x a = 0 ∨ x a = 1)
    (hh : ∑ a, x a = (h : ℚ)) (hhpos : 1 ≤ h) :
    0 ≤ E I s x ∧
    normSq (UQ I s h*classOf x-VQ I s)/(Q I h : ℚ)^2 =
      B₀ (q := q) I h + 2*kappa I (q := q) h*(∑ i, (rowValue I s x i-1)^2) +
        kappa I (q := q) h*E I s x + remainder I s h x ∧
    0 ≤ remainder I s h x ∧ remainder I s h x < kappa I (q := q) h/8 :=
  ⟨E_nonneg_binary I s x hx, checker_score I s x h hx hh hhpos,
    remainder_nonneg I s h x, remainder_lt I s x h hx hh hhpos⟩

/-- An explicit integer equal to Q²B₀. -/
def baselineNumerator (h : ℕ) : ℤ :=
  (Q I h : ℤ)^2*h*((q : ℤ)-h) +
    2*q*(Q I h)*(2*(W I)*h-2*(3*I.q)) +
    2*(Q I h)*(2*(h : ℤ)*(W I)-4*h^2*(W I)^2)

/-- The integrality identity needed for the threshold S in Section 5. -/
theorem baseline_scale_eq (h : ℕ) (hhpos : 1 ≤ h) :
    (Q I h : ℚ)^2*B₀ (q := q) I h = (baselineNumerator (q := q) I h : ℚ) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hQ0 : (Q I h : ℚ) ≠ 0 := by exact_mod_cast (Q_pos I h hhpos).ne'
  unfold B₀ kappa baselineNumerator
  push_cast
  field_simp
  <;> ring

theorem baseline_integral (h : ℕ) (hhpos : 1 ≤ h) :
    ∃ z : ℤ, (Q I h : ℚ)^2*B₀ (q := q) I h = z :=
  ⟨baselineNumerator I h, baseline_scale_eq I h hhpos⟩

/-- The second denominator cancellation needed for the integer threshold. -/
theorem kappa_scale_eq (h : ℕ) (hhpos : 1 ≤ h) :
    (Q I h : ℚ)^2*kappa I (q := q) h = 2*q*(Q I h) := by
  have hQ0 : (Q I h : ℚ) ≠ 0 := by exact_mod_cast (Q_pos I h hhpos).ne'
  unfold kappa
  field_simp
  <;> ring

/-- Equation (17) applied directly to the integral checker value. -/
theorem checker_score_int (s : IdealCVP.SidonPositions I.n)
    (x : Coeff ℤ q) (h : ℕ) (hx : ∀ a, x a = 0 ∨ x a = 1)
    (hh : ∑ a, x a = (h : ℤ)) (hhpos : 1 ≤ h) :
    ((normSq (U I s h*classOf x-V I s) : ℤ) : ℚ)/(Q I h : ℚ)^2 =
      B₀ (q := q) I h +
        2*kappa I (q := q) h*(∑ i, (rowValue I s (fun a => (x a : ℚ)) i-1)^2) +
        kappa I (q := q) h*E I s (fun a => (x a : ℚ)) +
          remainder I s h (fun a => (x a : ℚ)) := by
  have hx' : ∀ a, (x a : ℚ) = 0 ∨ (x a : ℚ) = 1 := by
    intro a
    rcases hx a with ha | ha <;> simp [ha]
  have hh' : ∑ a, (x a : ℚ) = (h : ℚ) := by exact_mod_cast hh
  have hs := checker_score I s (fun a => (x a : ℚ)) h hx' hh' hhpos
  rw [← rationalize_classOf] at hs
  change normSq (rationalize (U I s h)*rationalize (classOf x)-rationalize (V I s)) /
    (Q I h : ℚ)^2 = _ at hs
  rw [← map_mul, ← map_sub, normSq_rationalize] at hs
  exact hs

/-- The integer threshold numerator for any integral second-coordinate cost F. -/
def thresholdNumerator (h : ℕ) (F : ℤ) : ℤ :=
  baselineNumerator (q := q) I h + (Q I h : ℤ)^2*F + 2*q*(Q I h)

/-- Section 5's S = Q²(B₀ + F + κ) is integral. -/
theorem threshold_integral (h : ℕ) (hhpos : 1 ≤ h) (F : ℤ) :
    ∃ S : ℤ, (Q I h : ℚ)^2*(B₀ (q := q) I h+(F : ℚ)+kappa I (q := q) h) = S := by
  refine ⟨thresholdNumerator (q := q) I h F, ?_⟩
  rw [mul_add, mul_add, baseline_scale_eq I h hhpos, kappa_scale_eq I h hhpos]
  simp only [thresholdNumerator, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    Int.cast_ofNat]

end Correlations
end
end Rank2ModuleSVP.Checker
