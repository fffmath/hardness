import Rank2ModuleSVP.Wan
import Rank2ModuleSVP.Descent
import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Analysis.Asymptotics.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

/-! Binary completions and finite counting. The combinatorial results below
have explicit numerical premises, so the remaining asymptotic estimates can be
proved independently of the finite counting and of the cyclotomic model. -/
namespace Rank2ModuleSVP
open scoped BigOperators
open Filter
noncomputable section

/-- The largest integer satisfying the paper's exact integer inequality. -/
def rsK (q : ℕ) : ℕ := Nat.findGreatest (fun r => (2*r)^1000 ≤ q) q

def rsT (q : ℕ) : ℕ := Nat.findGreatest (fun r => r^2000 ≤ q) q

def rsH (q : ℕ) : ℕ := 201 * rsK q / 200

theorem rsK_pow_le (q : ℕ) : (2 * rsK q)^1000 ≤ q :=
  Nat.findGreatest_spec (P := fun r => (2*r)^1000 ≤ q)
    (m := 0) (Nat.zero_le q) (by norm_num)

theorem rsT_pow_le (q : ℕ) : (rsT q)^2000 ≤ q :=
  Nat.findGreatest_spec (P := fun r => r^2000 ≤ q)
    (m := 0) (Nat.zero_le q) (by norm_num)

theorem le_rsK {q r : ℕ} (hr : (2*r)^1000 ≤ q) : r ≤ rsK q := by
  exact Nat.le_findGreatest (P := fun r => (2*r)^1000 ≤ q)
    ((by omega : r ≤ 2*r).trans ((Nat.le_self_pow (by norm_num) (2*r)).trans hr)) hr

theorem le_rsT {q r : ℕ} (hr : r^2000 ≤ q) : r ≤ rsT q :=
  Nat.le_findGreatest (P := fun r => r^2000 ≤ q)
    ((Nat.le_self_pow (by norm_num) r).trans hr) hr

theorem rsK_greatest (q r : ℕ) : r ≤ rsK q ↔ (2*r)^1000 ≤ q := by
  constructor
  · intro hr
    exact (Nat.pow_le_pow_left (by omega) _).trans (rsK_pow_le q)
  · exact le_rsK

theorem rsT_greatest (q r : ℕ) : r ≤ rsT q ↔ r^2000 ≤ q := by
  constructor
  · intro hr
    exact (Nat.pow_le_pow_left hr _).trans (rsT_pow_le q)
  · exact le_rsT

theorem rsK_tendsto : Tendsto rsK atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop ((2*b)^1000)] with q hq
  exact le_rsK hq

theorem rsT_tendsto : Tendsto rsT atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b^2000)] with q hq
  exact le_rsT hq

theorem rsT_sq_le (q : ℕ) : rsT q ^ 2 ≤ 2 * rsK q + 1 := by
  by_contra hh
  have hle : 2 * (rsK q + 1) ≤ rsT q ^ 2 := by omega
  have hp : (2*(rsK q+1))^1000 ≤ q := by
    calc
      _ ≤ (rsT q ^ 2)^1000 := Nat.pow_le_pow_left hle _
      _ = rsT q ^ 2000 := by rw [← pow_mul]
      _ ≤ q := rsT_pow_le q
  have := le_rsK hp
  omega

/-- `T = o(k)`, in the equivalent integer-multiplier eventual form. -/
theorem rsT_small (c : ℕ) : ∀ᶠ q in atTop, c * rsT q ≤ rsK q := by
  filter_upwards [rsT_tendsto.eventually_ge_atTop (4*c+2)] with q hq
  have hs := rsT_sq_le q
  have hprod := Nat.mul_le_mul_right (rsT q) hq
  nlinarith

theorem rsH_rounding (q : ℕ) :
    200 * rsH q ≤ 201 * rsK q ∧ 201 * rsK q < 200 * (rsH q + 1) := by
  unfold rsH
  omega

theorem rsH_le (q : ℕ) : rsH q ≤ 2 * rsK q := by
  have := (rsH_rounding q).1
  omega

/-- The bounded rounding error in `h = 201k/200 + O(1)`. -/
theorem rsH_real_rounding (q : ℕ) :
    (201 : ℝ) * rsK q / 200 - 1 < rsH q ∧
    (rsH q : ℝ) ≤ 201 * rsK q / 200 := by
  obtain ⟨h₁, h₂⟩ := rsH_rounding q
  have h₁' : (200 : ℝ) * rsH q ≤ 201 * rsK q := by exact_mod_cast h₁
  have h₂' : (201 : ℝ) * rsK q < 200 * ((rsH q : ℝ) + 1) := by exact_mod_cast h₂
  constructor <;> linarith

/-- `h = o(q)`, in the equivalent integer-multiplier eventual form. -/
theorem rsH_small (c : ℕ) : ∀ᶠ q in atTop, c * rsH q ≤ q := by
  filter_upwards [rsK_tendsto.eventually_ge_atTop c] with q hq
  have hpow : (2 * rsK q)^2 ≤ q := by
    by_cases hz : rsK q = 0
    · simp [hz]
    · calc
        _ ≤ (2 * rsK q)^1000 := Nat.pow_le_pow_right (by omega) (by norm_num)
        _ ≤ q := rsK_pow_le q
  have hh := rsH_le q
  calc
    c * rsH q ≤ rsK q * (2 * rsK q) := Nat.mul_le_mul hq hh
    _ ≤ (2 * rsK q)^2 := by nlinarith
    _ ≤ q := hpow

theorem rsK_le_rsH (q : ℕ) : rsK q ≤ rsH q := by
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 200)).mpr
  omega

/-- Wan's admissible parameter range holds uniformly after prescribing at
most T ones. -/
theorem completion_parameter_range : ∀ᶠ q in atTop,
    ∀ t ≤ rsT q, 2 ≤ rsK q ∧ rsK q ≤ (rsH q-t)-2 ∧
      (rsH q-t)-2 < q-2 := by
  filter_upwards [rsT_small 400, rsK_tendsto.eventually_ge_atTop 1200,
    rsH_small 2] with q hT hk hh
  have hr := rsH_rounding q
  have hkh := rsK_le_rsH q
  intro t ht
  omega

/-- The polynomial error budget of `enhanced-clean` tends to zero: for each
fixed constant, its numerator is eventually smaller than q. -/
theorem clean_budget_eventually (C : ℕ) :
    ∀ᶠ q in atTop, C * rsT q ^ 2 *
      (2 * rsT q * rsH q + rsH q ^ 2) < q := by
  filter_upwards [rsT_small 1, rsK_tendsto.eventually_ge_atTop (C+1)] with q hT hk
  simp only [one_mul] at hT
  have hh := rsH_le q
  have hk0 : 0 < rsK q := by omega
  have hnum : C * rsT q ^ 2 * (2 * rsT q * rsH q + rsH q ^ 2) ≤
      8*C*rsK q^4 := by
    calc
      _ ≤ C * rsK q^2 * (2 * rsK q * (2*rsK q) + (2*rsK q)^2) := by gcongr
      _ = _ := by ring
  have hp : (2*rsK q)^6 ≤ q := by
    calc
      _ ≤ (2*rsK q)^1000 := Nat.pow_le_pow_right (by omega) (by norm_num)
      _ ≤ q := rsK_pow_le q
  have hpos : 0 < rsK q^4 := pow_pos hk0 _
  have hc : 8*C < 64*rsK q^2 := by
    nlinarith [Nat.le_self_pow (by norm_num : 2 ≠ 0) (rsK q)]
  have hmul := Nat.mul_lt_mul_of_pos_right hc hpos
  have he : 64*rsK q^2*rsK q^4 = (2*rsK q)^6 := by ring
  rw [he] at hmul
  exact hnum.trans_lt (hmul.trans_le hp)

/-- The usual real-valued little-o formulation of the parameter scale. -/
theorem rsT_isLittleO :
    (fun q => (rsT q : ℝ)) =o[atTop] (fun q => (rsK q : ℝ)) := by
  apply Asymptotics.isLittleO_iff_nat_mul_le.mpr
  intro c
  filter_upwards [rsT_small c] with q hq
  have hh : (c : ℝ) * rsT q ≤ rsK q := by exact_mod_cast hq
  simpa using hh

theorem rsH_isLittleO :
    (fun q => (rsH q : ℝ)) =o[atTop] (fun q : ℕ => (q : ℝ)) := by
  apply Asymptotics.isLittleO_iff_nat_mul_le.mpr
  intro c
  filter_upwards [rsH_small c] with q hq
  have hh : (c : ℝ) * rsH q ≤ q := by exact_mod_cast hq
  simpa using hh

section Orderings
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Enumerations of exactly the given finite support. -/
def supportOrderings (m : ℕ) (s : Finset α) : Finset (Fin m → α) :=
  Finset.univ.filter fun z => Function.Injective z ∧ Finset.univ.image z = s

/-- An enumeration is the same data as an equivalence to the support. -/
def supportOrderingsEquiv (m : ℕ) (s : Finset α) :
    {z // z ∈ supportOrderings m s} ≃ (Fin m ≃ s) where
  toFun z := Equiv.ofBijective
    (fun i => ⟨z.val i, by
      have he := (Finset.mem_filter.mp z.property).2.2
      have hi : z.val i ∈ Finset.univ.image z.val :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      exact Eq.mp (congrArg (fun t : Finset α => z.val i ∈ t) he) hi⟩)
    ⟨fun i j he => (Finset.mem_filter.mp z.property).2.1 (congrArg Subtype.val he), by
      intro a
      have he := (Finset.mem_filter.mp z.property).2.2
      have ha : a.val ∈ Finset.univ.image z.val := by rw [he]; exact a.property
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
      exact ⟨i, Subtype.ext hi⟩⟩
  invFun e := ⟨fun i => (e i).val, by
    simp only [supportOrderings, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun i j he => e.injective (Subtype.ext he), ?_⟩
    ext a
    constructor
    · intro ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact (e i).property
    · intro ha
      obtain ⟨i, hi⟩ := e.surjective ⟨a, ha⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, congrArg Subtype.val hi⟩⟩
  left_inv _ := rfl
  right_inv _ := by ext i; rfl

/-- The exact factorial, with no asymptotic or analytic input. -/
theorem card_supportOrderings (m : ℕ) (s : Finset α) (hs : s.card = m) :
    (supportOrderings m s).card = m.factorial := by
  have hc : Fintype.card (Fin m) = Fintype.card s := by simp [hs]
  have e : Fin m ≃ s := Fintype.equivOfCardEq hc
  calc
    _ = Fintype.card {z // z ∈ supportOrderings m s} := (Fintype.card_coe _).symm
    _ = Fintype.card (Fin m ≃ s) := Fintype.card_congr (supportOrderingsEquiv m s)
    _ = m.factorial := by rw [Fintype.card_equiv e, Fintype.card_fin]

/-- Ordered tuples whose support belongs to a family. -/
def orderedSupportFamily (m : ℕ) (S : Finset (Finset α)) : Finset (Fin m → α) :=
  Finset.univ.filter fun z => Function.Injective z ∧ Finset.univ.image z ∈ S

/-- Exact division by the factorial when unordered supports are counted. -/
theorem card_orderedSupportFamily (m : ℕ) (S : Finset (Finset α))
    (hS : ∀ s ∈ S, s.card = m) :
    (orderedSupportFamily m S).card = m.factorial * S.card := by
  have hf : ∀ z ∈ orderedSupportFamily m S, Finset.univ.image z ∈ S := by
    intro z hz
    exact (Finset.mem_filter.mp hz).2.2
  rw [Finset.card_eq_sum_card_fiberwise hf]
  have he (s) (hs : s ∈ S) :
      ((orderedSupportFamily m S).filter fun z => Finset.univ.image z = s) =
        supportOrderings m s := by
    ext z
    simp only [orderedSupportFamily, supportOrderings, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hz, _⟩, he⟩; exact ⟨hz, he⟩
    · rintro ⟨hz, he⟩; exact ⟨⟨hz, he.symm ▸ hs⟩, he⟩
  calc
    _ = ∑ _ ∈ S, m.factorial := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [he s hs, card_supportOrderings m s (hS s hs)]
    _ = _ := by simp [mul_comm]

end Orderings

section Finite
attribute [local instance] Classical.propDecidable
variable {q : ℕ} [NeZero q]

/-- Indicator vector of a support, with values in the required integral model. -/
def binaryIndicator (s : Finset (ZMod q)) : Coeff ℤ q :=
  fun a => if a ∈ s then 1 else 0

@[simp] theorem binaryIndicator_one (s : Finset (ZMod q)) (a : ZMod q) :
    binaryIndicator s a = 1 ↔ a ∈ s := by simp [binaryIndicator]

@[simp] theorem binaryIndicator_sum (s : Finset (ZMod q)) :
    (∑ a, binaryIndicator s a) = (s.card : ℤ) := by
  simp [binaryIndicator, ← Finset.sum_filter]

theorem binaryIndicator_injective : Function.Injective (binaryIndicator (q := q)) := by
  intro s t h
  ext a
  have hh := congrFun h a
  constructor
  · intro ha
    apply (binaryIndicator_one t a).mp
    rw [← hh]
    exact (binaryIndicator_one s a).mpr ha
  · intro ha
    apply (binaryIndicator_one s a).mp
    rw [hh]
    exact (binaryIndicator_one t a).mpr ha

/-- All binary coefficient vectors, without requiring a fictitious Fintype on ℤ. -/
def binaryVectors (q : ℕ) [NeZero q] : Finset (Coeff ℤ q) :=
  Finset.univ.image binaryIndicator

@[simp] theorem mem_binaryVectors (x : Coeff ℤ q) :
    x ∈ binaryVectors q ↔ IsBinary x := by
  constructor
  · intro hx
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hx
    intro a
    by_cases ha : a ∈ s <;> simp [binaryIndicator, ha]
  · intro hx
    refine Finset.mem_image.mpr ⟨Finset.univ.filter (fun a => x a = 1), Finset.mem_univ _, ?_⟩
    funext a
    rcases hx a with ha | ha <;> simp [binaryIndicator, ha]

/-- The paper's `F(u; P, η)`, as an actual finite set of integral vectors.
Only the values of `η` on `P` matter. The weight is a free parameter. -/
def completions (k h : ℕ) (u : Fin k → ZMod q)
    (P : Finset (ZMod q)) (η : Coeff ℤ q) : Finset (Coeff ℤ q) :=
  (binaryVectors q).filter fun x =>
    syndrome k x = u ∧ (∑ a, x a) = (h : ℤ) ∧ ∀ a ∈ P, x a = η a

@[simp] theorem mem_completions (k h : ℕ) (u : Fin k → ZMod q)
    (P : Finset (ZMod q)) (η x : Coeff ℤ q) :
    x ∈ completions k h u P η ↔
      IsBinary x ∧ syndrome k x = u ∧ (∑ a, x a) = (h : ℤ) ∧
        ∀ a ∈ P, x a = η a := by
  simp [completions, and_assoc]

/-- Support of an integral binary vector. -/
def binarySupport (x : Coeff ℤ q) : Finset (ZMod q) :=
  Finset.univ.filter fun a => x a = 1

@[simp] theorem mem_binarySupport (x : Coeff ℤ q) (a : ZMod q) :
    a ∈ binarySupport x ↔ x a = 1 := by simp [binarySupport]

@[simp] theorem binarySupport_indicator (s : Finset (ZMod q)) :
    binarySupport (binaryIndicator s) = s := by ext a; simp

theorem binaryIndicator_support {x : Coeff ℤ q} (hx : IsBinary x) :
    binaryIndicator (binarySupport x) = x := by
  funext a
  rcases hx a with ha | ha <;> simp [binaryIndicator, ha]

theorem binarySupport_card {x : Coeff ℤ q} (hx : IsBinary x) :
    ((binarySupport x).card : ℤ) = ∑ a, x a := by
  rw [← binaryIndicator_sum, binaryIndicator_support hx]

/-- The prescribed one positions; prescribed zero positions remain excluded. -/
def fixedOnes (P : Finset (ZMod q)) (η : Coeff ℤ q) : Finset (ZMod q) :=
  P.filter fun a => η a = 1

/-- Supports of the free one positions, an alternative finite description of F. -/
def freeSupports (k h : ℕ) (u : Fin k → ZMod q)
    (P : Finset (ZMod q)) (η : Coeff ℤ q) : Finset (Finset (ZMod q)) :=
  Finset.univ.filter fun s => Disjoint s P ∧
    s.card + (fixedOnes P η).card = h ∧
    syndrome k (binaryIndicator (s ∪ fixedOnes P η)) = u

/-- Reconstructing the binary vector from the free support is an exact
bijection, with the prescribed ones inserted and prescribed zeros excluded. -/
theorem completions_eq_image_freeSupports (k h : ℕ) (u : Fin k → ZMod q)
    (P : Finset (ZMod q)) (η : Coeff ℤ q)
    (hη : ∀ a ∈ P, η a = 0 ∨ η a = 1) :
    completions k h u P η =
      (freeSupports k h u P η).image (fun s => binaryIndicator (s ∪ fixedOnes P η)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hb, hu, hw, hp⟩ := (mem_completions k h u P η x).mp hx
    let s := binarySupport x \ P
    have hi : binarySupport x ∩ P = fixedOnes P η := by
      ext a
      simp only [Finset.mem_inter, mem_binarySupport, fixedOnes, Finset.mem_filter]
      constructor
      · rintro ⟨hxa, ha⟩
        exact ⟨ha, (hp a ha).symm.trans hxa⟩
      · rintro ⟨ha, he⟩
        exact ⟨(hp a ha).trans he, ha⟩
    have hs : s ∪ fixedOnes P η = binarySupport x := by
      rw [← hi]
      exact Finset.sdiff_union_inter _ _
    have hdis : Disjoint s P := Finset.sdiff_disjoint
    have hfix : fixedOnes P η ⊆ P := Finset.filter_subset _ _
    have hds : Disjoint s (fixedOnes P η) := hdis.mono_right hfix
    refine Finset.mem_image.mpr ⟨s, ?_, ?_⟩
    · simp only [freeSupports, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hdis, ?_, ?_⟩
      · have hcard : (binarySupport x).card = h := by
          have hh := binarySupport_card hb
          rw [hw] at hh
          exact_mod_cast hh
        rw [← Finset.card_union_of_disjoint hds, hs, hcard]
      · rw [hs, binaryIndicator_support hb, hu]
    · rw [hs, binaryIndicator_support hb]
  · intro hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hdis, hc, hu⟩ := (Finset.mem_filter.mp hs).2
    have hds : Disjoint s (fixedOnes P η) :=
      hdis.mono_right (Finset.filter_subset _ _)
    rw [mem_completions]
    refine ⟨?_, hu, ?_, ?_⟩
    · exact (mem_binaryVectors _).mp (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)
    · rw [binaryIndicator_sum, Finset.card_union_of_disjoint hds, hc]
    · intro a ha
      have has : a ∉ s := fun hh => Finset.disjoint_left.mp hdis hh ha
      rcases hη a ha with hzero | hone
      · simp [binaryIndicator, fixedOnes, has, ha, hzero]
      · simp [binaryIndicator, fixedOnes, has, ha, hone]

/-- The support bijection preserves cardinalities exactly. -/
theorem card_completions_eq_freeSupports (k h : ℕ) (u : Fin k → ZMod q)
    (P : Finset (ZMod q)) (η : Coeff ℤ q)
    (hη : ∀ a ∈ P, η a = 0 ∨ η a = 1) :
    (completions k h u P η).card = (freeSupports k h u P η).card := by
  rw [completions_eq_image_freeSupports k h u P η hη]
  apply Finset.card_image_iff.mpr
  intro s hs t ht he
  have hsP := (Finset.mem_filter.mp hs).2.1
  have htP := (Finset.mem_filter.mp ht).2.1
  have hu := binaryIndicator_injective he
  ext a
  have ha : a ∈ s ∪ fixedOnes P η ↔ a ∈ t ∪ fixedOnes P η := by rw [hu]
  by_cases hfix : a ∈ fixedOnes P η
  · have hP : a ∈ P := (Finset.mem_filter.mp hfix).1
    have hns : a ∉ s := fun hh => Finset.disjoint_left.mp hsP hh hP
    have hnt : a ∉ t := fun hh => Finset.disjoint_left.mp htP hh hP
    simp [hns, hnt]
  · simpa [hfix] using ha

/-- Ordered completions enumerate just the free one positions. -/
def orderedCompletions (k h m : ℕ) (u : Fin k → ZMod q)
    (P : Finset (ZMod q)) (η : Coeff ℤ q) : Finset (Fin m → ZMod q) :=
  orderedSupportFamily m (freeSupports k h u P η)

/-- The exact factorial identity in the proof of `uniform-completions`.
Here `m + t = h`, where `t` is the number of prescribed ones. -/
theorem card_orderedCompletions (k h m : ℕ) (u : Fin k → ZMod q)
    (P : Finset (ZMod q)) (η : Coeff ℤ q)
    (hη : ∀ a ∈ P, η a = 0 ∨ η a = 1)
    (hm : m + (fixedOnes P η).card = h) :
    (orderedCompletions k h m u P η).card =
      m.factorial * (completions k h u P η).card := by
  rw [orderedCompletions, card_orderedSupportFamily]
  · rw [card_completions_eq_freeSupports k h u P η hη]
  · intro s hs
    have hh := (Finset.mem_filter.mp hs).2.2.1
    omega

/-- The support definition has the intended power-sum syndrome. -/
theorem syndrome_binaryIndicator (k : ℕ) (s : Finset (ZMod q)) (j : Fin k) :
    syndrome k (binaryIndicator s) j = ∑ a ∈ s, a^j.val := by
  classical
  simp [syndrome, binaryIndicator, ← Finset.sum_filter]

/-- The shifted positive syndrome from `eq:shifted-syndrome`. -/
def shiftedMoment (k : ℕ) (u : Fin k → ZMod q)
    (P : Finset (ZMod q)) (η : Coeff ℤ q) : PositiveMoment k → ZMod q :=
  fun j => u j.val - ∑ a ∈ P, (η a : ZMod q) * a^j.val.val

/-- Insert the prescribed ones into a free support and add their moments. -/
theorem syndrome_insert_free (k : ℕ) (s P : Finset (ZMod q)) (η : Coeff ℤ q)
    (hs : Disjoint s P) (hη : ∀ a ∈ P, η a = 0 ∨ η a = 1) (j : Fin k) :
    syndrome k (binaryIndicator (s ∪ fixedOnes P η)) j =
      (∑ a ∈ s, a^j.val) + ∑ a ∈ P, (η a : ZMod q) * a^j.val := by
  have hd : Disjoint s (fixedOnes P η) :=
    hs.mono_right (Finset.filter_subset _ _)
  rw [syndrome_binaryIndicator, Finset.sum_union hd]
  congr 1
  rw [fixedOnes, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  rcases hη a ha with he | he <;> simp [he]

/-- For an injective tuple, its support moments are exactly its tuple moments. -/
theorem syndrome_insert_tuple (k m : ℕ) (z : Fin m → ZMod q)
    (hz : Function.Injective z) (P : Finset (ZMod q)) (η : Coeff ℤ q)
    (hav : ∀ i, z i ∉ P) (hη : ∀ a ∈ P, η a = 0 ∨ η a = 1) (j : Fin k) :
    syndrome k (binaryIndicator (Finset.univ.image z ∪ fixedOnes P η)) j =
      (∑ i, z i^j.val) + ∑ a ∈ P, (η a : ZMod q) * a^j.val := by
  have hd : Disjoint (Finset.univ.image z) P := by
    apply Finset.disjoint_left.mpr
    intro a ha hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hav i hp
  rw [syndrome_insert_free k _ P η hd hη j,
    Finset.sum_image (fun i _ l _ h => hz h)]

/-- The tuple description is exactly Wan's distinct, avoiding solution set
for the shifted positive syndrome, including the forced zeroth equation. -/
theorem orderedCompletions_eq_good (k h m : ℕ) (hk : 0 < k)
    (u : Fin k → ZMod q) (hu : u ⟨0,hk⟩ = (h : ZMod q))
    (P : Finset (ZMod q)) (η : Coeff ℤ q)
    (hη : ∀ a ∈ P, η a = 0 ∨ η a = 1)
    (hm : m + (fixedOnes P η).card = h) :
    orderedCompletions k h m u P η =
      goodPowerSumSolutions q k m (shiftedMoment k u P η) P := by
  classical
  ext z
  simp only [orderedCompletions, orderedSupportFamily, freeSupports,
    goodPowerSumSolutions, powerSumSolutions, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hinj, hd, hc, he⟩
    have hav : ∀ i, z i ∉ P := by
      intro i hi
      exact Finset.disjoint_left.mp hd (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) hi
    refine ⟨?_, hinj, hav⟩
    intro j
    have hj := congrFun he j.val
    rw [syndrome_insert_tuple k m z hinj P η hav hη j.val] at hj
    dsimp [shiftedMoment]
    exact eq_sub_iff_add_eq.mpr hj
  · rintro ⟨hpos, hinj, hav⟩
    have hd : Disjoint (Finset.univ.image z) P := by
      apply Finset.disjoint_left.mpr
      intro a ha hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact hav i hp
    have hc : (Finset.univ.image z).card = m := by
      rw [Finset.card_image_of_injective _ hinj]
      simp
    refine ⟨hinj, hd, by omega, ?_⟩
    funext j
    by_cases hj : j.val = 0
    · have hj0 : j = ⟨0,hk⟩ := Fin.ext hj
      subst j
      rw [hu]
      have hdis : Disjoint (Finset.univ.image z) (fixedOnes P η) :=
        hd.mono_right (Finset.filter_subset _ _)
      have hcard : (Finset.univ.image z ∪ fixedOnes P η).card = h := by
        rw [Finset.card_union_of_disjoint hdis, hc, hm]
      rw [syndrome_binaryIndicator]
      simpa using congrArg (fun n : ℕ => (n : ZMod q)) hcard
    · have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj
      rw [syndrome_insert_tuple k m z hinj P η hav hη j]
      have he := hpos ⟨j,hjpos⟩
      dsimp [shiftedMoment] at he
      exact eq_sub_iff_add_eq.mp he

/-- The paper's exact identity connecting binary completions to Wan's count. -/
theorem factorial_mul_card_completions (k h m : ℕ) (hk : 0 < k)
    (u : Fin k → ZMod q) (hu : u ⟨0,hk⟩ = (h : ZMod q))
    (P : Finset (ZMod q)) (η : Coeff ℤ q)
    (hη : ∀ a ∈ P, η a = 0 ∨ η a = 1)
    (hm : m + (fixedOnes P η).card = h) :
    m.factorial * (completions k h u P η).card =
      (goodPowerSumSolutions q k m (shiftedMoment k u P η) P).card := by
  rw [← orderedCompletions_eq_good k h m hk u hu P η hη hm]
  exact (card_orderedCompletions k h m u P η hη hm).symm

/-- A uniform explicit-error completion estimate under the permitted Wan
hypothesis. The expression is multiplied by m!, avoiding divisions and any
positivity side conditions on the main term. -/
theorem completions_count_bounds (hWan : WanPowerSumEstimates)
    (hq : q.Prime) (k h m : ℕ) (hk : 2 ≤ k)
    (hkm : k ≤ m-2) (hmq : m-2 < q-2)
    (u : Fin k → ZMod q) (hu : u ⟨0,by omega⟩ = (h : ZMod q))
    (P : Finset (ZMod q)) (η : Coeff ℤ q)
    (hη : ∀ a ∈ P, η a = 0 ∨ η a = 1)
    (hm : m + (fixedOnes P η).card = h) :
    wanMain q k m - wanError q k m -
        ((m : ℝ)^2 * ((q : ℝ)^(m-k) + wanCollisionError q k m) +
         (m : ℝ)*P.card * ((q : ℝ)^(m-k) + wanCoordinateError q k m)) ≤
      (m.factorial : ℝ) * (completions k h u P η).card ∧
    (m.factorial : ℝ) * (completions k h u P η).card ≤
      wanMain q k m + wanError q k m := by
  have hh := wan_good_count_bounds hWan q hq k m hk hkm hmq
    (shiftedMoment k u P η) P
  have he := factorial_mul_card_completions k h m (by omega) u hu P η hη hm
  have he' : (m.factorial : ℝ) * (completions k h u P η).card =
      (goodPowerSumSolutions q k m (shiftedMoment k u P η) P).card := by
    exact_mod_cast he
  rwa [← he'] at hh

/-- Positivity follows directly once the explicit error budget is smaller than
Wan's main term. This isolates precisely the analytic obligation. -/
theorem completions_nonempty_of_error_budget (hWan : WanPowerSumEstimates)
    (hq : q.Prime) (k h m : ℕ) (hk : 2 ≤ k)
    (hkm : k ≤ m-2) (hmq : m-2 < q-2)
    (u : Fin k → ZMod q) (hu : u ⟨0,by omega⟩ = (h : ZMod q))
    (P : Finset (ZMod q)) (η : Coeff ℤ q)
    (hη : ∀ a ∈ P, η a = 0 ∨ η a = 1)
    (hm : m + (fixedOnes P η).card = h)
    (herr : wanError q k m +
        ((m : ℝ)^2 * ((q : ℝ)^(m-k) + wanCollisionError q k m) +
         (m : ℝ)*P.card * ((q : ℝ)^(m-k) + wanCoordinateError q k m)) <
      wanMain q k m) :
    (completions k h u P η).Nonempty := by
  have hh := (completions_count_bounds hWan hq k h m hk hkm hmq
    u hu P η hη hm).1
  apply Finset.card_pos.mp
  by_contra hn
  have he : (completions k h u P η).card = 0 := by omega
  rw [he, Nat.cast_zero, mul_zero] at hh
  linarith

/-- Additional prescribed ones, the event used in the fixed-coordinate ratio. -/
def completionEvent (F : Finset (Coeff ℤ q)) (Q : Finset (ZMod q)) :
    Finset (Coeff ℤ q) := F.filter fun x => ∀ a ∈ Q, x a = 1

/-- Exact counting identity behind `fixed-coordinate-ratio`. -/
theorem completionEvent_eq (k h : ℕ) (u : Fin k → ZMod q)
    (P Q : Finset (ZMod q)) (η : Coeff ℤ q) (hPQ : Disjoint P Q) :
    completionEvent (completions k h u P η) Q =
      completions k h u (P ∪ Q) (fun a => if a ∈ Q then 1 else η a) := by
  ext x
  simp only [completionEvent, Finset.mem_filter, mem_completions]
  constructor
  · rintro ⟨⟨hb, hu, hw, hp⟩, hQ⟩
    refine ⟨hb, hu, hw, ?_⟩
    intro a ha
    by_cases hqa : a ∈ Q
    · simpa [hqa] using hQ a hqa
    · simp only [hqa, ↓reduceIte]
      exact hp a ((Finset.mem_union.mp ha).resolve_right hqa)
  · rintro ⟨hb, hu, hw, hp⟩
    refine ⟨⟨hb, hu, hw, ?_⟩, ?_⟩
    · intro a ha
      have hqa : a ∉ Q := Finset.disjoint_left.mp hPQ ha
      simpa [hqa] using hp a (Finset.mem_union_left Q ha)
    · intro a ha
      simpa [ha] using hp a (Finset.mem_union_right P ha)

/-- A pair event is contained in the event prescribing its free endpoints.
This is the exact interface used to apply a one/two coordinate ratio bound. -/
theorem pairEvent_subset_completionEvent (F : Finset (Coeff ℤ q))
    (P : Finset (ZMod q)) (a b : ZMod q) :
    (F.filter fun x => x a = 1 ∧ x b = 1) ⊆
      completionEvent F ({a,b} \ P) := by
  intro x hx
  obtain ⟨hxF, hxa, hxb⟩ := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨hxF, ?_⟩
  intro c hc
  have hc' := (Finset.mem_sdiff.mp hc).1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
  rcases hc' with rfl | rfl
  · exact hxa
  · exact hxb

theorem card_pairEvent_le (F : Finset (Coeff ℤ q))
    (P : Finset (ZMod q)) (a b : ZMod q) :
    (F.filter fun x => x a = 1 ∧ x b = 1).card ≤
      (completionEvent F ({a,b} \ P)).card :=
  Finset.card_le_card (pairEvent_subset_completionEvent F P a b)

/-- Integer cyclic correlation, independent of the checker implementation. -/
def cyclicCorrelation (x : Coeff ℤ q) (d : ZMod q) : ℤ :=
  ∑ a, x a * x (a+d)

/-- The precise events removed in the clean-completion union bound. Internal
pairs are retained; Sidon uniqueness handles those separately. -/
def forbiddenPairIndices (P D : Finset (ZMod q)) : Finset (ZMod q × ZMod q) :=
  (D.product Finset.univ).filter fun p => p.2 ∉ P ∨ p.2+p.1 ∉ P

/-- A finite union bound for clean products, with the exact event budget.
No independence of coordinate events is assumed. -/
theorem exists_clean_products_of_budget (F : Finset (Coeff ℤ q))
    (P D : Finset (ZMod q)) (hbinary : ∀ x ∈ F, IsBinary x)
    (hbudget : (∑ p ∈ forbiddenPairIndices P D,
      (F.filter fun x => x p.2 = 1 ∧ x (p.2+p.1) = 1).card) < F.card) :
    ∃ x ∈ F, ∀ d ∈ D, ∀ a, a ∉ P ∨ a+d ∉ P → x a * x (a+d) = 0 := by
  obtain ⟨x, hx, hav⟩ := exists_avoiding_of_sum_lt F (forbiddenPairIndices P D)
    (fun p x => x p.2 = 1 ∧ x (p.2+p.1) = 1) (by
      convert hbudget using 1
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      ext x
      simp only [Finset.mem_filter])
  refine ⟨x, hx, ?_⟩
  intro d hd a ha
  have hn : ¬ (x a = 1 ∧ x (a+d) = 1) :=
    hav (d,a) (by simp [forbiddenPairIndices, hd, ha])
  rcases hbinary x hx a with hzero | hone
  · simp [hzero]
  · rcases hbinary x hx (a+d) with hzero | hone'
    · simp [hzero]
    · exact (hn ⟨hone, hone'⟩).elim

/-- Once all external products vanish, an offset with a unique internal
ordered pair has exactly that pair's contribution. -/
theorem cyclicCorrelation_eq_single (x : Coeff ℤ q) (P : Finset (ZMod q))
    (d a₀ : ZMod q)
    (hinternal : ∀ a ∈ P, a+d ∈ P → a = a₀)
    (hzero : ∀ a, a ∉ P ∨ a+d ∉ P → x a * x (a+d) = 0) :
    cyclicCorrelation x d = x a₀ * x (a₀+d) := by
  unfold cyclicCorrelation
  apply Finset.sum_eq_single a₀
  · intro a _ hne
    by_cases ha : a ∈ P
    · by_cases had : a+d ∈ P
      · exact (hne (hinternal a ha had)).elim
      · exact hzero a (Or.inr had)
    · exact hzero a (Or.inl ha)
  · simp

/-- An offset with no internal pair has zero correlation. -/
theorem cyclicCorrelation_eq_zero (x : Coeff ℤ q) (P : Finset (ZMod q))
    (d : ZMod q) (hinternal : ∀ a ∈ P, a+d ∉ P)
    (hzero : ∀ a, a ∉ P ∨ a+d ∉ P → x a * x (a+d) = 0) :
    cyclicCorrelation x d = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a ∈ P
  · exact hzero a (Or.inr (hinternal a ha))
  · exact hzero a (Or.inl ha)

/-- Abstract Sidon witness offsets, with no row/checker construction. -/
def completionWitnessOffsets {n : ℕ} (α : Fin n → ZMod q) : Finset (ZMod q) :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2).image
    (fun p => α p.2 - α p.1)

/-- The finite, exact-budget form of `enhanced-clean`. Its numerical premise
is the union bound left to discharge using uniform completion estimates.
It applies to arbitrary syndromes and arbitrary integral prescribed values. -/
theorem enhanced_clean_of_budget {n : ℕ} (α : Fin n → ZMod q)
    (hα : Function.Injective α)
    (hSidon : ∀ j l j' l', j ≠ l → j' ≠ l' →
      α l - α j = α l' - α j' → j = j' ∧ l = l')
    (Dbad : Finset (ZMod q)) (hbad0 : (0 : ZMod q) ∉ Dbad)
    (hbadwit : Disjoint Dbad (completionWitnessOffsets α))
    (k h : ℕ) (u : Fin k → ZMod q) (η : Coeff ℤ q)
    (hbudget :
      (∑ p ∈ forbiddenPairIndices (Finset.univ.image α)
          (completionWitnessOffsets α ∪ Dbad),
        ((completions k h u (Finset.univ.image α) η).filter
          fun x => x p.2 = 1 ∧ x (p.2+p.1) = 1).card) <
        (completions k h u (Finset.univ.image α) η).card) :
    ∃ x ∈ completions k h u (Finset.univ.image α) η,
      (∀ j l, j ≠ l → cyclicCorrelation x (α l - α j) = η (α j) * η (α l)) ∧
      ∀ d ∈ Dbad, cyclicCorrelation x d = 0 := by
  let P := Finset.univ.image α
  obtain ⟨x, hx, hzero⟩ := exists_clean_products_of_budget
    (completions k h u P η) P (completionWitnessOffsets α ∪ Dbad)
    (fun x hx => (mem_completions k h u P η x).mp hx |>.1) hbudget
  have hfix := ((mem_completions k h u P η x).mp hx).2.2.2
  have hpres (j : Fin n) : x (α j) = η (α j) :=
    hfix _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  refine ⟨x, hx, ?_, ?_⟩
  · intro j l hjl
    have hd : α l - α j ∈ completionWitnessOffsets α :=
      Finset.mem_image.mpr ⟨(j,l), by simp [hjl], rfl⟩
    have hinternal : ∀ a ∈ P, a+(α l-α j) ∈ P → a = α j := by
      intro a ha hb
      obtain ⟨r, _, hr⟩ := Finset.mem_image.mp ha
      obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hb
      have hrs : r ≠ s := by
        intro he
        subst s
        have hz : α l - α j = 0 := by rw [hr] at hs; exact add_left_cancel (hs.symm.trans (add_zero a).symm)
        exact hjl (hα (sub_eq_zero.mp hz).symm)
      have he : α s - α r = α l - α j := by rw [hr, hs]; abel
      exact hr.symm.trans (congrArg α (hSidon r s j l hrs hjl he).1)
    rw [cyclicCorrelation_eq_single x P _ (α j) hinternal
      (hzero _ (Finset.mem_union_left Dbad hd))]
    have he : α j + (α l-α j) = α l := by abel
    rw [he, hpres j, hpres l]
  · intro d hd
    have hinternal : ∀ a ∈ P, a+d ∉ P := by
      intro a ha hb
      obtain ⟨r, _, hr⟩ := Finset.mem_image.mp ha
      obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hb
      have hrs : r ≠ s := by
        intro he
        subst s
        have hz : d = 0 := by rw [hr] at hs; exact add_left_cancel (hs.symm.trans (add_zero a).symm)
        exact hbad0 (hz ▸ hd)
      have he : α s - α r = d := by rw [hr, hs]; abel
      have hw : d ∈ completionWitnessOffsets α :=
        Finset.mem_image.mpr ⟨(r,s), by simp [hrs], he⟩
      exact Finset.disjoint_left.mp hbadwit hd hw
    exact cyclicCorrelation_eq_zero x P d hinternal
      (hzero d (Finset.mem_union_right _ hd))

end Finite
end
end Rank2ModuleSVP
