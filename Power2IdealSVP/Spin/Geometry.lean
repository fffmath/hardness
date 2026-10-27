import Power2IdealSVP.Spin.Runs
import Power2IdealSVP.Spin.Parameters

/-!
# Canonical integer configurations

The converse support construction is expressed before reduction modulo `n`. Component zero is
the trimer; negative components are left dimers and positive components are right dimers.
The finite set of component labels has all positive differences in the abstract source set `D`.

Paper: `paper/power2-ideal-svp.txt`, Section 1.3; audit Sections 7–8.
-/

namespace Power2IdealSVP.Spin

/-- The positive differences of an integer set belong to the source distance set. -/
def PositiveDifferences (D : Finset ℕ) (P : Finset ℤ) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, x < y → (y - x).toNat ∈ D

/-- The trimer at zero, a left dimer for a negative label, or a right dimer otherwise. -/
def component (q : ℤ) : Finset ℤ :=
  if q < 0 then {16 * q, 16 * q + 1}
  else if q = 0 then {0, 1, 2} else {16 * q + 1, 16 * q + 2}

/-- The canonical integer support associated with a set of component labels. -/
def configuration (P : Finset ℤ) : Finset ℤ := P.biUnion component

/-- Every component lies in its three-coordinate cell. -/
theorem component_bounds {q x : ℤ} (hx : x ∈ component q) :
    16 * q ≤ x ∧ x ≤ 16 * q + 2 := by
  unfold component at hx
  split_ifs at hx <;> simp only [Finset.mem_insert, Finset.mem_singleton] at hx <;>
    rcases hx with rfl | rfl | rfl <;> omega

/-- Component cells are strictly ordered with a gap of at least thirteen empty positions. -/
theorem components_separated {q r x y : ℤ} (hqr : q < r)
    (hx : x ∈ component q) (hy : y ∈ component r) : x + 14 ≤ y := by
  have := component_bounds hx
  have := component_bounds hy
  omega

/-- Distinct components have disjoint supports. -/
theorem components_disjoint {q r : ℤ} (hqr : q ≠ r) :
    Disjoint (component q) (component r) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hqr with h | h
  · have := components_separated h hx hy
    omega
  · have := components_separated h hy hx
    omega

/-- The zero component has three points; every other component has two. -/
theorem card_component (q : ℤ) : (component q).card = 2 + if q = 0 then 1 else 0 := by
  unfold component
  split_ifs <;> simp_all [show 16 * q ≠ 16 * q + 1 by omega,
    show 16 * q + 1 ≠ 16 * q + 2 by omega]

/-- A canonical support has `2 * |P| + 1` points when it contains the trimer label. -/
theorem card_configuration {P : Finset ℤ} (h0 : 0 ∈ P) :
    (configuration P).card = 2 * P.card + 1 := by
  rw [configuration, Finset.card_biUnion]
  · simp_rw [card_component]
    simp [Finset.sum_add_distrib, h0, Nat.mul_comm]
  · intro q hq r hr hqr
    exact components_disjoint hqr

/-- The construction is nonempty when its component set contains zero. -/
theorem configuration_nonempty {P : Finset ℤ} (h0 : 0 ∈ P) :
    (configuration P).Nonempty := by
  refine ⟨0, Finset.mem_biUnion.mpr ⟨0, h0, ?_⟩⟩
  simp [component]

/-- The constructed support has odd cardinality. -/
theorem odd_card_configuration {P : Finset ℤ} (h0 : 0 ∈ P) :
    Odd (configuration P).card := by
  rw [card_configuration h0]
  exact ⟨P.card, by omega⟩

/-- Four-window bounds for any pair of distinct, ordered components. -/
theorem component_cross_bounds {q r x y : ℤ} (hqr : q < r)
    (hx : x ∈ component q) (hy : y ∈ component r) :
    16 * (r - q) - 1 ≤ y - x ∧ y - x ≤ 16 * (r - q) + 2 := by
  unfold component at hx hy
  split_ifs at hx hy <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy <;>
    (rcases hx with rfl | rfl | rfl) <;> (rcases hy with rfl | rfl | rfl) <;> omega

/-- Pairs inside a single component have distance one or two. -/
theorem component_internal_distance {q x y : ℤ} (hx : x ∈ component q)
    (hy : y ∈ component q) (hxy : x < y) : (y - x).toNat = 1 ∨ (y - x).toNat = 2 := by
  have hx := component_bounds hx
  have hy := component_bounds hy
  omega

/-- All positive distances in the converse construction are allowed. -/
theorem configuration_allowed {D : Finset ℕ} {P : Finset ℤ}
    (hP : PositiveDifferences D P) {x y : ℤ} (hx : x ∈ configuration P)
    (hy : y ∈ configuration P) (hxy : x < y) : (y - x).toNat ∈ Eplus D := by
  obtain ⟨q, hq, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨r, hr, hy⟩ := Finset.mem_biUnion.mp hy
  rcases lt_trichotomy q r with hqr | rfl | hqr
  · have hd := hP q hq r hr hqr
    have hb := component_cross_bounds hqr hx hy
    apply mem_Eplus_iff.mpr
    right; right
    refine ⟨(r - q).toNat, hd, mem_window_iff.mpr ?_⟩
    dsimp [Q]
    have hcast : ((r - q).toNat : ℤ) = r - q := Int.toNat_of_nonneg (by omega)
    omega
  · rcases component_internal_distance hx hy hxy with h | h
    · exact mem_Eplus_iff.mpr (Or.inl h)
    · exact mem_Eplus_iff.mpr (Or.inr (Or.inl h))
  · have := components_separated hqr hy hx
    omega

/-- Positive source differences bound the diameter of the component-label set. -/
theorem component_labels_diameter {D : Finset ℕ} {P : Finset ℤ} {A0 : ℕ}
    (hD : DValid D A0) (hP : PositiveDifferences D P) {q r : ℤ}
    (hq : q ∈ P) (hr : r ∈ P) : q - r ≤ A0 := by
  by_cases hqr : r < q
  · have hle := (hD _ (hP r hr q hq hqr)).2
    have hcast : ((q - r).toNat : ℤ) = q - r := Int.toNat_of_nonneg (by omega)
    omega
  · omega

/-- The entire support has diameter at most `R0 = 16 * A0 + 2`. -/
theorem configuration_diameter {D : Finset ℕ} {P : Finset ℤ} {A0 : ℕ}
    (hD : DValid D A0) (hP : PositiveDifferences D P) {x y : ℤ}
    (hx : x ∈ configuration P) (hy : y ∈ configuration P) :
    x - y ≤ R0 A0 := by
  obtain ⟨q, hq, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨r, hr, hy⟩ := Finset.mem_biUnion.mp hy
  have := component_bounds hx
  have := component_bounds hy
  have := component_labels_diameter hD hP hq hr
  dsimp [R0, Q]
  omega

/-- A translation puts the converse support in the interval `[0,R0]`. -/
theorem configuration_in_short_interval {D : Finset ℕ} {P : Finset ℤ} {A0 : ℕ}
    (hD : DValid D A0) (hP : PositiveDifferences D P) (h0 : 0 ∈ P) :
    ∃ t : ℤ, ∀ x ∈ configuration P, 0 ≤ x - t ∧ x - t ≤ R0 A0 := by
  let W := configuration P
  have hW : W.Nonempty := configuration_nonempty h0
  refine ⟨W.min' hW, ?_⟩
  intro x hx
  exact ⟨sub_nonneg.mpr (Finset.min'_le W x hx),
    configuration_diameter hD hP hx (Finset.min'_mem W hW)⟩

/-- Allowed integer differences exclude occupied positions at distance three. -/
theorem noDistanceThree_of_allowed {D : Finset ℕ} {A0 : ℕ} {W : Finset ℤ}
    (hD : DValid D A0) (hW : PositiveDifferences (Eplus D) W) :
    NoDistanceThree W := by
  intro x hx hx3
  have he := hW x hx (x + 3) hx3 (by omega)
  have : (3 : ℕ) ∈ Eplus D := by simpa using he
  exact three_not_mem_Eplus hD this

/-- Two separated trimers would force a forbidden fifth consecutive far distance. -/
theorem trimer_unique {D : Finset ℕ} {A0 : ℕ} {W : Finset ℤ}
    (hD : DValid D A0) (hW : PositiveDifferences (Eplus D) W)
    (hI : NoIsolated W) {p q : ℤ} (hp : p ∈ runStarts W)
    (hq : q ∈ runStarts W) (hp2 : p + 2 ∈ W) (hq2 : q + 2 ∈ W) : p = q := by
  have h3 := noDistanceThree_of_allowed hD hW
  suffices ∀ p q : ℤ, p ∈ runStarts W → q ∈ runStarts W →
      p + 2 ∈ W → q + 2 ∈ W → p < q → False by
    rcases lt_trichotomy p q with h | h | h
    · exact (this p q hp hq hp2 hq2 h).elim
    · exact h
    · exact (this q p hq hp hq2 hp2 h).elim
  intro p q hp hq hp2 hq2 hpq
  have hsep := trimer_next_separated hI h3 hp hq hpq hp2
  have he0 := hW (p + 2) hp2 q (mem_runStarts.mp hq).1 (by omega)
  have he4 := hW p (mem_runStarts.mp hp).1 (q + 2) hq2 (by omega)
  have heq : (q + 2 - p).toNat = (q - (p + 2)).toNat + 4 := by omega
  rw [heq] at he4
  exact no_five_consecutive (by omega) he0 he4

/-- Odd support parity forces precisely one trimer among the disjoint run blocks. -/
theorem exists_unique_trimer {D : Finset ℕ} {A0 : ℕ} {W : Finset ℤ}
    (hD : DValid D A0) (hW : PositiveDifferences (Eplus D) W)
    (hI : NoIsolated W) (hodd : Odd W.card) :
    ∃! t : ℤ, t ∈ runStarts W ∧ t + 2 ∈ W := by
  obtain ⟨t, ht, ht2⟩ := exists_trimer hI (noDistanceThree_of_allowed hD hW) hodd
  refine ⟨t, ⟨ht, ht2⟩, ?_⟩
  intro q hq
  exact trimer_unique hD hW hI hq.1 ht hq.2 ht2

/-- A left run lies at a negative multiple of sixteen relative to the trimer start. -/
theorem left_run_offset {D : Finset ℕ} {A0 : ℕ} {W : Finset ℤ}
    (hD : DValid D A0) (hW : PositiveDifferences (Eplus D) W)
    (hI : NoIsolated W) {p t : ℤ} (hp : p ∈ runStarts W)
    (ht : t ∈ runStarts W) (ht2 : t + 2 ∈ W) (hpt : p < t) :
    ∃ d ∈ D, t - p = 16 * d := by
  have hsep := runStarts_separated hI (noDistanceThree_of_allowed hD hW) hp ht hpt
  have he0 := hW (p + 1) (runStart_succ_mem hI hp) t (mem_runStarts.mp ht).1
    (by omega)
  have he3 := hW p (mem_runStarts.mp hp).1 (t + 2) ht2 (by omega)
  have heq : (t + 2 - p).toNat = (t - (p + 1)).toNat + 3 := by omega
  rw [heq] at he3
  obtain ⟨d, hd, he⟩ := four_consecutive_window (by omega) he0 he3
  have hdpos := (hD d hd).1
  refine ⟨d, hd, ?_⟩
  dsimp [Q] at he
  omega

/-- A right run lies one beyond a positive multiple of sixteen from the trimer start. -/
theorem right_run_offset {D : Finset ℕ} {A0 : ℕ} {W : Finset ℤ}
    (hD : DValid D A0) (hW : PositiveDifferences (Eplus D) W)
    (hI : NoIsolated W) {p t : ℤ} (hp : p ∈ runStarts W)
    (ht : t ∈ runStarts W) (ht2 : t + 2 ∈ W) (htp : t < p) :
    ∃ d ∈ D, p - t = 16 * d + 1 := by
  have hsep := trimer_next_separated hI (noDistanceThree_of_allowed hD hW)
    ht hp htp ht2
  have he0 := hW (t + 2) ht2 p (mem_runStarts.mp hp).1 (by omega)
  have he3 := hW t (mem_runStarts.mp ht).1 (p + 1) (runStart_succ_mem hI hp)
    (by omega)
  have heq : (p + 1 - t).toNat = (p - (t + 2)).toNat + 3 := by omega
  rw [heq] at he3
  obtain ⟨d, hd, he⟩ := four_consecutive_window (by omega) he0 he3
  have hdpos := (hD d hd).1
  refine ⟨d, hd, ?_⟩
  dsimp [Q] at he
  omega

/-- The integer component label obtained from a run start and the trimer start. -/
def runLabel (t p : ℤ) : ℤ :=
  if p < t then (p - t) / 16 else if p = t then 0 else (p - t - 1) / 16

/-- Each run block translates to its canonical component. -/
theorem runBlock_translate {D : Finset ℕ} {A0 : ℕ} {W : Finset ℤ}
    (hD : DValid D A0) (hW : PositiveDifferences (Eplus D) W)
    (hI : NoIsolated W) {p t : ℤ} (hp : p ∈ runStarts W)
    (ht : t ∈ runStarts W) (ht2 : t + 2 ∈ W) :
    (runBlock W p).image (fun x => x - t) = component (runLabel t p) := by
  have hptrim : p ≠ t → p + 2 ∉ W := by
    intro hpt hp2
    exact hpt (trimer_unique hD hW hI hp ht hp2 ht2)
  rcases lt_trichotomy p t with h | rfl | h
  · obtain ⟨d, hd, hoff⟩ := left_run_offset hD hW hI hp ht ht2 h
    have hdpos := (hD d hd).1
    have hl : runLabel t p = -(d : ℤ) := by simp [runLabel, h]; omega
    have hp2 := hptrim (by omega)
    rw [hl, component, ite_eq_left (show -(d : ℤ) < 0 by omega)]
    simp [runBlock, hp2, show p - t = 16 * -(d : ℤ) by omega,
      show p + 1 - t = 16 * -(d : ℤ) + 1 by omega]
  · simp [runLabel, runBlock, ht2, component]
  · obtain ⟨d, hd, hoff⟩ := right_run_offset hD hW hI hp ht ht2 h
    have hdpos := (hD d hd).1
    have hl : runLabel t p = (d : ℤ) := by
      simp only [runLabel, ite_eq_right (show ¬p < t by omega),
        ite_eq_right (show p ≠ t by omega)]
      omega
    have hp2 := hptrim (by omega)
    rw [hl, component, ite_eq_right (show ¬(d : ℤ) < 0 by omega),
      ite_eq_right (show (d : ℤ) ≠ 0 by omega)]
    simp [runBlock, hp2, show p - t = 16 * (d : ℤ) + 1 by omega,
      show p + 1 - t = 16 * (d : ℤ) + 2 by omega]

/-- A canonical component always contains its middle cell coordinate. -/
theorem component_mid_mem (q : ℤ) : 16 * q + 1 ∈ component q := by
  unfold component
  split_ifs <;> simp_all

/-- The component labels extracted from an integer support satisfy the source difference rule. -/
theorem extracted_labels_positiveDifferences {D : Finset ℕ} {A0 : ℕ} {W : Finset ℤ}
    (hD : DValid D A0) (hW : PositiveDifferences (Eplus D) W)
    (hI : NoIsolated W) {t : ℤ} (ht : t ∈ runStarts W) (ht2 : t + 2 ∈ W) :
    PositiveDifferences D ((runStarts W).image (runLabel t)) := by
  intro q hq r hr hqr
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
  have hmid : ∀ a ∈ runStarts W, ∃ x ∈ W, x - t = 16 * runLabel t a + 1 := by
    intro a ha
    have hm := component_mid_mem (runLabel t a)
    rw [← runBlock_translate hD hW hI ha ht ht2] at hm
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hm
    exact ⟨x, runBlock_subset hI ha hx, he⟩
  obtain ⟨x, hx, hxe⟩ := hmid p hp
  obtain ⟨y, hy, hye⟩ := hmid s hs
  have he := hW x hx y hy (by omega)
  have hd : (y - x).toNat = Q * (runLabel t s - runLabel t p).toNat := by
    dsimp [Q]
    omega
  rw [hd] at he
  exact (mem_Eplus_center_iff (by omega)).mp he

/-- The forced integer geometry is exactly a translated canonical configuration. -/
theorem integer_geometry {D : Finset ℕ} {A0 : ℕ} {W : Finset ℤ}
    (hD : DValid D A0) (hW : PositiveDifferences (Eplus D) W)
    (hI : NoIsolated W) (hodd : Odd W.card) :
    ∃ t : ℤ, ∃ P : Finset ℤ, 0 ∈ P ∧ PositiveDifferences D P ∧
      W.image (fun x => x - t) = configuration P := by
  obtain ⟨t, ⟨ht, ht2⟩, _⟩ := exists_unique_trimer hD hW hI hodd
  let P := (runStarts W).image (runLabel t)
  refine ⟨t, P, ?_, extracted_labels_positiveDifferences hD hW hI ht ht2, ?_⟩
  · exact Finset.mem_image.mpr ⟨t, ht, by simp [runLabel]⟩
  · rw [← biUnion_runBlocks hI (noDistanceThree_of_allowed hD hW)]
    ext x
    simp only [Finset.mem_image, Finset.mem_biUnion, configuration, P]
    constructor
    · rintro ⟨y, ⟨p, hp, hyp⟩, rfl⟩
      exact ⟨runLabel t p, ⟨p, hp, rfl⟩,
        (runBlock_translate hD hW hI hp ht ht2) ▸ Finset.mem_image.mpr ⟨y, hyp, rfl⟩⟩
    · rintro ⟨q, ⟨p, hp, rfl⟩, hx⟩
      rw [← runBlock_translate hD hW hI hp ht ht2] at hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨y, ⟨p, hp, hy⟩, rfl⟩

/-- The classification also counts the occupied points in terms of its component labels. -/
theorem integer_geometry_with_card {D : Finset ℕ} {A0 : ℕ} {W : Finset ℤ}
    (hD : DValid D A0) (hW : PositiveDifferences (Eplus D) W)
    (hI : NoIsolated W) (hodd : Odd W.card) :
    ∃ t : ℤ, ∃ P : Finset ℤ, 0 ∈ P ∧ PositiveDifferences D P ∧
      W.image (fun x => x - t) = configuration P ∧ W.card = 2 * P.card + 1 := by
  obtain ⟨t, P, h0, hP, he⟩ := integer_geometry hD hW hI hodd
  refine ⟨t, P, h0, hP, he, ?_⟩
  have hcard := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ (fun x y h => by omega),
    card_configuration h0] at hcard
  exact hcard

/-- Each point in a canonical support has a neighbour in the same component. -/
theorem configuration_noIsolated (P : Finset ℤ) : NoIsolated (configuration P) := by
  intro x hx
  obtain ⟨q, hq, hx⟩ := Finset.mem_biUnion.mp hx
  have hmem : ∀ y ∈ component q, y ∈ configuration P := fun y hy =>
    Finset.mem_biUnion.mpr ⟨q, hq, hy⟩
  unfold component at hx
  split_ifs at hx with hneg hzero
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · right
      exact hmem _ (by simp [component, hneg])
    · left
      exact hmem _ (by simp [component, hneg])
  · subst q
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · right; exact hmem _ (by simp [component])
    · left; exact hmem _ (by simp [component])
    · left; exact hmem _ (by simp [component])
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · right
      exact hmem _ (by simp [component, hneg, hzero]; omega)
    · left
      exact hmem _ (by simp [component, hneg, hzero]; omega)

end Power2IdealSVP.Spin
