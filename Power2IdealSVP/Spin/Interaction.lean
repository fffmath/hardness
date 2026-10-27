import Power2IdealSVP.Spin.Geometry
import Power2IdealSVP.Spin.Defs

/-!
# Ordinary-distance endpoint interactions

The kernel below is the signed-offset kernel of the small multiplier on a short integer
lift. Its four-point window is `(0,1,0,1)` and it is even. Component fields include both
receiver and sender signs, as required by the sparse-spin objective.

Paper: `paper/power2-ideal-svp.txt`, Section 1.4; expanded audit, Section 9.
-/

namespace Power2IdealSVP.Spin

/-- The ordinary, even kernel of the small interaction before negacyclic reduction. -/
def interactionKernel (D : Finset ℕ) (e : ℤ) : ℤ :=
  if ∃ d ∈ D, e = 16 * (d : ℤ) ∨ e = -(16 * (d : ℤ)) ∨
      e = 16 * (d : ℤ) + 2 ∨ e = -(16 * (d : ℤ) + 2) then 1 else 0

/-- Reflection leaves the ordinary kernel unchanged. -/
@[simp] theorem interactionKernel_neg (D : Finset ℕ) (e : ℤ) :
    interactionKernel D (-e) = interactionKernel D e := by
  unfold interactionKernel
  congr 1
  apply propext
  constructor <;> rintro ⟨d, hd, he⟩ <;> refine ⟨d, hd, ?_⟩ <;>
    rcases he with he | he | he | he <;> omega

/-- Near a positive center, only offsets zero and two have nonzero kernel. -/
theorem interactionKernel_window {D : Finset ℕ} {A0 d : ℕ}
    (hD : DValid D A0) (hd : d ∈ D) {e : ℤ} (he0 : -2 ≤ e) (he2 : e ≤ 2) :
    interactionKernel D (16 * (d : ℤ) + e) = if e = 0 ∨ e = 2 then 1 else 0 := by
  have hdpos := (hD d hd).1
  unfold interactionKernel
  congr 1
  apply propext
  constructor
  · rintro ⟨c, hc, h⟩
    have hcpos := (hD c hc).1
    rcases h with h | h | h | h <;> omega
  · intro h
    refine ⟨d, hd, ?_⟩
    rcases h with rfl | rfl <;> omega

/-- The small interaction has no within-component term. -/
theorem interactionKernel_near {D : Finset ℕ} {A0 : ℕ} (hD : DValid D A0)
    {e : ℤ} (he0 : -2 ≤ e) (he2 : e ≤ 2) : interactionKernel D e = 0 := by
  unfold interactionKernel
  split_ifs with h
  · obtain ⟨d, hd, he⟩ := h
    have hdpos := (hD d hd).1
    rcases he with he | he | he | he <;> omega
  · rfl

/-- Each kernel coefficient is the sum of the four explicit multiplier indicators. -/
theorem interactionKernel_eq_sum {D : Finset ℕ} {A0 : ℕ} (hD : DValid D A0)
    (e : ℤ) : interactionKernel D e = ∑ d ∈ D,
      ((if e = 16 * (d : ℤ) then 1 else 0) +
       (if e = -(16 * (d : ℤ)) then 1 else 0) +
       (if e = 16 * (d : ℤ) + 2 then 1 else 0) +
       (if e = -(16 * (d : ℤ) + 2) then 1 else 0)) := by
  classical
  by_cases he : ∃ d ∈ D, e = 16 * (d : ℤ) ∨ e = -(16 * (d : ℤ)) ∨
      e = 16 * (d : ℤ) + 2 ∨ e = -(16 * (d : ℤ) + 2)
  · obtain ⟨d, hd, hde⟩ := he
    rw [Finset.sum_eq_single d]
    · rw [interactionKernel, ite_eq_left ⟨d, hd, hde⟩]
      have hdpos := (hD d hd).1
      rcases hde with h | h | h | h <;> split_ifs <;> omega
    · intro c hc hcd
      have hcpos := (hD c hc).1
      have hdpos := (hD d hd).1
      rcases hde with h | h | h | h <;> split_ifs <;> omega
    · exact fun h => (h hd).elim
  · rw [interactionKernel, ite_eq_right he]
    symm
    apply Finset.sum_eq_zero
    intro d hd
    have hd0 : e ≠ 16 * (d : ℤ) := fun h => he ⟨d, hd, Or.inl h⟩
    have hdn : e ≠ -(16 * (d : ℤ)) := fun h => he ⟨d, hd, Or.inr (Or.inl h)⟩
    have hd2 : e ≠ 16 * (d : ℤ) + 2 := fun h => he ⟨d, hd, Or.inr (Or.inr (Or.inl h))⟩
    have hdn2 : e ≠ -(16 * (d : ℤ) + 2) :=
      fun h => he ⟨d, hd, Or.inr (Or.inr (Or.inr h))⟩
    simp only [ite_eq_right hd0, ite_eq_right hdn, ite_eq_right hd2,
      ite_eq_right hdn2, add_zero]

/-- Every offset between two ordered component cells reduces to its local offset. -/
theorem interactionKernel_cells {D : Finset ℕ} {A0 : ℕ} (hD : DValid D A0)
    {q r : ℤ} (hqr : q < r) (hd : (r - q).toNat ∈ D)
    {a b : ℤ} (ha : 0 ≤ a ∧ a ≤ 2) (hb : 0 ≤ b ∧ b ≤ 2) :
    interactionKernel D ((16 * q + a) - (16 * r + b)) =
      if b - a = 0 ∨ b - a = 2 then 1 else 0 := by
  have hcast : ((r - q).toNat : ℤ) = r - q := Int.toNat_of_nonneg (by omega)
  rw [show (16 * q + a) - (16 * r + b) =
    -(16 * ((r - q).toNat : ℤ) + (b - a)) by rw [hcast]; ring]
  rw [interactionKernel_neg]
  exact interactionKernel_window hD hd (by omega) (by omega)

/-- Positive cross-cell offsets are compared directly with the center and its second offset. -/
theorem interactionKernel_cross_pos {D : Finset ℕ} {A0 : ℕ} (hD : DValid D A0)
    {q r : ℤ} (hqr : q < r) (hd : (r - q).toNat ∈ D) {e : ℤ}
    (he0 : 16 * (r - q) - 2 ≤ e) (he2 : e ≤ 16 * (r - q) + 2) :
    interactionKernel D e = if e = 16 * (r - q) ∨ e = 16 * (r - q) + 2
      then 1 else 0 := by
  have hcast : ((r - q).toNat : ℤ) = r - q := Int.toNat_of_nonneg (by omega)
  have h := interactionKernel_window hD hd
    (e := e - 16 * (r - q)) (by omega) (by omega)
  rw [hcast, show 16 * (r - q) + (e - 16 * (r - q)) = e by ring] at h
  simpa only [sub_eq_zero, sub_eq_iff_eq_add, add_comm, zero_add] using h

/-- Negative cross-cell offsets use the even reflection of the positive kernel. -/
theorem interactionKernel_cross_neg {D : Finset ℕ} {A0 : ℕ} (hD : DValid D A0)
    {q r : ℤ} (hqr : q < r) (hd : (r - q).toNat ∈ D) {e : ℤ}
    (he0 : 16 * (r - q) - 2 ≤ -e) (he2 : -e ≤ 16 * (r - q) + 2) :
    interactionKernel D e = if -e = 16 * (r - q) ∨ -e = 16 * (r - q) + 2
      then 1 else 0 := by
  rw [← interactionKernel_neg D e]
  exact interactionKernel_cross_pos hD hqr hd he0 he2

/-- Signs on a canonical component, with the trimer starting positive. -/
def componentSign (q x : ℤ) : ℤ :=
  if q < 0 then if x = 16 * q then 1 else -1
  else if q = 0 then if x = 1 then -1 else 1
  else if x = 16 * q + 1 then -1 else 1

/-- The field at `x` in receiver `q` contributed by sender component `r`. -/
def componentField (D : Finset ℕ) (q r x : ℤ) : ℤ :=
  componentSign q x *
    ∑ y ∈ component r, interactionKernel D (x - y) * componentSign r y

/-- A component contributes no small-interaction field to itself. -/
theorem componentField_self {D : Finset ℕ} {A0 : ℕ} {q x : ℤ}
    (hD : DValid D A0) (hx : x ∈ component q) : componentField D q q x = 0 := by
  unfold componentField
  have hz : ∀ y ∈ component q, interactionKernel D (x - y) = 0 := by
    intro y hy
    have hxb := component_bounds hx
    have hyb := component_bounds hy
    exact interactionKernel_near hD (by omega) (by omega)
  have hsum : (∑ y ∈ component q,
      interactionKernel D (x - y) * componentSign q y) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    rw [hz y hy, zero_mul]
  rw [hsum, mul_zero]

/-- The nine possible cross-cell kernel coefficients in the lower-to-upper direction. -/
theorem interactionKernel_cell_table {D : Finset ℕ} {A0 : ℕ} (hD : DValid D A0)
    {q r : ℤ} (hqr : q < r) (hd : (r - q).toNat ∈ D) :
    interactionKernel D (16 * q - 16 * r) = 1 ∧
    interactionKernel D (16 * q - (16 * r + 1)) = 0 ∧
    interactionKernel D (16 * q - (16 * r + 2)) = 1 ∧
    interactionKernel D ((16 * q + 1) - 16 * r) = 0 ∧
    interactionKernel D ((16 * q + 1) - (16 * r + 1)) = 1 ∧
    interactionKernel D ((16 * q + 1) - (16 * r + 2)) = 0 ∧
    interactionKernel D ((16 * q + 2) - 16 * r) = 0 ∧
    interactionKernel D ((16 * q + 2) - (16 * r + 1)) = 0 ∧
    interactionKernel D ((16 * q + 2) - (16 * r + 2)) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using interactionKernel_cells hD hqr hd
      (a := 0) (b := 0) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · simpa using interactionKernel_cells hD hqr hd
      (a := 0) (b := 1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · simpa using interactionKernel_cells hD hqr hd
      (a := 0) (b := 2) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · simpa using interactionKernel_cells hD hqr hd
      (a := 1) (b := 0) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · simpa using interactionKernel_cells hD hqr hd
      (a := 1) (b := 1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · simpa using interactionKernel_cells hD hqr hd
      (a := 1) (b := 2) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · simpa using interactionKernel_cells hD hqr hd
      (a := 2) (b := 0) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · simpa using interactionKernel_cells hD hqr hd
      (a := 2) (b := 1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · simpa using interactionKernel_cells hD hqr hd
      (a := 2) (b := 2) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩

/-- The nine possible cross-cell kernel coefficients in the upper-to-lower direction. -/
theorem interactionKernel_cell_table_rev {D : Finset ℕ} {A0 : ℕ} (hD : DValid D A0)
    {q r : ℤ} (hqr : r < q) (hd : (q - r).toNat ∈ D) :
    interactionKernel D (16 * q - 16 * r) = 1 ∧
    interactionKernel D (16 * q - (16 * r + 1)) = 0 ∧
    interactionKernel D (16 * q - (16 * r + 2)) = 0 ∧
    interactionKernel D ((16 * q + 1) - 16 * r) = 0 ∧
    interactionKernel D ((16 * q + 1) - (16 * r + 1)) = 1 ∧
    interactionKernel D ((16 * q + 1) - (16 * r + 2)) = 0 ∧
    interactionKernel D ((16 * q + 2) - 16 * r) = 1 ∧
    interactionKernel D ((16 * q + 2) - (16 * r + 1)) = 0 ∧
    interactionKernel D ((16 * q + 2) - (16 * r + 2)) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 16 * q - 16 * r = -(16 * r - 16 * q) by ring,
      interactionKernel_neg]
    simpa using interactionKernel_cells hD hqr hd
      (a := 0) (b := 0) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · rw [show 16 * q - (16 * r + 1) = -((16 * r + 1) - 16 * q) by ring,
      interactionKernel_neg]
    simpa using interactionKernel_cells hD hqr hd
      (a := 1) (b := 0) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · rw [show 16 * q - (16 * r + 2) = -((16 * r + 2) - 16 * q) by ring,
      interactionKernel_neg]
    simpa using interactionKernel_cells hD hqr hd
      (a := 2) (b := 0) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · rw [show (16 * q + 1) - 16 * r = -(16 * r - (16 * q + 1)) by ring,
      interactionKernel_neg]
    simpa using interactionKernel_cells hD hqr hd
      (a := 0) (b := 1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · rw [show (16 * q + 1) - (16 * r + 1) = -((16 * r + 1) - (16 * q + 1)) by ring,
      interactionKernel_neg]
    simpa using interactionKernel_cells hD hqr hd
      (a := 1) (b := 1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · rw [show (16 * q + 1) - (16 * r + 2) = -((16 * r + 2) - (16 * q + 1)) by ring,
      interactionKernel_neg]
    simpa using interactionKernel_cells hD hqr hd
      (a := 2) (b := 1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · rw [show (16 * q + 2) - 16 * r = -(16 * r - (16 * q + 2)) by ring,
      interactionKernel_neg]
    simpa using interactionKernel_cells hD hqr hd
      (a := 0) (b := 2) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · rw [show (16 * q + 2) - (16 * r + 1) = -((16 * r + 1) - (16 * q + 2)) by ring,
      interactionKernel_neg]
    simpa using interactionKernel_cells hD hqr hd
      (a := 1) (b := 2) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · rw [show (16 * q + 2) - (16 * r + 2) = -((16 * r + 2) - (16 * q + 2)) by ring,
      interactionKernel_neg]
    simpa using interactionKernel_cells hD hqr hd
      (a := 2) (b := 2) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩

/-- Complete directed table when the receiver is to the left of the sender. -/
theorem componentField_of_lt {D : Finset ℕ} {A0 : ℕ} (hD : DValid D A0)
    {q r x : ℤ} (hqr : q < r) (hd : (r - q).toNat ∈ D) (hx : x ∈ component q) :
    componentField D q r x = if r = 0 ∧ x = 16 * q then 2 else 1 := by
  obtain ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ :=
    interactionKernel_cell_table hD hqr hd
  unfold componentField
  unfold component at hx ⊢
  split_ifs at hx ⊢ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx <;>
    (rcases hx with rfl | rfl | rfl)
  all_goals try omega
  all_goals first
    | rw [Finset.sum_pair (by omega)]
    | rw [Finset.sum_insert (by norm_num : (0 : ℤ) ∉ ({1, 2} : Finset ℤ)),
        Finset.sum_pair (by norm_num : (1 : ℤ) ≠ 2)]
  all_goals simp_all [componentSign]
  all_goals omega

/-- Complete directed table when the receiver is to the right of the sender. -/
theorem componentField_of_gt {D : Finset ℕ} {A0 : ℕ} (hD : DValid D A0)
    {q r x : ℤ} (hqr : r < q) (hd : (q - r).toNat ∈ D) (hx : x ∈ component q) :
    componentField D q r x = if r = 0 ∧ x = 16 * q + 2 then 2 else 1 := by
  obtain ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ :=
    interactionKernel_cell_table_rev hD hqr hd
  unfold componentField
  unfold component at hx ⊢
  split_ifs at hx ⊢ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx <;>
    (rcases hx with rfl | rfl | rfl)
  all_goals try omega
  all_goals first
    | rw [Finset.sum_pair (by omega)]
    | rw [Finset.sum_insert (by norm_num : (0 : ℤ) ∉ ({1, 2} : Finset ℤ)),
        Finset.sum_pair (by norm_num : (1 : ℤ) ≠ 2)]
  all_goals simp_all [componentSign]
  all_goals omega

/-- The outside endpoint of a dimer receives the extra unit from the trimer. -/
def extraEndpoint (q x : ℤ) : Prop :=
  (q < 0 ∧ x = 16 * q) ∨ (0 < q ∧ x = 16 * q + 2)

instance (q x : ℤ) : Decidable (extraEndpoint q x) := inferInstanceAs
  (Decidable ((q < 0 ∧ x = 16 * q) ∨ (0 < q ∧ x = 16 * q + 2)))

/-- The directed table in a form suitable for summing over a configuration. -/
theorem componentField_table {D : Finset ℕ} {A0 : ℕ} {P : Finset ℤ}
    (hD : DValid D A0) (hP : PositiveDifferences D P)
    {q r x : ℤ} (hq : q ∈ P) (hr : r ∈ P) (hx : x ∈ component q) :
    componentField D q r x = (1 - if r = q then 1 else 0) +
      if r = 0 ∧ extraEndpoint q x then 1 else 0 := by
  rcases lt_trichotomy q r with hqr | rfl | hqr
  · rw [componentField_of_lt hD hqr (hP q hq r hr hqr) hx]
    unfold extraEndpoint
    split_ifs <;> omega
  · rw [componentField_self hD hx]
    unfold extraEndpoint
    split_ifs <;> omega
  · rw [componentField_of_gt hD hqr (hP r hr q hq hqr) hx]
    unfold extraEndpoint
    split_ifs <;> omega

/-- The whole small-interaction field on a canonical integer configuration. -/
def configurationField (D : Finset ℕ) (P : Finset ℤ) (q x : ℤ) : ℤ :=
  ∑ r ∈ P, componentField D q r x

/-- Exact totals: the trimer receives `|P|-1`, while each dimer has one extra endpoint. -/
theorem configurationField_eq {D : Finset ℕ} {A0 : ℕ} {P : Finset ℤ}
    (hD : DValid D A0) (hP : PositiveDifferences D P) (h0 : 0 ∈ P)
    {q x : ℤ} (hq : q ∈ P) (hx : x ∈ component q) :
    configurationField D P q x = (P.card : ℤ) - 1 +
      if extraEndpoint q x then 1 else 0 := by
  unfold configurationField
  have heq : ∀ r ∈ P, componentField D q r x =
      (1 - if r = q then 1 else 0) +
        if r = 0 then (if extraEndpoint q x then 1 else 0) else 0 := by
    intro r hr
    rw [componentField_table hD hP hq hr hx]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl heq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [hq, h0]

/-- All integer interaction fields are bounded below by the exact endpoint minimum. -/
theorem configurationField_lower {D : Finset ℕ} {A0 : ℕ} {P : Finset ℤ}
    (hD : DValid D A0) (hP : PositiveDifferences D P) (h0 : 0 ∈ P)
    {q x : ℤ} (hq : q ∈ P) (hx : x ∈ component q) :
    (P.card : ℤ) - 1 ≤ configurationField D P q x := by
  rw [configurationField_eq hD hP h0 hq hx]
  split_ifs <;> omega

/-- Either endpoint of the trimer attains the interaction minimum. -/
theorem configurationField_trimer {D : Finset ℕ} {A0 : ℕ} {P : Finset ℤ}
    (hD : DValid D A0) (hP : PositiveDifferences D P) (h0 : 0 ∈ P)
    {x : ℤ} (hx : x ∈ component 0) :
    configurationField D P 0 x = (P.card : ℤ) - 1 := by
  rw [configurationField_eq hD hP h0 h0 hx]
  simp [extraEndpoint]

/-- The ordinary nearest-neighbour kernel. -/
def neighborKernel (e : ℤ) : ℤ := if e = -1 ∨ e = 1 then 1 else 0

/-- Signed nearest-neighbour contribution between two components, with amplitude one. -/
def neighborComponentField (q r x : ℤ) : ℤ :=
  -componentSign q x * ∑ y ∈ component r, neighborKernel (x - y) * componentSign r y

/-- Separated components have no nearest-neighbour interactions. -/
theorem neighborComponentField_of_ne {q r x : ℤ} (hqr : q ≠ r)
    (hx : x ∈ component q) : neighborComponentField q r x = 0 := by
  unfold neighborComponentField
  have hz : ∀ y ∈ component r, neighborKernel (x - y) = 0 := by
    intro y hy
    rcases lt_or_gt_of_ne hqr with h | h
    · have := components_separated h hx hy
      simp [neighborKernel, show x - y ≠ -1 by omega, show x - y ≠ 1 by omega]
    · have := components_separated h hy hx
      simp [neighborKernel, show x - y ≠ -1 by omega, show x - y ≠ 1 by omega]
  have hsum : (∑ y ∈ component r, neighborKernel (x - y) * componentSign r y) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    rw [hz y hy, zero_mul]
  rw [hsum, mul_zero]

/-- Every endpoint has one nearest neighbour, and the trimer center has two. -/
theorem neighborComponentField_self {q x : ℤ} (hx : x ∈ component q) :
    neighborComponentField q q x = if q = 0 ∧ x = 1 then 2 else 1 := by
  unfold neighborComponentField
  unfold component at hx ⊢
  split_ifs at hx ⊢ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx <;>
    (rcases hx with rfl | rfl | rfl)
  all_goals try omega
  all_goals first
    | rw [Finset.sum_pair (by omega)]
    | rw [Finset.sum_insert (by norm_num : (0 : ℤ) ∉ ({1, 2} : Finset ℤ)),
        Finset.sum_pair (by norm_num : (1 : ℤ) ≠ 2)]
  all_goals simp (discharger := omega) [componentSign, neighborKernel]
  all_goals omega

/-- The nearest-neighbour field in the whole integer configuration. -/
def neighborConfigurationField (P : Finset ℤ) (q x : ℤ) : ℤ :=
  ∑ r ∈ P, neighborComponentField q r x

/-- The nearest-neighbour field depends only on whether the receiver is the trimer center. -/
theorem neighborConfigurationField_eq {P : Finset ℤ} {q x : ℤ}
    (hq : q ∈ P) (hx : x ∈ component q) :
    neighborConfigurationField P q x = if q = 0 ∧ x = 1 then 2 else 1 := by
  unfold neighborConfigurationField
  rw [Finset.sum_eq_single q]
  · exact neighborComponentField_self hx
  · intro r _ hrq
    exact neighborComponentField_of_ne hrq.symm hx
  · exact fun h => (h hq).elim

/-- The entire small field, including the nearest-neighbour amplitude. -/
def smallConfigurationField (c : ℤ) (D : Finset ℕ) (P : Finset ℤ) (q x : ℤ) : ℤ :=
  c * neighborConfigurationField P q x + configurationField D P q x

/-- The exact whole small-field minimum is `c + |P| - 1`. -/
theorem smallConfigurationField_min {D : Finset ℕ} {A0 : ℕ} {P : Finset ℤ}
    (hD : DValid D A0) (hP : PositiveDifferences D P) (h0 : 0 ∈ P)
    {c : ℤ} (hc : 0 ≤ c) :
    (∀ q ∈ P, ∀ x ∈ component q,
      c + (P.card : ℤ) - 1 ≤ smallConfigurationField c D P q x) ∧
    smallConfigurationField c D P 0 0 = c + (P.card : ℤ) - 1 := by
  constructor
  · intro q hq x hx
    unfold smallConfigurationField
    rw [neighborConfigurationField_eq hq hx, configurationField_eq hD hP h0 hq hx]
    split_ifs <;> omega
  · unfold smallConfigurationField
    have hx : (0 : ℤ) ∈ component 0 := by simp [component]
    rw [neighborConfigurationField_eq h0 hx, configurationField_trimer hD hP h0 hx]
    norm_num
    ring

/-- The integer table accepts exactly configurations with at least the target many components. -/
theorem smallConfigurationField_threshold {D : Finset ℕ} {A0 h : ℕ} {P : Finset ℤ}
    (hD : DValid D A0) (hP : PositiveDifferences D P) (h0 : 0 ∈ P) :
    (∀ q ∈ P, ∀ x ∈ component q,
      tau D A0 h ≤ smallConfigurationField (C D A0 h) D P q x) ↔ h ≤ P.card := by
  have hmin := smallConfigurationField_min hD hP h0 (le_of_lt (C_pos D A0 h))
  constructor
  · intro hfield
    have hfield0 := hfield 0 h0 0 (by simp [component])
    rw [hmin.2] at hfield0
    unfold tau at hfield0
    omega
  · intro hh q hq x hx
    have hbound := hmin.1 q hq x hx
    unfold tau
    omega

/-- Integer lifting is additive in the coefficient array. -/
theorem lift_add {m : ℕ} (a b : Power2ModuleSVP.Coeff m) (e : ℤ) :
    lift (a + b) e = lift a e + lift b e := by
  by_cases hm : 0 < m <;> simp [lift, hm, mul_add]

/-- Integer lifting respects subtraction. -/
theorem lift_sub {m : ℕ} (a b : Power2ModuleSVP.Coeff m) (e : ℤ) :
    lift (a - b) e = lift a e - lift b e := by
  by_cases hm : 0 < m <;> simp [lift, hm, mul_sub]

/-- Integer lifting respects integer scalar multiplication. -/
theorem lift_smul {m : ℕ} (c : ℤ) (a : Power2ModuleSVP.Coeff m) (e : ℤ) :
    lift (c • a) e = c * lift a e := by
  by_cases hm : 0 < m <;> simp [lift, hm, mul_left_comm]

/-- Integer lifting commutes with finite sums. -/
theorem lift_finset_sum {ι : Type*} {m : ℕ} (s : Finset ι)
    (a : ι → Power2ModuleSVP.Coeff m) (e : ℤ) :
    lift (∑ j ∈ s, a j) e = ∑ j ∈ s, lift (a j) e := by
  by_cases hm : 0 < m <;> simp [lift, hm, Finset.sum_apply, Finset.mul_sum]

/-- On the short lift, the actual small multiplier has exactly the ordinary kernel. -/
theorem lift_T_eq_kernel {D : Finset ℕ} {A0 : ℕ} (hD : DValid D A0)
    {e : ℤ} (he : |e| ≤ R0 A0) :
    lift (T D A0) e = interactionKernel D e := by
  have hn := separation_lt_n A0
  have he' := abs_le.mp he
  have hk : ∀ k : ℤ, -(R0 A0 : ℤ) ≤ k → k ≤ R0 A0 →
      |e - k| < (n A0 : ℤ) := by
    intro k hk0 hk1
    apply abs_lt.mpr
    constructor <;> omega
  rw [interactionKernel_eq_sum hD, T, lift_finset_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' := hD d hd
  have h0 : (16 : ℤ) * d ≤ R0 A0 := by dsimp [R0, Q]; omega
  have h2 : (16 : ℤ) * d + 2 ≤ R0 A0 := by dsimp [R0, Q]; omega
  simp only [lift_add]
  simp only [Q, Nat.cast_ofNat]
  rw [lift_xpow_near (n_pos A0) e _ (hk _ (by omega) h0),
    lift_xpow_near (n_pos A0) e _ (hk _ (by omega) (by omega)),
    lift_xpow_near (n_pos A0) e _ (hk _ (by omega) h2),
    lift_xpow_near (n_pos A0) e _ (hk _ (by omega) (by omega))]

/-- Convolution can always be restricted to the active coordinates of its second factor. -/
theorem mul_on_support {m : ℕ} (J σ : Power2ModuleSVP.Coeff m) (i : Fin m) :
    IdealCVP.Cyclotomic.mul J σ i =
      ∑ j ∈ support σ, lift J ((i.val : ℤ) - j.val) * σ j := by
  rw [IdealCVP.Cyclotomic.mul_comm, mul_apply_lift]
  calc
    _ = ∑ j ∈ support σ, σ j * lift J ((i.val : ℤ) - j.val) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have hz : σ j = 0 := by simpa only [mem_support, not_not] using hj
      simp [hz]
    _ = _ := by apply Finset.sum_congr rfl; intro j _; ring

/-- Negacyclic convolution on an active short arc is ordinary kernel convolution. -/
theorem mul_T_on_short_support {D : Finset ℕ} {A0 : ℕ}
    (hD : DValid D A0) (σ : Power2ModuleSVP.Coeff (n A0))
    (i : Fin (n A0))
    (hshort : ∀ j ∈ support σ, |(i.val : ℤ) - j.val| ≤ R0 A0) :
    IdealCVP.Cyclotomic.mul (T D A0) σ i =
      ∑ j ∈ support σ, interactionKernel D ((i.val : ℤ) - j.val) * σ j := by
  rw [mul_on_support]
  apply Finset.sum_congr rfl
  intro j hj
  rw [lift_T_eq_kernel hD (hshort j hj)]

/-- The actual nearest-neighbour multiplier has its ordinary kernel on the short lift. -/
theorem lift_neighbors_eq_kernel {A0 : ℕ} {e : ℤ} (he : |e| ≤ R0 A0) :
    lift (xpow (n A0) 1 + xpow (n A0) (-1)) e = neighborKernel e := by
  have hn := separation_lt_n A0
  have he' := abs_le.mp he
  have hm : |e - 1| < (n A0 : ℤ) := abs_lt.mpr ⟨by omega, by omega⟩
  have hp : |e - (-1)| < (n A0 : ℤ) := abs_lt.mpr ⟨by omega, by omega⟩
  rw [lift_add, lift_xpow_near (n_pos A0) e 1 hm,
    lift_xpow_near (n_pos A0) e (-1) hp]
  unfold neighborKernel
  split_ifs <;> omega

/-- Allowed short offsets have zero guard coefficient in the integer lift. -/
theorem lift_A_eq_zero {D : Finset ℕ} {A0 : ℕ} {e : ℤ}
    (he : |e| ≤ R0 A0) (ha : e = 0 ∨ e.natAbs ∈ Eplus D) :
    lift (A D A0) e = 0 := by
  have hn := separation_lt_n A0
  have he' := abs_le.mp he
  rw [A, lift_finset_sum]
  apply Finset.sum_eq_zero
  intro j _
  have hd := mem_forbidden_iff.mp (forbiddenAt_mem D A0 j)
  have hneq : e ≠ (forbiddenAt D A0 j : ℤ) ∧ e ≠ -(forbiddenAt D A0 j : ℤ) := by
    constructor <;> intro heq <;> rcases ha with h0 | ha
    · omega
    · apply hd.2.2
      simpa only [heq, Int.natAbs_natCast] using ha
    · omega
    · apply hd.2.2
      simpa only [heq, Int.natAbs_neg, Int.natAbs_natCast] using ha
  rw [lift_smul, lift_sub,
    lift_xpow_near (n_pos A0) e _ (abs_lt.mpr ⟨by omega, by omega⟩),
    lift_xpow_near (n_pos A0) e _ (abs_lt.mpr ⟨by omega, by omega⟩)]
  simp [hneq.1, hneq.2]

end Power2IdealSVP.Spin
