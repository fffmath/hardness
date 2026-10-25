module

public import Power2ModuleSVP.Coloring.Partial.Invariants
public import Mathlib.Data.Rat.Lemmas
public import Power2ModuleSVP.Runtime.Coloring.Arithmetic
public import Mathlib.Data.Nat.Cast.Field

/-!
# Denominators

Common denominators for coloring coordinates. Only weights are rounded to a
mesh. A common denominator for all coordinates, rather than a separate
height recurrence per arithmetic operation, makes the coordinate growth
additive. These results do not assume a projector bit bound.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP.ColoringNative

open scoped BigOperators
open PartialColoringAlg

/-- All canonical coordinate denominators divide the same natural. -/
def CommonDen {r : ℕ} (D : ℕ) (x : Vec r) : Prop := ∀ j, (x j).den ∣ D

/-- Clearing a canonical denominator gives a shared integral numerator. -/
theorem eq_int_div_of_den_dvd {D : ℕ} (hD : 0 < D) (q : ℚ) (hq : q.den ∣ D) :
    ∃ n : ℤ, q = (n : ℚ) / D := by
  refine ⟨q.num * (D / q.den : ℕ), ?_⟩
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div_charZero hq]
  calc
    q = (q.num : ℚ) / q.den := q.num_div_den.symm
    _ = _ := by field_simp

/-- Canonical reduction cannot create a new denominator factor. -/
theorem den_dvd_of_eq_int_div {q : ℚ} {n d : ℤ} (h : q = (n : ℚ) / d) :
    q.den ∣ d.natAbs := by
  rw [h, ← Rat.divInt_eq_div]
  simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr (Rat.den_dvd n d)

private theorem den_dvd_nat_of_eq {q : ℚ} {n : ℤ} {D : ℕ}
    (h : q = (n : ℚ) / D) : q.den ∣ D := by
  simpa using den_dvd_of_eq_int_div (d := (D : ℤ)) (by simpa using h)

/-- Full steps multiply the shared denominator by a direction denominator
and the fixed step denominator once, independently of the dimension. -/
theorem fullStep_commonDen {r D E : ℕ} (hD : 0 < D) (hE : 0 < E)
    (x z : Vec r) (hx : CommonDen D x) (hz : CommonDen E z) (δ : ℚ) :
    CommonDen (D * δ.den * E) (x + δ • z) := by
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hE' : (E : ℚ) ≠ 0 := by exact_mod_cast hE.ne'
  have hδ : (δ.den : ℚ) ≠ 0 := by exact_mod_cast δ.den_ne_zero
  intro i
  obtain ⟨p, hp⟩ := eq_int_div_of_den_dvd hD (x i) (hx i)
  obtain ⟨n, hn⟩ := eq_int_div_of_den_dvd hE (z i) (hz i)
  apply den_dvd_nat_of_eq (n := p * δ.den * E + δ.num * n * D)
  change x i + δ * z i = _
  rw [hp, hn]
  conv_lhs => rw [← δ.num_div_den]
  push_cast
  field_simp

/-- Boundary truncation cancels the shared direction denominator. The new
shared denominator contains the old one just once. -/
theorem truncatedStep_commonDen {r D E : ℕ} (hD : 0 < D) (hE : 0 < E)
    (p n : Fin r → ℤ) (j : Fin r) (hn : n j ≠ 0) (ε : ℤ) :
    CommonDen (D * (n j).natAbs)
      (fun i => (p i : ℚ) / D + ((ε : ℚ) - (p j : ℚ) / D) *
        ((n i : ℚ) / E) / ((n j : ℚ) / E)) := by
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hE' : (E : ℚ) ≠ 0 := by exact_mod_cast hE.ne'
  have hn' : (n j : ℚ) ≠ 0 := by exact_mod_cast hn
  intro i
  have heq : (p i : ℚ) / D + ((ε : ℚ) - (p j : ℚ) / D) *
      ((n i : ℚ) / E) / ((n j : ℚ) / E) =
      ((p i * n j + (ε * D - p j) * n i : ℤ) : ℚ) / ((D : ℤ) * n j) := by
    push_cast
    field_simp
  have hd := den_dvd_of_eq_int_div (n := p i * n j + (ε * D - p j) * n i)
    (d := (D : ℤ) * n j) (by simpa only [Int.cast_mul] using heq)
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hd

/-- An attained minimum of the capacities is either the full-step cap or
one actual coordinate capacity. -/
theorem stepFraction_eq_one_or_capacity {r : ℕ} (x z : Vec r) :
    stepFraction x z = 1 ∨ ∃ j, stepFraction x z = capacity x z j := by
  have hlist (l : List ℚ) : l.foldr min 1 = 1 ∨ l.foldr min 1 ∈ l := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.foldr_cons]
      by_cases ha : a ≤ l.foldr min 1
      · exact Or.inr (by simp [min_eq_left ha])
      · rw [min_eq_right (le_of_not_ge ha)]
        exact ih.imp_right (fun h => List.mem_cons_of_mem a h)
  rcases hlist ((List.finRange r).map (capacity x z)) with h | h
  · exact Or.inl h
  · obtain ⟨j, _, hj⟩ := List.mem_map.mp h
    exact Or.inr ⟨j, hj.symm⟩

/-- One actual cube step has an additive common-denominator bit bound.
The direction bound is separate from the current point's denominator. -/
theorem cubeStep_commonDen {r D E : ℕ} (hr : 0 < r) (hD : 0 < D) (hE : 0 < E)
    (x z : Vec r) (hx : CommonDen D x) (hz : CommonDen E z)
    (hzbound : ∀ i, |z i| ≤ 1) :
    ∃ D' : ℕ, 0 < D' ∧
      CommonDen D' (x + stepSize r • (stepFraction x z • z)) ∧
      D'.size ≤ D.size + (stepSize r).den.size + E.size := by
  rcases stepFraction_eq_one_or_capacity x z with hfull | ⟨j, hj⟩
  · refine ⟨D * (stepSize r).den * E, by positivity, ?_, ?_⟩
    · simpa only [hfull, one_smul] using fullStep_commonDen hD hE x z hx hz (stepSize r)
    · exact (Nat.size_mul_le _ _).trans
        (Nat.add_le_add_right (Nat.size_mul_le _ _) _)
  · classical
    choose p hp using fun i => eq_int_div_of_den_dvd hD (x i) (hx i)
    choose n hn using fun i => eq_int_div_of_den_dvd hE (z i) (hz i)
    by_cases hz0 : z j = 0
    · have hf : stepFraction x z = 1 := by simp only [capacity, hz0] at hj; simpa using hj
      refine ⟨D * (stepSize r).den * E, by positivity, ?_, ?_⟩
      · simpa only [hf, one_smul] using fullStep_commonDen hD hE x z hx hz (stepSize r)
      · exact (Nat.size_mul_le _ _).trans
          (Nat.add_le_add_right (Nat.size_mul_le _ _) _)
    · have hnj : n j ≠ 0 := by intro h; apply hz0; simp [hn j, h]
      have hnjpos : 0 < (n j).natAbs := Int.natAbs_pos.mpr hnj
      have hnle : (n j).natAbs ≤ E := by
        have hE' : (0 : ℚ) < E := by exact_mod_cast hE
        have habs := hzbound j
        rw [hn j, abs_div, abs_of_pos hE', div_le_one hE'] at habs
        have ha : (|(n j)| : ℤ) ≤ (E : ℤ) := by exact_mod_cast habs
        rw [← Int.natCast_natAbs] at ha
        exact_mod_cast ha
      let ε : ℤ := if 0 < z j then 1 else -1
      have heq : x + stepSize r • (stepFraction x z • z) =
          fun i => (p i : ℚ) / D + ((ε : ℚ) - (p j : ℚ) / D) *
            ((n i : ℚ) / E) / ((n j : ℚ) / E) := by
        funext i
        change x i + stepSize r * (stepFraction x z * z i) = _
        rw [← hn i, ← hn j, ← hp i, ← hp j, hj]
        dsimp only [ε]
        unfold capacity
        split_ifs with hpos hneg
        · have hδ := (stepSize_pos hr).ne'
          push_cast
          field_simp
        · have hδ := (stepSize_pos hr).ne'
          push_cast
          field_simp
        · exact False.elim (hz0 (by linarith))
      refine ⟨D * (n j).natAbs, Nat.mul_pos hD hnjpos, ?_, ?_⟩
      · rw [heq]
        exact truncatedStep_commonDen hD hE p n j hnj ε
      · have hs := Nat.size_le_size hnle
        have hm := Nat.size_mul_le D (n j).natAbs
        omega

theorem normalize_dot_self_le {r : ℕ} (v : Vec r) :
    dot (normalize v) (normalize v) ≤ 1 := by
  by_cases hv : v = 0
  · simp [hv, PartialColoringAlg.normalize]
  · exact (normalize_bounds v hv).2

theorem coordinate_abs_le_of_dot_self_le {r : ℕ} (v : Vec r)
    (hv : dot v v ≤ 1) (j : Fin r) : |v j| ≤ 1 := by
  have hs : v j * v j ≤ dot v v :=
    Finset.single_le_sum (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ j)
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Normalizing zero, or a projector with no nonzero column, is harmless
for the size estimates; progress is a separate semantic question. -/
theorem direction_coordinate_bound {r m : ℕ} (a : Fin m → Row r) (s : State r m)
    (j : Fin r) : |direction a s j| ≤ 1 := by
  have h := coordinate_abs_le_of_dot_self_le _
    (normalize_dot_self_le (bestColumn (quadraticRows a s) (cachedColumns (constraints a s)))) j
  unfold direction orient
  split_ifs
  · exact h
  · simpa only [Pi.neg_apply, abs_neg] using h

/-- Only the Boolean set of frozen coordinates is read from the point
when constructing the projection constraints. -/
theorem constraints_eq_of_weights_and_fixed {r m : ℕ} (a : Fin m → Row r)
    (s t : State r m) (hw : s.w = t.w)
    (hf : ∀ j, (s.x j = -1 ∨ s.x j = 1) ↔ (t.x j = -1 ∨ t.x j = 1)) :
    constraints a s = constraints a t := by
  have hfilter : ((List.finRange r).filter fun j => s.x j = -1 ∨ s.x j = 1) =
      ((List.finRange r).filter fun j => t.x j = -1 ∨ t.x j = 1) := by
    apply List.filter_congr
    intro j hj
    exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using hf j)
  simp only [constraints, hw, hfilter]

/-- Changing the unfrozen point, including all its denominator bits,
changes a direction only by its orientation sign. -/
theorem direction_eq_or_neg_of_weights_and_fixed {r m : ℕ} (a : Fin m → Row r)
    (s t : State r m) (hw : s.w = t.w)
    (hf : ∀ j, (s.x j = -1 ∨ s.x j = 1) ↔ (t.x j = -1 ∨ t.x j = 1)) :
    direction a s = direction a t ∨ direction a s = -direction a t := by
  have hc := constraints_eq_of_weights_and_fixed a s t hw hf
  have hq : quadraticRows a s = quadraticRows a t := by simp only [quadraticRows, hw]
  simp only [direction, hc, hq, orient]
  split_ifs <;> simp

/-- In particular, exact coordinate denominators do not feed back into
projector/direction denominators. -/
theorem direction_den_eq_of_weights_and_fixed {r m : ℕ} (a : Fin m → Row r)
    (s t : State r m) (hw : s.w = t.w)
    (hf : ∀ j, (s.x j = -1 ∨ s.x j = 1) ↔ (t.x j = -1 ∨ t.x j = 1)) (j : Fin r) :
    (direction a s j).den = (direction a t j).den := by
  rcases direction_eq_or_neg_of_weights_and_fixed a s t hw hf with h | h <;> rw [h]
  rfl

/-- A uniform direction-denominator bound yields an additive coordinate
bound throughout the actual stopped cubic-fuel walk. The only premise
left here concerns the projector/direction, not the current point. -/
theorem walk_commonDen {r m B : ℕ} (hr : 0 < r) (a : Fin m → Row r)
    (P : State r m → Prop) (hpreserve : ∀ s, P s → P (nextState a s))
    (hdirection : ∀ s : State r m, P s → ∃ E : ℕ, 0 < E ∧
      CommonDen E (direction a s) ∧ E.size ≤ B) (fuel D : ℕ) (hD : 0 < D)
    (s : State r m) (hP : P s) (hx : CommonDen D s.x) :
    ∃ D' : ℕ, 0 < D' ∧ CommonDen D' (walk a fuel s).x ∧
      D'.size ≤ D.size + fuel * ((stepSize r).den.size + B) := by
  induction fuel generalizing D s with
  | zero => exact ⟨D, hD, hx, by simp⟩
  | succ fuel ih =>
    rw [walk]
    split_ifs
    · exact ⟨D, hD, hx, by omega⟩
    · obtain ⟨E, hE, hz, hB⟩ := hdirection s hP
      obtain ⟨D₁, hD₁, hx₁, hb₁⟩ := cubeStep_commonDen hr hD hE s.x
        (direction a s) hx hz (direction_coordinate_bound a s)
      obtain ⟨D₂, hD₂, hx₂, hb₂⟩ := ih D₁ hD₁ (nextState a s) (hpreserve s hP) hx₁
      refine ⟨D₂, hD₂, hx₂, ?_⟩
      nlinarith

/-- Bounded cube coordinates charge numerator bits to their common
denominator as well. -/
theorem coordinate_bits_le {r D : ℕ} (hD : 0 < D) (x : Vec r)
    (hx : CommonDen D x) (hcube : RationalCube x) (j : Fin r) :
    ColoringRuntime.rationalBits (x j) ≤ 2 * D.size := by
  have hq := (rationalCube_iff x).mp hcube j
  have hd : (0 : ℚ) < (x j).den := by exact_mod_cast (x j).den_pos
  have hnum : (|(x j).num| : ℚ) ≤ (x j).den := by
    have hn := hq
    conv_lhs at hn => rw [← (x j).num_div_den]
    rw [abs_div, abs_of_pos hd, div_le_one hd] at hn
    exact_mod_cast hn
  have hnum' : (x j).num.natAbs ≤ (x j).den := by
    have hi : (|(x j).num| : ℤ) ≤ ((x j).den : ℤ) := by exact_mod_cast hnum
    rw [← Int.natCast_natAbs] at hi
    exact_mod_cast hi
  have hden := Nat.le_of_dvd hD (hx j)
  have hnsize := Nat.size_le_size (hnum'.trans hden)
  have hdsize := Nat.size_le_size hden
  unfold ColoringRuntime.rationalBits
  omega

/-- The mesh fixes weight denominators independently of their inputs. -/
theorem roundUp_den_dvd (k : ℕ) (w : ℚ) :
    (roundUp (1 / (2 : ℚ) ^ k) w).den ∣ 2 ^ k := by
  apply den_dvd_nat_of_eq (n := ⌈w / (1 / (2 : ℚ) ^ k)⌉)
  simp only [roundUp, Nat.cast_pow, Nat.cast_ofNat]
  ring

theorem nextState_weight_den {r m : ℕ} (a : Fin m → Row r) (s : State r m) (i : Fin m) :
    ((nextState a s).w i).den ∣ 2 ^ precision r m := by
  exact roundUp_den_dvd _ _

/-- Half-mesh initialization adds exactly one possible power of two. -/
theorem initialWeight_den (r m : ℕ) (lam : ℚ) :
    (initialWeight r m lam).den ∣ 2 ^ (precision r m + 1) := by
  unfold initialWeight mesh
  have he : 1 / (2 : ℚ) ^ precision r m / 2 = 1 / (2 : ℚ) ^ (precision r m + 1) := by
    rw [pow_succ]
    ring
  rw [he]
  exact roundUp_den_dvd _ _

/-- All later weights use the coarser mesh, so the initial common dyadic
bound works at every walk stage. -/
theorem walk_weight_den {r m : ℕ} (a : Fin m → Row r) (fuel : ℕ) (s : State r m)
    (hs : ∀ i, (s.w i).den ∣ 2 ^ (precision r m + 1)) :
    ∀ i, ((walk a fuel s).w i).den ∣ 2 ^ (precision r m + 1) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    rw [walk]
    split_ifs
    · exact hs
    · apply ih
      intro i
      exact (nextState_weight_den a s i).trans (pow_dvd_pow 2 (by omega))

theorem run_weight_den {r m : ℕ} (a : Fin m → Row r) (x : Vec r) (i : Fin m) :
    ((run a x).w i).den ∣ 2 ^ (precision r m + 1) :=
  walk_weight_den a _ _ (fun i => initialWeight_den r m (a i).threshold) i

theorem run_weight_den_size {r m : ℕ} (a : Fin m → Row r) (x : Vec r) (i : Fin m) :
    ((run a x).w i).den.size ≤ precision r m + 2 := by
  apply Nat.size_le.mpr
  have hd := Nat.le_of_dvd (by positivity : 0 < 2 ^ (precision r m + 1))
    (run_weight_den a x i)
  exact hd.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-- Multiplying a shared denominator adds bit lengths. -/
theorem denominator_size_mul (D E : ℕ) : (D * E).size ≤ D.size + E.size :=
  Nat.size_mul_le D E

/-- The coordinate-denominator recurrence is linear in the number of
steps once each new direction factor has a uniform bit bound. -/
theorem product_denominator_size (D : ℕ) (factors : List ℕ) {B : ℕ}
    (hB : ∀ E ∈ factors, E.size ≤ B) :
    (D * factors.prod).size ≤ D.size + factors.length * B := by
  induction factors generalizing D with
  | nil => simp
  | cons E es ih =>
    rw [List.prod_cons, ← Nat.mul_assoc]
    have hi := ih (D * E) (fun n hn => hB n (by simp [hn]))
    have he := denominator_size_mul D E
    have hb := hB E (by simp)
    simp only [List.length_cons]
    nlinarith

/-- A common denominator can always be obtained by clearing each coordinate
once. Its bit length is additive in those input denominators. -/
def vectorDen {r : ℕ} (x : Vec r) : ℕ := (List.ofFn fun j => (x j).den).prod

theorem vectorDen_pos {r : ℕ} (x : Vec r) : 0 < vectorDen x := by
  apply List.prod_pos
  intro d hd
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hd
  exact (x j).den_pos

theorem vectorDen_commonDen {r : ℕ} (x : Vec r) : CommonDen (vectorDen x) x := by
  intro j
  exact List.dvd_prod (List.mem_ofFn.mpr ⟨j, rfl⟩)

theorem vectorDen_size {r B : ℕ} (x : Vec r) (hB : ∀ j, (x j).den.size ≤ B) :
    (vectorDen x).size ≤ 1 + r * B := by
  have h := product_denominator_size 1 (List.ofFn fun j => (x j).den) (by
    intro E hE
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hE
    exact hB j)
  simpa only [vectorDen, Nat.one_mul, List.length_ofFn, Nat.size_one] using h

end Power2ModuleSVP.ColoringNative
