module

public import Power2ModuleSVP.Coloring.Partial.ProjectorTable
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Rat.Floor

/-!
# The exact rational partial-coloring walk

Define normalization, direction selection, cube truncation, and weight updates using exact
rational comparisons. Rational ceiling square roots give the required factor-two normalization.
Global semantic estimates and runtime bounds are developed separately.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP.PartialColoringAlg

open scoped BigOperators

def ceilSqrt (n : ℕ) : ℕ := if n = 0 then 0 else Nat.sqrt (n - 1) + 1

theorem ceilSqrt_bounds {n : ℕ} (hn : 0 < n) :
    0 < ceilSqrt n ∧ n ≤ ceilSqrt n ^ 2 ∧ ceilSqrt n ^ 2 < 4 * n := by
  rw [ceilSqrt, ite_eq_right (by omega : n ≠ 0)]
  have h₁ := Nat.sqrt_le' (n - 1)
  have h₂ := Nat.lt_succ_sqrt' (n - 1)
  have h₃ := Nat.sqrt_le_self (n - 1)
  have h₄ : n - 1 + 1 = n := by omega
  refine ⟨by omega, by nlinarith, by nlinarith⟩

/-- A polynomial-size rational upper bound for the square root of a
positive rational. The value at nonpositive arguments is irrelevant. -/
def normScale (s : ℚ) : ℚ := (ceilSqrt (s.num.natAbs * s.den) : ℚ) / s.den

theorem normScale_bounds {s : ℚ} (hs : 0 < s) :
    0 < normScale s ∧ s ≤ normScale s ^ 2 ∧ normScale s ^ 2 < 4 * s := by
  have hn : 0 < s.num := Rat.num_pos.mpr hs
  have ha : 0 < s.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt hn)
  have hd : (0 : ℚ) < s.den := by exact_mod_cast s.den_pos
  have han : (s.num.natAbs : ℚ) = (s.num : ℚ) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hn.le]
  have hid : s * (s.den : ℚ) = (s.num.natAbs : ℚ) := by
    rw [han]
    exact ((div_eq_iff hd.ne').mp s.num_div_den).symm
  obtain ⟨hpos, hlo, hhi⟩ := ceilSqrt_bounds (Nat.mul_pos ha s.den_pos)
  have hpos' : (0 : ℚ) < ceilSqrt (s.num.natAbs * s.den) := by exact_mod_cast hpos
  have hlo' : (s.num.natAbs : ℚ) * s.den ≤
      (ceilSqrt (s.num.natAbs * s.den) : ℚ) ^ 2 := by exact_mod_cast hlo
  have hhi' : (ceilSqrt (s.num.natAbs * s.den) : ℚ) ^ 2 <
      4 * ((s.num.natAbs : ℚ) * s.den) := by exact_mod_cast hhi
  refine ⟨div_pos hpos' hd, ?_, ?_⟩
  · unfold normScale
    rw [div_pow, le_div_iff₀ (sq_pos_of_pos hd)]
    nlinarith [hid]
  · unfold normScale
    rw [div_pow, div_lt_iff₀ (sq_pos_of_pos hd)]
    nlinarith [hid]

def normalize {r : ℕ} (v : Vec r) : Vec r := (normScale (dot v v))⁻¹ • v

theorem normalize_bounds {r : ℕ} (v : Vec r) (hv : v ≠ 0) :
    (1 : ℚ) / 4 < dot (normalize v) (normalize v) ∧
      dot (normalize v) (normalize v) ≤ 1 := by
  have hp : 0 < dot v v := lt_of_le_of_ne (dot_self_nonneg v)
    (Ne.symm ((dot_self_eq_zero v).not.mpr hv))
  obtain ⟨hscale, hlo, hhi⟩ := normScale_bounds hp
  have hid : dot (normalize v) (normalize v) = dot v v / normScale (dot v v) ^ 2 := by
    rw [normalize, dot_smul_left, dot_smul_right]
    field_simp
  rw [hid]
  constructor
  · apply (lt_div_iff₀ (sq_pos_of_pos hscale)).mpr
    linarith
  · apply (div_le_iff₀ (sq_pos_of_pos hscale)).mpr
    simpa using hlo

def orient {r : ℕ} (x z : Vec r) : Vec r := if 0 ≤ dot x z then z else -z

theorem orient_nonneg {r : ℕ} (x z : Vec r) : 0 ≤ dot x (orient x z) := by
  unfold orient
  split_ifs with h
  · exact h
  · have hid : dot x (-z) = -dot x z := by simp [dot]
    rw [hid]
    exact neg_nonneg.mpr (le_of_not_ge h)

def stepSize (r : ℕ) : ℚ := 1 / (16 * r)
def stepBudget (r : ℕ) : ℕ := 2048 * r ^ 3
def precision (r m : ℕ) : ℕ := (1024 * m * (stepBudget r + 1)).size
def mesh (r m : ℕ) : ℚ := 1 / (2 : ℚ) ^ precision r m

theorem mesh_pos (r m : ℕ) : 0 < mesh r m := by
  unfold mesh
  positivity

def roundUp (η w : ℚ) : ℚ := η * (⌈w / η⌉ : ℤ)

theorem roundUp_bounds {η : ℚ} (hη : 0 < η) (w : ℚ) :
    w ≤ roundUp η w ∧ roundUp η w < w + η := by
  unfold roundUp
  have hlo := Int.le_ceil (w / η)
  have hhi := Int.ceil_lt_add_one (w / η)
  constructor
  · simpa only [mul_comm] using (div_le_iff₀ hη).mp hlo
  · have h := mul_lt_mul_of_pos_left hhi hη
    have he : η * (w / η + 1) = w + η := by field_simp
    simpa only [he] using h

/-- A half-mesh final rounding leaves half a mesh for an enclosing
approximation. There is no need to decide whether the target is on a grid
boundary. -/
theorem roundUp_half_enclosure {η w : ℚ} {target : ℝ} (hη : 0 < η)
    (hlo : target ≤ (w : ℝ)) (hhi : (w : ℝ) ≤ target + (η : ℝ) / 2) :
    target ≤ (roundUp (η / 2) w : ℝ) ∧
      (roundUp (η / 2) w : ℝ) < target + (η : ℝ) := by
  obtain ⟨hl, hh⟩ := roundUp_bounds (by positivity : 0 < η / 2) w
  have hl' : (w : ℝ) ≤ (roundUp (η / 2) w : ℝ) := by exact_mod_cast hl
  have hh' : (roundUp (η / 2) w : ℝ) < (w : ℝ) + (η : ℝ) / 2 := by exact_mod_cast hh
  exact ⟨hlo.trans hl', by linarith⟩

/-- Rational Taylor sum, evaluated without transcendental operations. -/
def expSum (s : ℚ) (L : ℕ) : ℚ :=
  ((List.range L).map fun k => s ^ k / (Nat.factorial k : ℚ)).sum

def initialWeight (r m : ℕ) (lam : ℚ) : ℚ :=
  roundUp (mesh r m / 2) ((expSum (lam ^ 2) (max (32 * r) (precision r m + 4)))⁻¹)

structure Row (r : ℕ) where
  a : Vec r
  threshold : ℚ

/-- Remove the irrelevant rows and store both signs of each retained row. -/
def prepareRows {r m : ℕ} (V : Fin m → Vec r) (lam : Fin m → ℚ) : List (Row r) :=
  (List.ofFn fun i : Fin m => i).flatMap fun i =>
    if dot (V i) (V i) = 0 ∨ 4 * (r : ℚ) < lam i ^ 2 then []
    else [⟨normalize (V i), lam i⟩, ⟨-normalize (V i), lam i⟩]

structure State (r m : ℕ) where
  x : Vec r
  w : Fin m → ℚ

def damping {r m : ℕ} (a : Fin m → Row r) (i : Fin m) : ℚ :=
  1 - 4 * stepSize r ^ 2 * (a i).threshold ^ 2 / r

def heavyRows {r m : ℕ} (w : Fin m → ℚ) : List (Fin m) :=
  ((List.finRange m).mergeSort (fun i j => decide (w j ≤ w i))).take ((r + 7) / 8)

def constraints {r m : ℕ} (a : Fin m → Row r) (s : State r m) : List (Vec r) :=
  let fixed := ((List.finRange r).filter fun j => s.x j = -1 ∨ s.x j = 1).map coordinate
  let heavy := (heavyRows (r := r) s.w).map fun i => (a i).a
  let small := ((List.finRange m).filter fun i => (a i).threshold ≤ 1).map fun i => (a i).a
  let h : Vec r := fun j => ∑ i, s.w i * damping a i * (a i).threshold * (a i).a j
  h :: (fixed ++ heavy ++ small)

def quadraticRows {r m : ℕ} (a : Fin m → Row r) (s : State r m) : List (ℚ × Vec r) :=
  List.ofFn fun i => (s.w i * (a i).threshold ^ 2, (a i).a)

def direction {r m : ℕ} (a : Fin m → Row r) (s : State r m) : Vec r :=
  orient s.x (normalize (bestColumn (quadraticRows a s) (cachedColumns (constraints a s))))

/-- The first cube boundary in a given coordinate, with one as the cap for
zero directions. Taking the minimum with one implements full steps. -/
def capacity {r : ℕ} (x z : Vec r) (j : Fin r) : ℚ :=
  if 0 < z j then (1 - x j) / (stepSize r * z j)
  else if z j < 0 then (-1 - x j) / (stepSize r * z j) else 1

def stepFraction {r : ℕ} (x z : Vec r) : ℚ :=
  ((List.finRange r).map (capacity x z)).foldr min 1

def nextState {r m : ℕ} (a : Fin m → Row r) (s : State r m) : State r m :=
  let z := direction a s
  let α := stepFraction s.x z
  let y := α • z
  { x := s.x + stepSize r • y
    w := fun i =>
      let t := stepSize r * (a i).threshold * dot (a i).a y
      roundUp (mesh r m) (s.w i * damping a i * (1 + t + t ^ 2)) }

def walk {r m : ℕ} (a : Fin m → Row r) : ℕ → State r m → State r m
  | 0, s => s
  | fuel + 1, s =>
    if r ≤ 2 * signCoordinateCount s.x then s else walk a fuel (nextState a s)

def initialState {r m : ℕ} (a : Fin m → Row r) (x : Vec r) : State r m :=
  ⟨x, fun i => initialWeight r m (a i).threshold⟩

def run {r m : ℕ} (a : Fin m → Row r) (x : Vec r) : State r m :=
  walk a (stepBudget r) (initialState a x)

/-- The typed core still returns a list, so its interface is independent of
the representation of finite dimensions. -/
def partialColorCore (r m : ℕ) (V : Fin m → Vec r) (x : Vec r) (lam : Fin m → ℚ) : List ℚ :=
  let rows := prepareRows V lam
  if rows.isEmpty then List.ofFn fun j => nearestRationalSign (x j)
  else
    List.ofFn (run rows.get x).x

/-- Cheap rational checks; the transcendental entropy budget is deliberately
absent. In particular, points outside the cube do not enter the walk. -/
def validInput (input : PartialColoringInput) : Bool :=
  (input.1.all fun row => decide (row.length = input.2.1.length)) &&
    decide (input.2.2.length = input.1.length) &&
    (input.2.1.all fun q => decide (|q| ≤ 1)) &&
    (input.2.2.all fun q => decide (0 ≤ q))

theorem validInput_of_cube {r m : ℕ} (V : Fin m → Vec r) (x : Vec r) (c : Fin m → ℚ)
    (hx : RationalCube x) (hc : ∀ i, 0 ≤ c i) :
    validInput (partialColoringInput V x c) = true := by
  have hx' : ∀ j, |x j| ≤ 1 := by intro j; exact_mod_cast hx j
  simp [validInput, partialColoringInput, List.all_eq_true, hx', hc]

/-- The concrete total list program. Correctness of its nontrivial branch
is still a global walk-analysis obligation, not a theorem of this file. -/
def partialColor (input : PartialColoringInput) : List ℚ :=
  let r := input.2.1.length
  let m := input.1.length
  if validInput input then
    partialColorCore r m (fun i j => (input.1.getD i []).getD j 0)
      (fun j => input.2.1.getD j 0) (fun i => input.2.2.getD i 0)
  else input.2.1.map nearestRationalSign

theorem partialColor_length (input : PartialColoringInput) :
    (partialColor input).length = input.2.1.length := by
  unfold partialColor partialColorCore
  dsimp only
  split_ifs <;> simp

theorem partialColor_on_input {r m : ℕ} (V : Fin m → Vec r) (x : Vec r)
    (c : Fin m → ℚ) (hx : RationalCube x) (hc : ∀ i, 0 ≤ c i) :
    partialColor (partialColoringInput V x c) =
      if (prepareRows V c).isEmpty then List.ofFn fun j => nearestRationalSign (x j)
      else List.ofFn (run (prepareRows V c).get x).x := by
  have hv := validInput_of_cube V x c hx hc
  unfold partialColor
  rw [ite_eq_left hv]
  change partialColorCore _ _ _ _ _ = partialColorCore r m V x c
  congr! 3
  · simp [partialColoringInput]
  · simp [partialColoringInput]
  · simp [partialColoringInput]
  · rename_i i i' hi j j' hj
    have hi' := Fin.val_eq_val_of_heq hi
    have hj' := Fin.val_eq_val_of_heq hj
    simp [partialColoringInput, List.getD_eq_getElem?_getD, hi', hj']
  · rename_i j j' hj
    have hj' := Fin.val_eq_val_of_heq hj
    simp [partialColoringInput, List.getD_eq_getElem?_getD, hj']
  · rename_i i i' hi
    have hi' := Fin.val_eq_val_of_heq hi
    simp [partialColoringInput, List.getD_eq_getElem?_getD, hi']

theorem direction_orthogonal {r m : ℕ} (a : Fin m → Row r) (s : State r m) :
    OrthogonalTo (constraints a s) (direction a s) := by
  have h := bestColumn_orthogonal (quadraticRows a s) (constraints a s)
  intro q hq
  simp only [direction, cachedColumns_eq]
  unfold orient normalize
  split_ifs
  · rw [dot_smul_right, h q hq, mul_zero]
  · have hid (v : Vec r) : dot q (-v) = -dot q v := by simp [dot]
    rw [hid, dot_smul_right, h q hq, mul_zero, neg_zero]

theorem nextState_fixed {r m : ℕ} (a : Fin m → Row r) (s : State r m)
    (j : Fin r) (hj : s.x j = -1 ∨ s.x j = 1) : (nextState a s).x j = s.x j := by
  have hc : coordinate j ∈ constraints a s := by
    simp only [constraints, List.mem_cons, List.mem_append, List.mem_map]
    exact Or.inr (Or.inl (Or.inl ⟨j, by simp [hj], rfl⟩))
  have h := direction_orthogonal a s (coordinate j) hc
  simp only [dot_coordinate] at h
  simp [nextState, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h]

theorem nextState_small_row {r m : ℕ} (a : Fin m → Row r) (s : State r m)
    (i : Fin m) (hi : (a i).threshold ≤ 1) :
    dot (a i).a (nextState a s).x = dot (a i).a s.x := by
  have hc : (a i).a ∈ constraints a s := by
    simp only [constraints, List.mem_cons, List.mem_append, List.mem_map]
    exact Or.inr (Or.inr ⟨i, by simp [hi], rfl⟩)
  have h := direction_orthogonal a s (a i).a hc
  have hadd (u v : Vec r) : dot (a i).a (u + v) = dot (a i).a u + dot (a i).a v := by
    simp [dot, mul_add, Finset.sum_add_distrib]
  simp only [nextState, hadd, dot_smul_right, h, mul_zero, add_zero]

end Power2ModuleSVP.PartialColoringAlg
