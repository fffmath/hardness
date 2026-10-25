import Power2ModuleSVP.Anchor.Screen
import Power2ModuleSVP.Anchor.LocalExpectations

/-!
# Repair

Finite, exact arithmetic for the deterministic anchor repair. The candidate
enumerator uses sums of a fixed number of signed unit vectors, rather than a
box of dimension-dependent exponential size. The exact potential and its
initial estimate implement the private manuscript's `thm:repair`.

Paper: `paper/power2svp.pdf`, Section 5 (Theorems 3–4 and deterministic anchor repair).
-/
namespace Power2ModuleSVP
namespace AnchorRepair
open IdealCVP.Cyclotomic
set_option maxRecDepth 4096
set_option exponentiation.threshold 4096

/-- The fixed screening radius for the half-strength seed bound. -/
def screeningBound : ℕ := 2 ^ 506

theorem screeningBound_ge_three : 3 ≤ screeningBound := by
  calc
    3 ≤ 2 ^ 2 := by decide
    _ ≤ 2 ^ 506 := Nat.pow_le_pow_right (by decide) (by decide)

theorem dyadic_eq_pow_log2 {d : ℕ} (hd : Dyadic d) : d = 2 ^ (Nat.log2 d) := by
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.log2_eq_log_two, Nat.log_pow (by decide)]

/-- Integral coefficient one-norm, used only for sparse enumeration. -/
def mass {d : ℕ} (v : Coeff d) : ℕ := ∑ i, (v i).natAbs

/-- The blank symbol and all signed coefficient unit vectors. -/
def atoms (d : ℕ) : List (Coeff d) :=
  0 :: (List.finRange d).flatMap (fun j => [monomial j 1, -monomial j 1])

/-- Sums of `n` atoms; blanks pad vectors with smaller one-norm. -/
def atomSums (d : ℕ) : ℕ → List (Coeff d)
  | 0 => [0]
  | n + 1 => (atomSums d n).flatMap (fun v => (atoms d).map (fun a => v + a))

theorem zero_mem_atoms (d : ℕ) : (0 : Coeff d) ∈ atoms d := by
  simp [atoms]

theorem monomial_mem_atoms {d : ℕ} (j : Fin d) : monomial j 1 ∈ atoms d := by
  simp only [atoms, List.mem_cons, List.mem_flatMap, List.mem_finRange,
    List.not_mem_nil, or_false, true_and]
  exact Or.inr ⟨j, Or.inl rfl⟩

theorem neg_monomial_mem_atoms {d : ℕ} (j : Fin d) : -monomial j 1 ∈ atoms d := by
  simp only [atoms, List.mem_cons, neg_eq_zero, List.mem_flatMap, List.mem_finRange,
    neg_inj, List.not_mem_nil, or_false, true_and]
  exact Or.inr ⟨j, Or.inr rfl⟩

theorem zero_mem_atomSums (d n : ℕ) : (0 : Coeff d) ∈ atomSums d n := by
  induction n with
  | zero => simp [atomSums]
  | succ n ih =>
    simp only [atomSums, List.mem_flatMap, List.mem_map]
    exact ⟨0, ih, 0, zero_mem_atoms d, by simp⟩

theorem mass_le_sqNorm {d : ℕ} (v : Coeff d) :
    (mass v : ℤ) ≤ IdealCVP.sqNorm v := by
  simp only [mass, Nat.cast_sum, IdealCVP.sqNorm]
  apply Finset.sum_le_sum
  intro i _
  rw [Int.natCast_natAbs]
  rcases le_total 0 (v i) with hi | hi
  · rw [abs_of_nonneg hi]
    have h : v i = 0 ∨ 1 ≤ v i := by omega
    rcases h with h | h <;> nlinarith
  · rw [abs_of_nonpos hi]
    have h : v i = 0 ∨ v i ≤ -1 := by omega
    rcases h with h | h <;> nlinarith

private theorem natAbs_sub_sign {z : ℤ} (hz : z ≠ 0) :
    (z - (if 0 < z then 1 else -1)).natAbs + 1 = z.natAbs := by
  have he : ((z - (if 0 < z then 1 else -1)).natAbs : ℤ) + 1 = z.natAbs := by
    simp only [Int.natCast_natAbs]
    split_ifs with h
    · rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
      omega
    · rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]
      omega
  exact_mod_cast he

private theorem mass_remove {d : ℕ} (v : Coeff d) (j : Fin d) (hj : v j ≠ 0) :
    mass (v - monomial j (if 0 < v j then 1 else -1)) + 1 = mass v := by
  classical
  let w := v - monomial j (if 0 < v j then 1 else -1)
  have he : ∑ i ∈ (Finset.univ.erase j), (w i).natAbs =
      ∑ i ∈ (Finset.univ.erase j), (v i).natAbs := by
    apply Finset.sum_congr rfl
    intro i hi
    have hij := (Finset.mem_erase.mp hi).1
    simp [w, monomial, hij]
  have hv := Finset.sum_erase_add Finset.univ (fun i : Fin d => (v i).natAbs)
    (Finset.mem_univ j)
  have hw := Finset.sum_erase_add Finset.univ (fun i : Fin d => (w i).natAbs)
    (Finset.mem_univ j)
  have hjw : (w j).natAbs + 1 = (v j).natAbs := by
    simpa [w] using natAbs_sub_sign hj
  change (∑ i, (w i).natAbs) + 1 = ∑ i, (v i).natAbs
  omega

/-- Every vector of one-norm at most `n` occurs, including zero and repeats. -/
theorem mem_atomSums_of_mass_le {d n : ℕ} (v : Coeff d) (hv : mass v ≤ n) :
    v ∈ atomSums d n := by
  classical
  induction n generalizing v with
  | zero =>
    have hz : v = 0 := by
      funext i
      have hi : (v i).natAbs ≤ mass v := by
        apply Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have : (v i).natAbs = 0 := by omega
      exact Int.natAbs_eq_zero.mp this
    subst v
    exact zero_mem_atomSums d 0
  | succ n ih =>
    by_cases hz : v = 0
    · subst v
      exact zero_mem_atomSums d (n + 1)
    · obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
        by_contra h
        apply hz
        ext i
        simpa using not_exists.mp h i
      let t : ℤ := if 0 < v j then 1 else -1
      let a : Coeff d := monomial j t
      let w := v - a
      have hw : mass w ≤ n := by
        have := mass_remove v j hj
        change mass w + 1 = mass v at this
        omega
      have ha : a ∈ atoms d := by
        dsimp [a, t]
        split_ifs
        · exact monomial_mem_atoms j
        · have he : monomial j (-1) = -monomial j 1 := by
            ext i
            by_cases hi : i = j <;> simp [monomial, hi]
          rw [he]
          exact neg_monomial_mem_atoms j
      simp only [atomSums, List.mem_flatMap, List.mem_map]
      exact ⟨w, ih w hw, a, ha, sub_add_cancel v a⟩

/-- Finite support in the coefficient representation. -/
def support {d : ℕ} (v : Coeff d) : Finset (Fin d) :=
  Finset.univ.filter (fun j => v j ≠ 0)

/-- The sparse candidate list. Multiplicity is harmless for the potential;
its cardinality estimate must consequently bound this actual list. -/
def candidates (d n : ℕ) : List (Coeff d) :=
  (atomSums d n).filter (fun v => 2 ≤ (support v).card ∧ IdealCVP.sqNorm v ≤ n)

theorem mem_candidates {d n : ℕ} (v : Coeff d)
    (hs : 2 ≤ (support v).card) (hv : IdealCVP.sqNorm v ≤ n) :
    v ∈ candidates d n := by
  have hm : mass v ≤ n := by
    exact_mod_cast (mass_le_sqNorm v).trans hv
  simp only [candidates, List.mem_filter, decide_eq_true_eq]
  exact ⟨mem_atomSums_of_mass_le v hm, hs, hv⟩

/-- The list-level row tests and coefficient-level screen use the same support. -/
theorem testSupport_eq {d : ℕ} (v : Coeff d) :
    AnchorTests.multiplierSupport d (IdealCVP.toList v) =
      (multiplierSupport v).map Fin.valEmbedding := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨hj, hn⟩ := Finset.mem_filter.mp hj
    have hlt := Finset.mem_range.mp hj
    apply Finset.mem_map.mpr
    refine ⟨⟨j, hlt⟩, ?_, rfl⟩
    simp only [mem_multiplierSupport]
    have he := congrFun (IdealCVP.ofList_toList v) ⟨j, hlt⟩
    change (IdealCVP.toList v).getD j 0 = v ⟨j, hlt⟩ at he
    rwa [← he]
  · intro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr i.isLt, ?_⟩
    have he := congrFun (IdealCVP.ofList_toList v) i
    change (IdealCVP.toList v).getD i.val 0 = v i at he
    change (IdealCVP.toList v).getD i.val 0 ≠ 0
    rw [he]
    simpa using hi

theorem testSupport_card {d : ℕ} (v : Coeff d) :
    (AnchorTests.multiplierSupport d (IdealCVP.toList v)).card = (multiplierSupport v).card := by
  rw [testSupport_eq, Finset.card_map]

theorem candidate_support_bounds {d n : ℕ} (v : Coeff d) (hv : v ∈ candidates d n) :
    2 ≤ (AnchorTests.multiplierSupport d (IdealCVP.toList v)).card ∧
      (AnchorTests.multiplierSupport d (IdealCVP.toList v)).card ≤ n := by
  have hfilter := (List.mem_filter.mp hv).2
  have hc : 2 ≤ (support v).card ∧ IdealCVP.sqNorm v ≤ n := by simpa using hfilter
  rw [testSupport_card]
  refine ⟨hc.1, ?_⟩
  have hcard := (support_card_le_sqNorm v).trans hc.2
  exact_mod_cast hcard

theorem atoms_length (d : ℕ) : (atoms d).length = 1 + 2 * d := by
  simp [atoms, List.length_flatMap, List.map_const', List.sum_replicate]
  omega

theorem atomSums_length (d n : ℕ) : (atomSums d n).length = (1 + 2 * d) ^ n := by
  induction n with
  | zero => simp [atomSums]
  | succ n ih =>
    simp [atomSums, List.length_flatMap, atoms_length, List.map_const',
      List.sum_replicate, ih, pow_succ]

theorem candidates_length_le (d n : ℕ) : (candidates d n).length ≤ (1 + 2 * d) ^ n := by
  rw [← atomSums_length]
  exact List.length_filter_le _ _

/-- The list itself, with all repetitions, has the required fixed-power bound. -/
theorem candidates_length_le_pow {d n : ℕ} (hd : 3 ≤ d) :
    (candidates d n).length ≤ d ^ (2 * n) := by
  calc
    _ ≤ (1 + 2 * d) ^ n := candidates_length_le d n
    _ ≤ (d ^ 2) ^ n := Nat.pow_le_pow_left (by nlinarith) n
    _ = _ := by rw [← pow_mul, Nat.mul_comm 2 n]

/-- Choose a branch using exact rational comparison, with a fixed tie rule. -/
def nextFlag (F : List Bool → ℚ) (σ : List Bool) : Bool :=
  if F (σ ++ [false]) ≤ F (σ ++ [true]) then false else true

/-- Conditional-expectation minimisation for a specified rational potential. -/
def minimize (F : List Bool → ℚ) : ℕ → List Bool → List Bool
  | 0, σ => σ
  | n + 1, σ => minimize F n (σ ++ [nextFlag F σ])

theorem minimize_length (F : List Bool → ℚ) (n : ℕ) (σ : List Bool) :
    (minimize F n σ).length = σ.length + n := by
  induction n generalizing σ with
  | zero => simp [minimize]
  | succ n ih => simp [minimize, ih, Nat.add_comm, Nat.add_left_comm]

theorem nextFlag_le (F : List Bool → ℚ) (σ : List Bool) (p : ℚ)
    (hp : 0 ≤ p) (hp' : p ≤ 1)
    (havg : F σ = (1 - p) * F (σ ++ [false]) + p * F (σ ++ [true])) :
    F (σ ++ [nextFlag F σ]) ≤ F σ := by
  unfold nextFlag
  split_ifs with h
  · have := mul_nonneg hp (sub_nonneg.mpr h)
    nlinarith
  · have := mul_nonneg (sub_nonneg.mpr hp') (sub_nonneg.mpr (le_of_not_ge h))
    nlinarith

/-- A branch-average identity is enough for the deterministic algorithm;
no sample space or real-valued comparison enters this program. -/
theorem minimize_le (F : List Bool → ℚ) (d : ℕ) (p : ℚ)
    (hp : 0 ≤ p) (hp' : p ≤ 1)
    (havg : ∀ σ, σ.length < d →
      F σ = (1 - p) * F (σ ++ [false]) + p * F (σ ++ [true]))
    (n : ℕ) (σ : List Bool) (hlen : σ.length + n ≤ d) :
    F (minimize F n σ) ≤ F σ := by
  induction n generalizing σ with
  | zero => exact le_rfl
  | succ n ih =>
    have hstep := nextFlag_le F σ p hp hp' (havg σ (by omega))
    apply le_trans (ih (σ ++ [nextFlag F σ]) ?_) hstep
    simp only [List.length_append, List.length_singleton]
    omega

/-- Flip precisely the coefficients whose exposed flags are true. -/
def flipped (d : ℕ) (s : List ℤ) (σ : List Bool) : Coeff d := fun i =>
  if σ.getD i.val false then -(IdealCVP.ofList (d := d) s i)
  else IdealCVP.ofList (d := d) s i

theorem flipped_signs {d : ℕ} (s : List ℤ) (σ : List Bool)
    (hs : Signs (IdealCVP.ofList (d := d) s)) : Signs (flipped d s σ) := by
  intro i
  dsimp [flipped]
  rcases hs i with h | h <;> cases σ.getD i.val false <;> simp [h]

/-- The coordinates changed by the flag word. -/
def flipSet (d : ℕ) (σ : List Bool) : Finset (Fin d) :=
  Finset.univ.filter fun i => σ.getD i.val false = true

theorem flipped_eq_off_set {d : ℕ} (s : List ℤ) (σ : List Bool)
    (i : Fin d) (hi : i ∉ flipSet d σ) :
    flipped d s σ i = IdealCVP.ofList (d := d) s i := by
  have h : σ.getD i.val false = false := by
    simpa [flipSet] using hi
  unfold flipped
  rw [h]
  rfl

theorem flipSet_card {d : ℕ} (σ : List Bool) (hlen : σ.length = d) :
    (flipSet d σ).card = σ.count true := by
  have hlist : List.ofFn (fun i : Fin d => σ.getD i.val false) = σ := by
    apply List.ext_getElem
    · simpa using hlen.symm
    · intro n hn hm
      simp only [List.getElem_ofFn]
      simp only [List.getD, List.getElem?_eq_getElem hm, Option.getD_some]
  have hc := (List.nodup_finRange d).card_eq_countP
    (P := fun i : Fin d => σ.getD i.val false = true)
  calc
    _ = (List.finRange d).countP (fun i => σ.getD i.val false) := by
      simpa [flipSet] using hc
    _ = (List.ofFn (fun i : Fin d => σ.getD i.val false)).count true := by
      simp [List.ofFn_eq_map, List.count, Function.comp_def]
    _ = _ := by rw [hlist]

/-- The rational Bernoulli parameter; total also on inadmissible degrees. -/
def flipProbability (d : ℕ) : ℚ :=
  (8 * (screeningBound : ℚ) ^ 3 * (Nat.log2 d : ℚ)) / (d : ℚ)

/-- The integral flip budget. -/
def flipBudget (d : ℕ) : ℕ := 16 * screeningBound ^ 3 * Nat.log2 d

/-- The paper's repair dimensions, with the actual fixed spectral constant. -/
def Admissible (d : ℕ) : Prop :=
  Dyadic d ∧ screeningBound ≤ d ∧
    16 * screeningBound ^ 4 * Nat.log2 d ≤ d ∧
    (64 * screeningBound ^ 3 * Nat.log2 d : ℕ) ≤
      (seedConstant : ℝ) * Real.sqrt d

/-- The manuscript's fixed cutoff supplies all explicit repair dimensions. -/
theorem admissible_of_cutoff {d : ℕ} (hd : Dyadic d) (hlarge : 2 ^ 3600 ≤ d) :
    Admissible d := by
  obtain ⟨k, rfl⟩ := hd
  have hk : 3600 ≤ k := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hlarge
  obtain ⟨hC, hdim, hspec⟩ := repair_cutoff k hk
  refine ⟨⟨k, rfl⟩, hC, ?_, ?_⟩
  · simpa only [screeningBound, Nat.log2_eq_log_two, Nat.log_pow (by decide : 1 < (2 : ℕ))]
      using hdim
  · simpa only [screeningBound, Nat.log2_eq_log_two, Nat.log_pow (by decide : 1 < (2 : ℕ))]
      using hspec

/-- Linear expected flip penalty after exposing a prefix. -/
def penalty (d : ℕ) (σ : List Bool) : ℚ :=
  ((σ.count true : ℚ) + flipProbability d * ((d - σ.length : ℕ) : ℚ)) /
    ((flipBudget d : ℚ) + 1)

/-- Exact rational potential, using local expectations on disjoint rows. -/
def potential (d : ℕ) (s : List ℤ) (σ : List Bool) : ℚ :=
  penalty d σ + ((candidates d screeningBound).map (fun v =>
    AnchorTests.eventProbability d s (IdealCVP.toList v) σ (flipProbability d))).sum

theorem penalty_branch {d : ℕ} (σ : List Bool) (hlen : σ.length < d) :
    penalty d σ =
      (1 - flipProbability d) * penalty d (σ ++ [false]) +
      flipProbability d * penalty d (σ ++ [true]) := by
  have hn : d - σ.length = (d - (σ.length + 1)) + 1 := by omega
  unfold penalty
  simp only [List.count_append, List.count_cons, List.count_nil,
    List.length_append, List.length_singleton]
  simp only [show (false == true) = false from rfl,
    show (true == true) = true from rfl, Bool.false_eq_true, ite_false, ite_true]
  rw [hn]
  push_cast
  ring

private theorem sum_branch {α : Type*} (xs : List α) (p : ℚ)
    (F : α → List Bool → ℚ) (σ : List Bool)
    (h : ∀ x ∈ xs, F x σ = (1 - p) * F x (σ ++ [false]) + p * F x (σ ++ [true])) :
    (xs.map (fun x => F x σ)).sum =
      (1 - p) * (xs.map (fun x => F x (σ ++ [false]))).sum +
      p * (xs.map (fun x => F x (σ ++ [true]))).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    ring

theorem potential_branch {d : ℕ} (s : List ℤ) (σ : List Bool)
    (hlen : σ.length < d) :
    potential d s σ =
      (1 - flipProbability d) * potential d s (σ ++ [false]) +
      flipProbability d * potential d s (σ ++ [true]) := by
  unfold potential
  rw [penalty_branch σ hlen,
    sum_branch (candidates d screeningBound) (flipProbability d)
      (fun v σ => AnchorTests.eventProbability d s (IdealCVP.toList v) σ
        (flipProbability d)) σ (by
          intro v _
          exact AnchorTests.eventProbability_branch _ _ _ _ _)]
  ring

theorem flipProbability_nonneg (d : ℕ) : 0 ≤ flipProbability d := by
  unfold flipProbability
  positivity

theorem flipProbability_le_one {d : ℕ} (hd : Admissible d) :
    flipProbability d ≤ 1 := by
  have hC : 1 ≤ screeningBound := by
    have hpos : 0 < screeningBound := by unfold screeningBound; positivity
    omega
  have hnum : 8 * screeningBound ^ 3 * Nat.log2 d ≤ d := by
    have hpow : screeningBound ^ 3 ≤ screeningBound ^ 4 :=
      Nat.pow_le_pow_right hC (by decide)
    have hh : 8 * screeningBound ^ 3 ≤ 16 * screeningBound ^ 4 := by omega
    exact (Nat.mul_le_mul_right (Nat.log2 d) hh).trans hd.2.2.1
  unfold flipProbability
  apply (div_le_one (by exact_mod_cast hd.1.pos : (0 : ℚ) < d)).mpr
  exact_mod_cast hnum

/-- The dimension bound gives the sharper parameter used in the row estimate. -/
theorem flipProbability_mul_le {d : ℕ} (hd : Admissible d) :
    flipProbability d * (2 * (screeningBound : ℚ)) ≤ 1 := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd.1.pos
  have hnum : (16 * (screeningBound : ℚ) ^ 4 * (Nat.log2 d : ℚ)) ≤ d := by
    exact_mod_cast hd.2.2.1
  unfold flipProbability
  apply (mul_le_mul_iff_left₀ hdq).mp
  have he : ((8 * (screeningBound : ℚ) ^ 3 * Nat.log2 d) / d *
      (2 * screeningBound)) * (d : ℚ) = 16 * (screeningBound : ℚ) ^ 4 * Nat.log2 d := by
    field_simp [hdq.ne']
    ring
  rw [he, one_mul]
  exact hnum

/-- The expected linear penalty already has the strict half-unit slack;
only the sum of initial survival probabilities remains to be estimated. -/
theorem penalty_nil_lt_half {d : ℕ} (hd : 0 < d) : penalty d [] < 1/2 := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : penalty d [] = (flipBudget d : ℚ) / (2 * ((flipBudget d : ℚ) + 1)) := by
    unfold penalty flipProbability flipBudget
    simp only [List.count_nil, List.length_nil, Nat.sub_zero, Nat.cast_zero]
    push_cast
    field_simp [hdq]
    ring
  rw [he]
  apply (div_lt_iff₀ (by positivity : (0 : ℚ) < 2 * ((flipBudget d : ℚ) + 1))).mpr
  linarith

/-- A uniform local survival bound multiplies over the disjoint test rows. -/
theorem event_le_pow_of_row_bound (d : ℕ) (s v : List ℤ) (p : ℚ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hrows : ∀ i ∈ AnchorTests.selectedRows d v,
      AnchorTests.rowProbability d s v i [] p ≤ 1 - p / 2) :
    AnchorTests.eventProbability d s v [] p ≤
      (1 - p / 2) ^ (AnchorTests.selectedRows d v).length := by
  unfold AnchorTests.eventProbability
  generalize AnchorTests.selectedRows d v = rows at *
  induction rows with
  | nil => simp
  | cons i rows ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    have hi := hrows i (by simp)
    have ht : ∀ j ∈ rows, AnchorTests.rowProbability d s v j [] p ≤ 1 - p / 2 :=
      fun j hj => hrows j (by simp [hj])
    have hnonneg : 0 ≤ (rows.map (fun j => AnchorTests.rowProbability d s v j [] p)).prod := by
      apply List.prod_nonneg
      intro x hx
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
      exact AnchorTests.rowProbability_nonneg _ _ _ _ _ _ hp hp1
    have hq : 0 ≤ 1 - p / 2 := by linarith
    calc
      _ ≤ (1 - p / 2) * (1 - p / 2) ^ rows.length := mul_le_mul hi (ih ht) hnonneg hq
      _ = _ := mul_comm _ _

private theorem rational_sum_le {α : Type*} (xs : List α) (F : α → ℚ) (K : ℝ)
    (h : ∀ x ∈ xs, (F x : ℝ) ≤ K) :
    (((xs.map F).sum : ℚ) : ℝ) ≤ (xs.length : ℝ) * K := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, Rat.cast_add, List.length_cons,
      Nat.cast_add, Nat.cast_one]
    nlinarith

/-- The disjoint-row estimate and sparse candidate count bound the initial
survival contribution by one half, including enumeration multiplicities. -/
theorem initial_survival_sum_le_half {d : ℕ} (hd : Admissible d) (s : List ℤ)
    (hs : Signs (IdealCVP.ofList (d := d) s)) :
    ((candidates d screeningBound).map (fun v =>
      AnchorTests.eventProbability d s (IdealCVP.toList v) [] (flipProbability d))).sum ≤ 1/2 := by
  have hC : 0 < screeningBound := by have := screeningBound_ge_three; omega
  have hd3 : 3 ≤ d := screeningBound_ge_three.trans hd.2.1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd.1.pos
  have hCR : (0 : ℝ) < screeningBound := by exact_mod_cast hC
  have hp := flipProbability_nonneg d
  have hp1 := flipProbability_le_one hd
  have hparam := flipProbability_mul_le hd
  have hparam' : (screeningBound : ℚ) * flipProbability d ≤ 1/2 := by linarith
  have hpd : (flipProbability d : ℝ) * (d : ℝ) =
      8 * (screeningBound : ℝ) ^ 3 * (Nat.log2 d : ℝ) := by
    unfold flipProbability
    push_cast
    field_simp [hdR.ne']
  have hexponent : -((flipProbability d : ℝ) * d) / (2 * (screeningBound : ℝ) ^ 2) =
      -4 * (screeningBound : ℝ) * (Nat.log2 d : ℝ) := by
    rw [hpd]
    apply (div_eq_iff (by positivity : 2 * (screeningBound : ℝ) ^ 2 ≠ 0)).mpr
    ring
  have hprob : ∀ v ∈ candidates d screeningBound,
      (AnchorTests.eventProbability d s (IdealCVP.toList v) [] (flipProbability d) : ℝ) ≤
        Real.exp (-4 * (screeningBound : ℝ) * (Nat.log2 d : ℝ)) := by
    intro v hv
    obtain ⟨hm2, hmC⟩ := candidate_support_bounds v hv
    have hmp : ((AnchorTests.multiplierSupport d (IdealCVP.toList v)).card : ℚ) *
        flipProbability d ≤ 1/2 := by
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hmC) hp).trans hparam'
    have hprod := event_le_pow_of_row_bound d s (IdealCVP.toList v) (flipProbability d) hp hp1
      (fun i hi => AnchorTests.rowProbability_le_one_sub_half hd.1.pos s (IdealCVP.toList v)
        i (AnchorTests.selectedRows_lt d _ hi) hs hm2 (flipProbability d) hp hp1 hmp)
    have hnonempty : (AnchorTests.multiplierSupport d (IdealCVP.toList v)).Nonempty :=
      Finset.card_pos.mp (by omega)
    have hpacking := AnchorTests.selectedRows_packing d (IdealCVP.toList v) hnonempty
    have hexp := repair_event_exp_bound hC hmC hpacking
      (show (0 : ℝ) ≤ (flipProbability d : ℝ) by exact_mod_cast hp)
      (show (flipProbability d : ℝ) ≤ 1 by exact_mod_cast hp1)
    rw [hexponent] at hexp
    apply le_trans _ hexp
    exact_mod_cast hprod
  have hsum := rational_sum_le (candidates d screeningBound)
    (fun v => AnchorTests.eventProbability d s (IdealCVP.toList v) [] (flipProbability d))
    (Real.exp (-4 * (screeningBound : ℝ) * (Nat.log2 d : ℝ))) hprob
  have hlen : ((candidates d screeningBound).length : ℝ) ≤ (d : ℝ) ^ (2 * screeningBound) := by
    exact_mod_cast candidates_length_le_pow (n := screeningBound) hd3
  have hhalf := repair_union_exp_le_half (C := screeningBound) (dyadic_eq_pow_log2 hd.1)
    (by omega) (by omega)
  have hsumR := hsum.trans ((mul_le_mul_of_nonneg_right hlen
    (Real.exp_nonneg _)).trans hhalf)
  apply (Rat.cast_le (K := ℝ)).mp
  convert hsumR using 1
  norm_num

/-- The initial exact rational potential is strictly below one. -/
theorem initial_potential_lt_one {d : ℕ} (hd : Admissible d) (s : List ℤ)
    (hs : Signs (IdealCVP.ofList (d := d) s)) : potential d s [] < 1 := by
  have hp := penalty_nil_lt_half hd.1.pos
  have hsum := initial_survival_sum_le_half hd s hs
  unfold potential
  linarith

/-- The deterministic flag word chosen by exact conditional expectations. -/
def repairFlags (d : ℕ) (s : List ℤ) : List Bool := minimize (potential d s) d []

theorem repairFlags_length (d : ℕ) (s : List ℤ) : (repairFlags d s).length = d := by
  simp [repairFlags, minimize_length]

theorem repaired_potential_le {d : ℕ} (hd : Admissible d) (s : List ℤ) :
    potential d s (repairFlags d s) ≤ potential d s [] := by
  exact minimize_le (potential d s) d (flipProbability d) (flipProbability_nonneg d)
    (flipProbability_le_one hd) (potential_branch s) d [] (by simp)

theorem survival_sum_nonneg {d : ℕ} (hd : Admissible d) (s : List ℤ) (σ : List Bool) :
    0 ≤ ((candidates d screeningBound).map (fun v =>
      AnchorTests.eventProbability d s (IdealCVP.toList v) σ (flipProbability d))).sum := by
  apply List.sum_nonneg
  intro q hq
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hq
  exact AnchorTests.eventProbability_nonneg _ _ _ _ _ (flipProbability_nonneg d)
    (flipProbability_le_one hd)

theorem penalty_nonneg (d : ℕ) (σ : List Bool) : 0 ≤ penalty d σ := by
  apply div_nonneg
  · exact add_nonneg (Nat.cast_nonneg _) (mul_nonneg (flipProbability_nonneg _) (Nat.cast_nonneg _))
  · positivity

/-- A terminal potential below one certifies the integral flip budget. -/
theorem count_le_budget {d : ℕ} (hd : Admissible d) (s : List ℤ) (σ : List Bool)
    (hlen : σ.length = d) (hW : potential d s σ < 1) :
    σ.count true ≤ flipBudget d := by
  have hsum := survival_sum_nonneg hd s σ
  have hpen : penalty d σ < 1 := by unfold potential at hW; linarith
  have he : penalty d σ = (σ.count true : ℚ) / ((flipBudget d : ℚ) + 1) := by
    simp [penalty, hlen]
  rw [he] at hpen
  have hden : (0 : ℚ) < (flipBudget d : ℚ) + 1 := by positivity
  have hlt := (div_lt_one hden).mp hpen
  have : σ.count true < flipBudget d + 1 := by exact_mod_cast hlt
  omega

/-- A terminal potential below one excludes every enumerated survival event. -/
theorem event_ne_one {d : ℕ} (hd : Admissible d) (s : List ℤ) (σ : List Bool)
    (hW : potential d s σ < 1) (v : Coeff d) (hv : v ∈ candidates d screeningBound) :
    AnchorTests.eventProbability d s (IdealCVP.toList v) σ (flipProbability d) ≠ 1 := by
  intro he
  have hmem : AnchorTests.eventProbability d s (IdealCVP.toList v) σ (flipProbability d) ∈
      (candidates d screeningBound).map (fun w =>
        AnchorTests.eventProbability d s (IdealCVP.toList w) σ (flipProbability d)) :=
    List.mem_map.mpr ⟨v, hv, rfl⟩
  have hsingle := List.single_le_sum (fun q hq => by
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hq
    exact AnchorTests.eventProbability_nonneg d s (IdealCVP.toList w) σ
      (flipProbability d) (flipProbability_nonneg d) (flipProbability_le_one hd)) _ hmem
  rw [he] at hsingle
  have hp := penalty_nonneg d σ
  unfold potential at hW
  linarith

/-- A sign product makes every selected row survive at a terminal prefix. -/
theorem event_eq_one_of_signs {d : ℕ} (hd : 0 < d) (s : List ℤ)
    (σ : List Bool) (hlen : σ.length = d) (v : Coeff d)
    (hv : Signs (mul (flipped d s σ) v)) :
    AnchorTests.eventProbability d s (IdealCVP.toList v) σ (flipProbability d) = 1 := by
  rw [AnchorTests.eventProbability_terminal _ _ _ _ _ hd hlen.ge]
  unfold AnchorTests.eventIndicator
  have hc : (fun k : Fin d => s.getD k.val 0 *
      (if σ.getD k.val false then -1 else 1)) = flipped d s σ := by
    funext k
    unfold flipped IdealCVP.ofList
    cases σ.getD k.val false <;> simp
  have hall : (AnchorTests.selectedRows d (IdealCVP.toList v)).all (fun i =>
      decide (AnchorTests.rowValue d s (IdealCVP.toList v) i (fun j => σ.getD j false) = -1 ∨
        AnchorTests.rowValue d s (IdealCVP.toList v) i (fun j => σ.getD j false) = 1)) = true := by
    apply List.all_eq_true.mpr
    intro i hi
    have hi' : i < d := AnchorTests.selectedRows_lt d _ hi
    have he := AnchorTests.rowValue_eq_mul hd s (IdealCVP.toList v) ⟨i, hi'⟩
      (fun j => σ.getD j false)
    rw [hc, IdealCVP.ofList_toList] at he
    simp only [decide_eq_true_eq]
    simpa only [he] using hv ⟨i, hi'⟩
  rw [hall]
  rfl

/-- The terminal implication for the concrete finite rational potential. -/
theorem rigid_of_initial_potential {d : ℕ} (hd : Admissible d) (s : List ℤ)
    (hs : SpectralSeed d (IdealCVP.ofList (d := d) s))
    (hinit : potential d s [] < 1) : Rigid (flipped d s (repairFlags d s)) := by
  let σ := repairFlags d s
  have hlen : σ.length = d := repairFlags_length d s
  have hW : potential d s σ < 1 := (repaired_potential_le hd s).trans_lt hinit
  have hcount := count_le_budget hd s σ hlen hW
  have hf := flipped_signs s σ hs.signs
  have hsize : 4 * ((flipSet d σ).card : ℝ) ≤ (seedConstant : ℝ) * Real.sqrt d := by
    rw [flipSet_card σ hlen]
    calc
      4 * (σ.count true : ℝ) ≤ 4 * (flipBudget d : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left 4 hcount
      _ = (64 * screeningBound ^ 3 * Nat.log2 d : ℕ) := by
        unfold flipBudget
        push_cast
        ring
      _ ≤ _ := hd.2.2.2
  have hspec := hs.perturbation hd.1.pos hf (flipSet d σ)
    (fun i hi => (flipped_eq_off_set s σ i hi).symm) hsize
  apply rigid_of_candidate_exclusion (C := screeningBound) hd.1 hf
  · intro v hv
    exact half_seed_screen hd.1.pos hspec hv
  · intro v hv hvnorm hsign
    have hmem := mem_candidates v hv hvnorm
    exact event_ne_one hd s σ hW v hmem (event_eq_one_of_signs hd.1.pos s σ hlen v hsign)

end AnchorRepair

/-- The total, exact rational repair program. Its list output always has the
requested degree, including on malformed seeds and inadmissible degrees. -/
def repair (d : ℕ) (s : List ℤ) : List ℤ :=
  IdealCVP.toList (AnchorRepair.flipped d s (AnchorRepair.repairFlags d s))

theorem repair_length (d : ℕ) (s : List ℤ) : (repair d s).length = d := by
  simp [repair]

theorem repair_signs {d : ℕ} (s : List ℤ)
    (hs : Signs (IdealCVP.ofList (d := d) s)) :
    Signs (IdealCVP.ofList (d := d) (repair d s)) := by
  simpa [repair] using AnchorRepair.flipped_signs s (AnchorRepair.repairFlags d s) hs

theorem repair_rigid_of_initial_potential {d : ℕ} (hd : AnchorRepair.Admissible d)
    (s : List ℤ) (hs : SpectralSeed d (IdealCVP.ofList (d := d) s))
    (hinit : AnchorRepair.potential d s [] < 1) :
    Rigid (IdealCVP.ofList (d := d) (repair d s)) := by
  simpa [repair] using AnchorRepair.rigid_of_initial_potential hd s hs hinit

/-- Deterministic repair of a spectral seed is rigid whenever the explicit
dimension inequalities hold. No repair or probability hypothesis is used. -/
theorem repair_rigid {d : ℕ}
    (hd : AnchorRepair.Admissible d) (s : List ℤ)
    (hs : SpectralSeed d (IdealCVP.ofList (d := d) s)) :
    Rigid (IdealCVP.ofList (d := d) (repair d s)) :=
  repair_rigid_of_initial_potential hd s hs (AnchorRepair.initial_potential_lt_one hd s hs.signs)

/-- The deterministic repaired word has sign coefficients and is rigid. -/
theorem repair_spec {d : ℕ} (hd : AnchorRepair.Admissible d) (s : List ℤ)
    (hs : SpectralSeed d (IdealCVP.ofList (d := d) s)) :
    (repair d s).length = d ∧ Signs (IdealCVP.ofList (d := d) (repair d s)) ∧
      Rigid (IdealCVP.ofList (d := d) (repair d s)) :=
  ⟨repair_length d s, repair_signs s hs.signs, repair_rigid hd s hs⟩

/-- Above the fixed cutoff, the only mathematical input is a spectral seed. -/
theorem repair_rigid_of_cutoff {d : ℕ} (hd : Dyadic d) (hlarge : 2 ^ 3600 ≤ d)
    (s : List ℤ) (hs : SpectralSeed d (IdealCVP.ofList (d := d) s)) :
    Rigid (IdealCVP.ofList (d := d) (repair d s)) :=
  repair_rigid (AnchorRepair.admissible_of_cutoff hd hlarge) s hs

end Power2ModuleSVP
