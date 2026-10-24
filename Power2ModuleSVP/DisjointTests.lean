import Power2ModuleSVP.AnchorScreen

/-!
Finite, exact tests for the anchor repair. All probabilities are rational;
the expectation evaluator visits only the flags occurring in the given row.
This file concerns the local tests, not a machine running-time certificate.
-/
namespace Power2ModuleSVP.AnchorTests

/-- A function depends only on the listed Boolean coordinates. -/
def DependsOn (vars : List ℕ) (f : (ℕ → Bool) → ℚ) : Prop :=
  ∀ a b, (∀ j ∈ vars, a j = b j) → f a = f b

/-- Exact expectation over a finite list of independent Bernoulli flags.
`fixed` records already exposed flags; `base` supplies irrelevant coordinates. -/
def localExpectation (p : ℚ) (vars : List ℕ) (f : (ℕ → Bool) → ℚ)
    (fixed : ℕ → Option Bool) (base : ℕ → Bool) : ℚ :=
  match vars with
  | [] => f base
  | j :: js =>
    match fixed j with
    | some b => localExpectation p js f fixed (Function.update base j b)
    | none =>
      (1-p) * localExpectation p js f fixed (Function.update base j false) +
      p * localExpectation p js f fixed (Function.update base j true)

theorem localExpectation_congr_fixed (p : ℚ) (vars : List ℕ)
    (f : (ℕ → Bool) → ℚ) (a b : ℕ → Option Bool)
    (h : ∀ j ∈ vars, a j = b j) (base : ℕ → Bool) :
    localExpectation p vars f a base = localExpectation p vars f b base := by
  induction vars generalizing base with
  | nil => rfl
  | cons j js ih =>
    have hj := h j (by simp)
    have ht : ∀ k ∈ js, a k = b k := fun k hk => h k (by simp [hk])
    simp only [localExpectation, hj]
    cases b j <;> simp only [ih ht]

theorem localExpectation_branch (p : ℚ) (vars : List ℕ)
    (f : (ℕ → Bool) → ℚ) (fixed : ℕ → Option Bool) (base : ℕ → Bool)
    (n : ℕ) (hn : fixed n = none) (hvars : vars.Nodup) :
    localExpectation p vars f fixed base =
      (1-p) * localExpectation p vars f (Function.update fixed n (some false)) base +
      p * localExpectation p vars f (Function.update fixed n (some true)) base := by
  induction vars generalizing base with
  | nil => simp [localExpectation]; ring
  | cons j js ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hvars
    by_cases hj : j = n
    · subst j
      have he (b : Bool) (x : ℕ → Bool) :
          localExpectation p js f (Function.update fixed n (some b)) x =
            localExpectation p js f fixed x := by
        apply localExpectation_congr_fixed
        intro k hk
        exact Function.update_of_ne (by intro h; subst k; exact hnot hk) _ _
      simp only [localExpectation, hn, Function.update_self]
      rw [he, he]
    · have hu (b : Bool) : Function.update fixed n (some b) j = fixed j :=
        Function.update_of_ne hj _ _
      simp only [localExpectation, hu]
      cases hfixed : fixed j with
      | some b => exact ih _ htail
      | none =>
        rw [ih _ htail, ih _ htail]
        ring

/-- A branch outside the local support has no effect. -/
theorem localExpectation_update_of_not_mem (p : ℚ) (vars : List ℕ)
    (f : (ℕ → Bool) → ℚ) (fixed : ℕ → Option Bool) (base : ℕ → Bool)
    {n : ℕ} (hn : n ∉ vars) (b : Bool) :
    localExpectation p vars f (Function.update fixed n (some b)) base =
      localExpectation p vars f fixed base := by
  apply localExpectation_congr_fixed
  intro j hj
  exact Function.update_of_ne (by intro h; subst j; exact hn hj) _ _

/-- Coordinate dependence is preserved when irrelevant base coordinates change. -/
theorem localExpectation_congr_base (p : ℚ) (vars support : List ℕ)
    (f : (ℕ → Bool) → ℚ) (hf : DependsOn support f)
    (fixed : ℕ → Option Bool) (a b : ℕ → Bool)
    (h : ∀ j ∈ support, j ∉ vars → a j = b j) :
    localExpectation p vars f fixed a = localExpectation p vars f fixed b := by
  induction vars generalizing a b with
  | nil => exact hf a b (fun j hj => h j hj (by simp))
  | cons j js ih =>
    have he (bit : Bool) :
        ∀ k ∈ support, k ∉ js →
          Function.update a j bit k = Function.update b j bit k := by
      intro k hk hkt
      by_cases hkj : k = j
      · subst k; simp
      · simp only [Function.update_of_ne hkj]
        exact h k hk (by simp [hkj, hkt])
    simp only [localExpectation]
    cases fixed j <;> simp only [ih _ _ (he _)]

/-- If every local flag is fixed to the base assignment, no averaging remains. -/
theorem localExpectation_all_fixed (p : ℚ) (vars : List ℕ)
    (f : (ℕ → Bool) → ℚ) (fixed : ℕ → Option Bool) (base : ℕ → Bool)
    (h : ∀ j ∈ vars, fixed j = some (base j)) :
    localExpectation p vars f fixed base = f base := by
  induction vars with
  | nil => rfl
  | cons j js ih =>
    rw [localExpectation, h j (by simp)]
    simp only [Function.update_eq_self]
    apply ih
    exact fun k hk => h k (by simp [hk])

theorem localExpectation_nonneg (p : ℚ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (vars : List ℕ) (f : (ℕ → Bool) → ℚ) (hf : ∀ b, 0 ≤ f b)
    (fixed : ℕ → Option Bool) (base : ℕ → Bool) :
    0 ≤ localExpectation p vars f fixed base := by
  induction vars generalizing base with
  | nil => exact hf _
  | cons j js ih =>
    simp only [localExpectation]
    cases fixed j with
    | some b => exact ih _
    | none =>
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hp') (ih _))
        (mul_nonneg hp (ih _))

theorem localExpectation_le_one (p : ℚ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (vars : List ℕ) (f : (ℕ → Bool) → ℚ) (hf : ∀ b, f b ≤ 1)
    (fixed : ℕ → Option Bool) (base : ℕ → Bool) :
    localExpectation p vars f fixed base ≤ 1 := by
  induction vars generalizing base with
  | nil => exact hf _
  | cons j js ih =>
    simp only [localExpectation]
    cases fixed j with
    | some b => exact ih _
    | none =>
      have h0 := mul_le_mul_of_nonneg_left (ih (Function.update base j false))
        (sub_nonneg.mpr hp')
      have h1 := mul_le_mul_of_nonneg_left (ih (Function.update base j true)) hp
      nlinarith

def completeAssignment : List ℕ → (ℕ → Bool) → (ℕ → Bool) → (ℕ → Bool)
  | [], _, base => base
  | j :: js, target, base =>
    completeAssignment js target (Function.update base j (target j))

theorem completeAssignment_apply (vars : List ℕ) (target base : ℕ → Bool) (j : ℕ) :
    completeAssignment vars target base j = if j ∈ vars then target j else base j := by
  induction vars generalizing base with
  | nil => simp [completeAssignment]
  | cons i vars ih =>
    rw [completeAssignment, ih]
    by_cases hmem : j ∈ vars
    · simp [hmem]
    · by_cases hji : j = i
      · subst j; simp [hmem]
      · simp [hmem, hji, Function.update_of_ne hji]

/-- Probability weight of one fully specified local assignment. -/
def assignmentWeight (p : ℚ) : List ℕ → (ℕ → Bool) → ℚ
  | [], _ => 1
  | j :: js, target =>
    (if target j then p else 1-p) * assignmentWeight p js target

theorem localExpectation_ge_leaf (p : ℚ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (vars : List ℕ) (f : (ℕ → Bool) → ℚ) (hf : ∀ a, 0 ≤ f a)
    (target base : ℕ → Bool) :
    assignmentWeight p vars target * f (completeAssignment vars target base) ≤
      localExpectation p vars f (fun _ => none) base := by
  induction vars generalizing base with
  | nil => simp [assignmentWeight, completeAssignment, localExpectation]
  | cons j vars ih =>
    cases hbit : target j with
    | false =>
      have hh := mul_le_mul_of_nonneg_left
        (ih (Function.update base j false)) (sub_nonneg.mpr hp')
      have ho := mul_nonneg hp
        (localExpectation_nonneg p hp hp' vars f hf (fun _ => none) (Function.update base j true))
      simpa only [assignmentWeight, completeAssignment, hbit, Bool.false_eq_true,
        ite_false, mul_assoc, localExpectation] using
        le_trans hh (le_add_of_nonneg_right ho)
    | true =>
      have hh := mul_le_mul_of_nonneg_left
        (ih (Function.update base j true)) hp
      have ho := mul_nonneg (sub_nonneg.mpr hp')
        (localExpectation_nonneg p hp hp' vars f hf (fun _ => none) (Function.update base j false))
      simpa only [assignmentWeight, completeAssignment, hbit, ite_true,
        mul_assoc, localExpectation] using
        le_trans hh (le_add_of_nonneg_left ho)

theorem localExpectation_one_sub (p : ℚ) (vars : List ℕ)
    (f : (ℕ → Bool) → ℚ) (fixed : ℕ → Option Bool) (base : ℕ → Bool) :
    localExpectation p vars (fun b => 1-f b) fixed base =
      1-localExpectation p vars f fixed base := by
  induction vars generalizing base with
  | nil => rfl
  | cons j vars ih =>
    simp only [localExpectation]
    cases fixed j with
    | some b => exact ih _
    | none => rw [ih, ih]; ring

/-- A known illegal assignment gives an exact upper bound on survival. -/
theorem localExpectation_le_one_sub_leaf (p : ℚ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (vars : List ℕ) (f : (ℕ → Bool) → ℚ) (hf : DependsOn vars f)
    (hf' : ∀ b, f b ≤ 1) (target base : ℕ → Bool) (ht : f target = 0) :
    localExpectation p vars f (fun _ => none) base ≤ 1-assignmentWeight p vars target := by
  have he : f (completeAssignment vars target base) = 0 := by
    rw [hf _ target (fun j hj => by simp [completeAssignment_apply, hj]), ht]
  have hh := localExpectation_ge_leaf p hp hp' vars (fun b => 1-f b)
    (fun b => sub_nonneg.mpr (hf' b)) target base
  rw [he, sub_zero, mul_one, localExpectation_one_sub] at hh
  linarith

theorem assignmentWeight_all_false (p : ℚ) (vars : List ℕ) :
    assignmentWeight p vars (fun _ => false) = (1-p)^vars.length := by
  induction vars with
  | nil => simp [assignmentWeight]
  | cons j vars ih => simp [assignmentWeight, ih, pow_succ, mul_comm]

theorem assignmentWeight_update_of_not_mem (p : ℚ) (vars : List ℕ)
    {n : ℕ} (hn : n ∉ vars) :
    assignmentWeight p vars (Function.update (fun _ => false) n true) =
      (1-p)^vars.length := by
  induction vars with
  | nil => simp [assignmentWeight]
  | cons j vars ih =>
    have hnj : j ≠ n := by intro h; subst j; exact hn (by simp)
    have hnt : n ∉ vars := fun h => hn (by simp [h])
    simp [assignmentWeight, Function.update_of_ne hnj, ih hnt, pow_succ, mul_comm]

theorem assignmentWeight_singleton (p : ℚ) (vars : List ℕ) (hnodup : vars.Nodup)
    {n : ℕ} (hn : n ∈ vars) :
    assignmentWeight p vars (Function.update (fun _ => false) n true) =
      p * (1-p)^(vars.length-1) := by
  induction vars with
  | nil => simp at hn
  | cons j vars ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hnodup
    by_cases hjn : j = n
    · subst j
      simp [assignmentWeight, assignmentWeight_update_of_not_mem p vars hnot]
    · have hnt : n ∈ vars := (List.mem_cons.mp hn).resolve_left (Ne.symm hjn)
      have hlen : 0 < vars.length := List.length_pos_of_mem hnt
      rw [assignmentWeight, Function.update_of_ne hjn]
      simp only [Bool.false_eq_true, ite_false]
      rw [ih htail hnt]
      have he : vars.length = vars.length-1+1 := by omega
      simp only [List.length_cons, Nat.add_sub_cancel]
      have hpw : (1-p)^vars.length = (1-p)^(vars.length-1)*(1-p) := by
        conv_lhs => rw [he, pow_succ]
      rw [hpw]
      ring

/-- The actual flags influencing a negacyclic convolution row. -/
def rowFlags (d : ℕ) (support : Finset ℕ) (i : ℕ) : Finset ℕ :=
  support.image (fun j => (i+d-j) % d)

def rowVariables (d : ℕ) (support : Finset ℕ) (i : ℕ) : List ℕ :=
  (rowFlags d support i).sort (· ≤ ·)

@[simp] theorem mem_rowVariables (d : ℕ) (support : Finset ℕ) (i j : ℕ) :
    j ∈ rowVariables d support i ↔ j ∈ rowFlags d support i := by
  simp [rowVariables]

theorem rowVariables_nodup (d : ℕ) (support : Finset ℕ) (i : ℕ) :
    (rowVariables d support i).Nodup := by
  exact Finset.sort_nodup _ _

theorem rowFlags_card {d : ℕ} (support : Finset ℕ)
    (hs : ∀ j ∈ support, j < d) {i : ℕ} (hi : i < d) :
    (rowFlags d support i).card = support.card := by
  apply Finset.card_image_iff.mpr
  intro j hj k hk he
  have hval (r : ℕ) (hr : r < d) :
      (i+d-r)%d = if r ≤ i then i-r else i+d-r := by
    split_ifs with h
    · rw [show i+d-r = (i-r)+d by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]
  have hjlt := hs j hj
  have hklt := hs k hk
  dsimp only at he
  rw [hval j hjlt, hval k hklt] at he
  split_ifs at he <;> omega

theorem rowVariables_length {d : ℕ} (support : Finset ℕ)
    (hs : ∀ j ∈ support, j < d) {i : ℕ} (hi : i < d) :
    (rowVariables d support i).length = support.card := by
  rw [rowVariables, Finset.length_sort, rowFlags_card support hs hi]

/-- For at least two nonzero integer terms, either the unflipped sum is
illegal or some single flip makes it illegal. -/
theorem exists_illegal_flip {ι : Type*} (S : Finset ι) (t : ι → ℤ)
    (hm : 2 ≤ S.card) (ht : ∀ j ∈ S, t j ≠ 0) :
    ((∑ j ∈ S, t j) ≠ -1 ∧ (∑ j ∈ S, t j) ≠ 1) ∨
      ∃ j ∈ S,
        (∑ k ∈ S, t k) - 2 * t j ≠ -1 ∧
        (∑ k ∈ S, t k) - 2 * t j ≠ 1 := by
  classical
  let a := ∑ j ∈ S, t j
  by_cases ha : a = -1 ∨ a = 1
  · right
    by_contra hn
    have he : ∀ j ∈ S, t j = a := by
      intro j hj
      have htj := ht j hj
      have hjlegal : a - 2 * t j = -1 ∨ a - 2 * t j = 1 := by
        by_contra hjbad
        exact hn ⟨j, hj, (not_or.mp hjbad).1, (not_or.mp hjbad).2⟩
      rcases ha with ha | ha <;> rcases hjlegal with hjlegal | hjlegal <;> omega
    have hsum : a = (S.card : ℤ) * a := by
      change (∑ j ∈ S, t j) = _
      simp_rw [Finset.sum_congr rfl he]
      simp
    have hcard : (2 : ℤ) ≤ S.card := by exact_mod_cast hm
    rcases ha with ha | ha <;> nlinarith
  · exact Or.inl (not_or.mp ha)

/-- Reverse-order greedy selection, with exact finite-set intersection tests. -/
def greedySelect (flags : ℕ → Finset ℕ) : List ℕ → List ℕ
  | [] => []
  | i :: is =>
    let rest := greedySelect flags is
    if rest.all (fun j => decide (Disjoint (flags i) (flags j))) then i :: rest else rest

theorem greedySelect_pairwise (flags : ℕ → Finset ℕ) (rows : List ℕ) :
    (greedySelect flags rows).Pairwise (fun i j => Disjoint (flags i) (flags j)) := by
  induction rows with
  | nil => simp [greedySelect]
  | cons i rows ih =>
    simp only [greedySelect]
    split_ifs with h
    · apply List.pairwise_cons.mpr
      exact ⟨by simpa only [List.all_eq_true, decide_eq_true_eq] using h, ih⟩
    · exact ih

theorem greedySelect_subset (flags : ℕ → Finset ℕ) (rows : List ℕ) :
    ∀ i ∈ greedySelect flags rows, i ∈ rows := by
  induction rows with
  | nil => simp [greedySelect]
  | cons j rows ih =>
    simp only [greedySelect]
    split_ifs
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · simp
      · exact List.mem_cons_of_mem _ (ih i hi)
    · intro i hi
      exact List.mem_cons_of_mem _ (ih i hi)

/-- Every input row intersects a retained row, provided its flag set is nonempty. -/
theorem greedySelect_cover (flags : ℕ → Finset ℕ) (rows : List ℕ)
    (hne : ∀ i ∈ rows, (flags i).Nonempty) :
    ∀ i ∈ rows, ∃ j ∈ greedySelect flags rows, ¬ Disjoint (flags i) (flags j) := by
  induction rows with
  | nil => simp
  | cons i rows ih =>
    have ht : ∀ j ∈ rows, (flags j).Nonempty :=
      fun j hj => hne j (List.mem_cons_of_mem _ hj)
    intro k hk
    simp only [greedySelect]
    split_ifs with h
    · rcases List.mem_cons.mp hk with hki | hk
      · subst k
        obtain ⟨x, hx⟩ := hne i (by simp)
        refine ⟨i, by simp, ?_⟩
        exact fun hd => Finset.disjoint_left.mp hd hx hx
      · obtain ⟨j, hj, hij⟩ := ih ht k hk
        exact ⟨j, List.mem_cons_of_mem _ hj, hij⟩
    · rcases List.mem_cons.mp hk with rfl | hk
      · by_contra hn
        apply h
        simp only [List.all_eq_true, decide_eq_true_eq]
        intro j hj
        by_contra hd
        exact hn ⟨j, hj, hd⟩
      · exact ih ht k hk

/-- A size-`m` support gives at most `m²` possible conflicts with a fixed row. -/
def conflictingRows (d : ℕ) (support : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (support ×ˢ support).image (fun jk => (r+d-jk.2+jk.1)%d)

theorem conflictingRows_card (d : ℕ) (support : Finset ℕ) (r : ℕ) :
    (conflictingRows d support r).card ≤ support.card ^ 2 := by
  calc
    _ ≤ (support ×ˢ support).card := Finset.card_image_le
    _ = _ := by simp [pow_two]

theorem mem_conflictingRows {d : ℕ} (support : Finset ℕ)
    (hs : ∀ j ∈ support, j < d) {i r : ℕ} (hi : i < d)
    (hconf : ¬ Disjoint (rowFlags d support i) (rowFlags d support r)) :
    i ∈ conflictingRows d support r := by
  obtain ⟨x, hxi, hxr⟩ := Finset.not_disjoint_iff.mp hconf
  obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hxi
  obtain ⟨k, hk, hke⟩ := Finset.mem_image.mp hxr
  have he : (i+d-j)%d = (r+d-k)%d := hje.trans hke.symm
  have hcancel : ((i+d-j)%d+j)%d = i := by
    rw [Nat.mod_add_mod, Nat.sub_add_cancel (by have := hs j hj; omega),
      Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  apply Finset.mem_image.mpr
  refine ⟨(j,k), by simp [hj,hk], ?_⟩
  rw [← hcancel, he, Nat.mod_add_mod]

def multiplierSupport (d : ℕ) (v : List ℤ) : Finset ℕ :=
  (Finset.range d).filter (fun j => v.getD j 0 ≠ 0)

def selectedRows (d : ℕ) (v : List ℤ) : List ℕ :=
  greedySelect (rowFlags d (multiplierSupport d v)) (List.range d)

theorem selectedRows_pairwise (d : ℕ) (v : List ℤ) :
    (selectedRows d v).Pairwise (fun i j =>
      Disjoint (rowFlags d (multiplierSupport d v) i)
        (rowFlags d (multiplierSupport d v) j)) :=
  greedySelect_pairwise _ _

theorem selectedRows_lt (d : ℕ) (v : List ℤ) {i : ℕ}
    (hi : i ∈ selectedRows d v) : i < d := by
  exact List.mem_range.mp (greedySelect_subset _ _ i hi)

/-- The greedy construction retains at least `d / m²` rows, expressed without
division so the bound remains exact for natural cardinalities. -/
theorem selectedRows_packing (d : ℕ) (v : List ℤ)
    (hs : (multiplierSupport d v).Nonempty) :
    d ≤ (selectedRows d v).length * (multiplierSupport d v).card ^ 2 := by
  let S := multiplierSupport d v
  have hsb : ∀ j ∈ S, j < d := by
    intro j hj
    exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hne : ∀ i ∈ List.range d, (rowFlags d S i).Nonempty := by
    intro i _
    exact hs.image _
  have hcover : Finset.range d ⊆
      (selectedRows d v).toFinset.biUnion (conflictingRows d S) := by
    intro i hi
    obtain ⟨r, hr, hconf⟩ := greedySelect_cover (rowFlags d S) (List.range d)
      hne i (List.mem_range.mpr (Finset.mem_range.mp hi))
    apply Finset.mem_biUnion.mpr
    exact ⟨r, List.mem_toFinset.mpr hr,
      mem_conflictingRows S hsb (Finset.mem_range.mp hi) hconf⟩
  calc
    d = (Finset.range d).card := by simp
    _ ≤ ((selectedRows d v).toFinset.biUnion (conflictingRows d S)).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ r ∈ (selectedRows d v).toFinset, (conflictingRows d S r).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ (selectedRows d v).toFinset, S.card ^ 2 := by
      apply Finset.sum_le_sum
      intro r _
      exact conflictingRows_card d S r
    _ = (selectedRows d v).toFinset.card * S.card ^ 2 := by simp
    _ ≤ (selectedRows d v).length * S.card ^ 2 :=
      Nat.mul_le_mul_right _ (List.toFinset_card_le _)

/-- The coefficient of the flipped-seed product in one convolution row. -/
def rowValue (d : ℕ) (s v : List ℤ) (i : ℕ) (flags : ℕ → Bool) : ℤ :=
  ∑ j ∈ multiplierSupport d v,
    (if j ≤ i then (1 : ℤ) else -1) * s.getD ((i+d-j)%d) 0 * v.getD j 0 *
      (if flags ((i+d-j)%d) then -1 else 1)

def rowIndicator (d : ℕ) (s v : List ℤ) (i : ℕ) (flags : ℕ → Bool) : ℚ :=
  if rowValue d s v i flags = -1 ∨ rowValue d s v i flags = 1 then 1 else 0

/-- The local integer row computation is the genuine negacyclic product. -/
theorem rowValue_eq_mul {d : ℕ} (hd : 0 < d) (s v : List ℤ)
    (i : Fin d) (flags : ℕ → Bool) :
    rowValue d s v i.val flags =
      IdealCVP.Cyclotomic.mul
        (fun k : Fin d => s.getD k.val 0 * (if flags k.val then -1 else 1))
        (IdealCVP.ofList v) i := by
  rw [mul_row_formula hd]
  simp only [Fin.val_mk, IdealCVP.ofList]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    (if j ≤ i.val then (1 : ℤ) else -1) *
      (s.getD ((i.val+d-j)%d) 0 * (if flags ((i.val+d-j)%d) then -1 else 1)) *
      v.getD j 0) d]
  unfold rowValue multiplierSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hv : v.getD j 0 = 0
  · simp only [hv, ne_eq, not_true_eq_false, ite_false, mul_zero]
  · simp only [hv, ne_eq, not_false_eq_true, ite_true, IdealCVP.ofList]
    ring

theorem rowIndicator_depends (d : ℕ) (s v : List ℤ) (i : ℕ) :
    DependsOn (rowVariables d (multiplierSupport d v) i) (rowIndicator d s v i) := by
  intro a b hab
  have he : rowValue d s v i a = rowValue d s v i b := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hab ((i+d-j)%d) (by
      simp only [mem_rowVariables, rowFlags, Finset.mem_image]
      exact ⟨j, hj, rfl⟩)]
  simp only [rowIndicator, he]

/-- Flipping one contributing flag subtracts twice that row term. -/
theorem rowValue_singleton {d : ℕ} (s v : List ℤ) {i : ℕ} (hi : i < d)
    {j : ℕ} (hj : j ∈ multiplierSupport d v) :
    rowValue d s v i (Function.update (fun _ => false) ((i+d-j)%d) true) =
      rowValue d s v i (fun _ => false) -
        2 * ((if j ≤ i then (1 : ℤ) else -1) *
          s.getD ((i+d-j)%d) 0 * v.getD j 0) := by
  classical
  let S := multiplierSupport d v
  let t := fun k => (if k ≤ i then (1 : ℤ) else -1) *
    s.getD ((i+d-k)%d) 0 * v.getD k 0
  have hsb : ∀ k ∈ S, k < d := fun k hk =>
    Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  have hinj : Set.InjOn (fun k => (i+d-k)%d) (S : Set ℕ) :=
    Finset.card_image_iff.mp (rowFlags_card S hsb hi)
  change (∑ k ∈ S, t k *
      (if Function.update (fun _ => false) ((i+d-j)%d) true ((i+d-k)%d) then -1 else 1)) =
    (∑ k ∈ S, t k * (if false then -1 else 1)) - 2 * t j
  simp only [Bool.false_eq_true, ite_false, mul_one]
  have hterm : ∀ k ∈ S,
      t k * (if Function.update (fun _ => false) ((i+d-j)%d) true ((i+d-k)%d)
        then -1 else 1) = if k = j then -t k else t k := by
    intro k hk
    by_cases hkj : k = j
    · subst k; simp
    · have hflag : (i+d-k)%d ≠ (i+d-j)%d := fun he => hkj (hinj hk hj he)
      simp only [Function.update_of_ne hflag, Bool.false_eq_true, ite_false, mul_one,
        hkj]
  rw [Finset.sum_congr rfl hterm]
  have hsum := Finset.sum_erase_add S t hj
  have hsum' := Finset.sum_erase_add S (fun k => if k = j then -t k else t k) hj
  have hrest : (∑ k ∈ S.erase j, if k = j then -t k else t k) =
      ∑ k ∈ S.erase j, t k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact if_neg (Finset.mem_erase.mp hk).1
  rw [hrest] at hsum'
  simp only [ite_true] at hsum'
  linarith

theorem half_le_one_sub_pow (p : ℚ) (hp : p ≤ 1) (m : ℕ)
    (hmp : (m : ℚ) * p ≤ 1/2) : (1/2 : ℚ) ≤ (1-p)^m := by
  have hh := one_add_mul_le_pow (a := -p) (by linarith : (-2 : ℚ) ≤ -p) m
  have he : (1 + -p)^m = (1-p)^m := by congr 1; ring
  rw [he] at hh
  nlinarith

/-- Conditional local survival probability, with at most one binary choice
per member of the multiplier support. -/
def rowProbability (d : ℕ) (s v : List ℤ) (i : ℕ)
    (pre : List Bool) (p : ℚ) : ℚ :=
  localExpectation p (rowVariables d (multiplierSupport d v) i)
    (rowIndicator d s v i) (fun j => pre[j]?) (fun _ => false)

/-- Product of the selected, disjoint row survival probabilities. -/
def eventProbability (d : ℕ) (s v : List ℤ) (pre : List Bool) (p : ℚ) : ℚ :=
  ((selectedRows d v).map (fun i => rowProbability d s v i pre p)).prod

/-- Every row of a multiplier with at least two terms fails with probability
at least `p/2`. The assumption `m*p ≤ 1/2` is the local form of the paper's
choice `p ≤ 1/(2C)` and support bound `m ≤ C`. -/
theorem rowProbability_le_one_sub_half {d : ℕ} (hd : 0 < d)
    (s v : List ℤ) (i : ℕ) (hi : i < d)
    (hs : Signs (IdealCVP.ofList (d := d) s))
    (hm : 2 ≤ (multiplierSupport d v).card)
    (p : ℚ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hmp : ((multiplierSupport d v).card : ℚ) * p ≤ 1/2) :
    rowProbability d s v i [] p ≤ 1-p/2 := by
  let S := multiplierSupport d v
  let vars := rowVariables d S i
  let t := fun j => (if j ≤ i then (1 : ℤ) else -1) *
    s.getD ((i+d-j)%d) 0 * v.getD j 0
  have hsb : ∀ j ∈ S, j < d := fun j hj =>
    Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hlen : vars.length = S.card := rowVariables_length S hsb hi
  have ht : ∀ j ∈ S, t j ≠ 0 := by
    intro j hj
    have hvj : v.getD j 0 ≠ 0 := (Finset.mem_filter.mp hj).2
    have hsign := hs ⟨(i+d-j)%d, Nat.mod_lt _ hd⟩
    change s.getD ((i+d-j)%d) 0 = -1 ∨ s.getD ((i+d-j)%d) 0 = 1 at hsign
    have hsj : s.getD ((i+d-j)%d) 0 ≠ 0 := by rcases hsign with h | h <;> omega
    exact mul_ne_zero (mul_ne_zero (by split_ifs <;> norm_num) hsj) hvj
  have hzero : rowValue d s v i (fun _ => false) = ∑ j ∈ S, t j := by
    simp only [rowValue, Bool.false_eq_true, ite_false, mul_one]
    rfl
  have hf : DependsOn vars (rowIndicator d s v i) := rowIndicator_depends d s v i
  have hf' : ∀ b, rowIndicator d s v i b ≤ 1 := by
    intro b
    unfold rowIndicator
    split_ifs <;> norm_num
  rcases exists_illegal_flip S t hm ht with hbad | ⟨j, hj, hbad⟩
  · have hrow : rowIndicator d s v i (fun _ => false) = 0 := by
      unfold rowIndicator
      rw [hzero, if_neg (not_or.mpr hbad)]
    have he : rowProbability d s v i [] p ≤
        1-assignmentWeight p vars (fun _ => false) :=
      localExpectation_le_one_sub_leaf p hp hp' vars (rowIndicator d s v i)
        hf hf' _ _ hrow
    rw [assignmentWeight_all_false, hlen] at he
    have hh := half_le_one_sub_pow p hp' S.card hmp
    linarith
  · let n := (i+d-j)%d
    let target := Function.update (fun _ => false) n true
    have hrow : rowIndicator d s v i target = 0 := by
      unfold rowIndicator
      rw [rowValue_singleton s v hi hj, hzero]
      exact if_neg (not_or.mpr hbad)
    have hn : n ∈ vars := by
      apply (mem_rowVariables _ _ _ _).mpr
      exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
    have he : rowProbability d s v i [] p ≤ 1-assignmentWeight p vars target :=
      localExpectation_le_one_sub_leaf p hp hp' vars (rowIndicator d s v i)
        hf hf' target _ hrow
    rw [assignmentWeight_singleton p vars (rowVariables_nodup _ _ _) hn, hlen] at he
    have hcast : ((S.card-1 : ℕ) : ℚ) ≤ (S.card : ℚ) := by
      exact_mod_cast Nat.sub_le S.card 1
    have hmp' : ((S.card-1 : ℕ) : ℚ) * p ≤ 1/2 :=
      le_trans (mul_le_mul_of_nonneg_right hcast hp) hmp
    have hh := mul_le_mul_of_nonneg_left
      (half_le_one_sub_pow p hp' (S.card-1) hmp') hp
    linarith

theorem prefixFixed_append (pre : List Bool) (bit : Bool) :
    (fun j => (pre ++ [bit])[j]?) =
      Function.update (fun j => pre[j]?) pre.length (some bit) := by
  funext j
  by_cases hj : j = pre.length
  · subst j
    simp
  · by_cases hlt : j < pre.length
    · simp [List.getElem?_append, hlt, Function.update_of_ne hj]
    · have hgt : pre.length < j := by omega
      simp [List.getElem?_append, hlt, Function.update_of_ne hj,
        List.getElem?_eq_none_iff.mpr (by omega : pre.length ≤ j),
        List.getElem?_eq_none_iff.mpr (by simp; omega : [bit].length ≤ j-pre.length)]

theorem rowProbability_branch (d : ℕ) (s v : List ℤ) (i : ℕ)
    (pre : List Bool) (p : ℚ) :
    rowProbability d s v i pre p =
      (1-p) * rowProbability d s v i (pre ++ [false]) p +
      p * rowProbability d s v i (pre ++ [true]) p := by
  unfold rowProbability
  rw [prefixFixed_append, prefixFixed_append]
  exact localExpectation_branch _ _ _ _ _ pre.length (by simp)
    (rowVariables_nodup _ _ _)

theorem rowProbability_append_of_not_mem (d : ℕ) (s v : List ℤ) (i : ℕ)
    (pre : List Bool) (p : ℚ) (bit : Bool)
    (hn : pre.length ∉ rowFlags d (multiplierSupport d v) i) :
    rowProbability d s v i (pre ++ [bit]) p =
      rowProbability d s v i pre p := by
  unfold rowProbability
  rw [prefixFixed_append]
  apply localExpectation_update_of_not_mem
  simpa only [mem_rowVariables] using hn

theorem rowProbability_terminal (d : ℕ) (s v : List ℤ) (i : ℕ)
    (pre : List Bool) (p : ℚ) (hd : 0 < d) (hp : d ≤ pre.length) :
    rowProbability d s v i pre p =
      rowIndicator d s v i (fun j => pre.getD j false) := by
  unfold rowProbability
  rw [localExpectation_congr_base p _ _ _ (rowIndicator_depends d s v i)
    _ (fun _ => false) (fun j => pre.getD j false)
    (fun j hj hn => False.elim (hn hj))]
  apply localExpectation_all_fixed
  intro j hj
  have hjd : j < d := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ((mem_rowVariables _ _ _ _).mp hj)
    exact Nat.mod_lt _ hd
  have hjp : j < pre.length := by omega
  simp [List.getD, List.getElem?_eq_getElem hjp]

theorem rowProbability_nonneg (d : ℕ) (s v : List ℤ) (i : ℕ)
    (pre : List Bool) (p : ℚ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    0 ≤ rowProbability d s v i pre p := by
  apply localExpectation_nonneg p hp hp'
  intro b
  unfold rowIndicator
  split_ifs <;> norm_num

theorem rowProbability_le_one (d : ℕ) (s v : List ℤ) (i : ℕ)
    (pre : List Bool) (p : ℚ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    rowProbability d s v i pre p ≤ 1 := by
  apply localExpectation_le_one p hp hp'
  intro b
  unfold rowIndicator
  split_ifs <;> norm_num

theorem product_rowProbability_append (d : ℕ) (s v : List ℤ) (rows : List ℕ)
    (pre : List Bool) (p : ℚ) (bit : Bool)
    (h : ∀ i ∈ rows, pre.length ∉ rowFlags d (multiplierSupport d v) i) :
    (rows.map (fun i => rowProbability d s v i (pre ++ [bit]) p)).prod =
      (rows.map (fun i => rowProbability d s v i pre p)).prod := by
  congr 1
  apply List.map_congr_left
  intro i hi
  exact rowProbability_append_of_not_mem _ _ _ _ _ _ _ (h i hi)

theorem product_rowProbability_branch (d : ℕ) (s v : List ℤ) (rows : List ℕ)
    (pre : List Bool) (p : ℚ)
    (hrows : rows.Pairwise (fun i j =>
      Disjoint (rowFlags d (multiplierSupport d v) i)
        (rowFlags d (multiplierSupport d v) j))) :
    (rows.map (fun i => rowProbability d s v i pre p)).prod =
      (1-p) * (rows.map (fun i => rowProbability d s v i (pre ++ [false]) p)).prod +
      p * (rows.map (fun i => rowProbability d s v i (pre ++ [true]) p)).prod := by
  induction rows with
  | nil => simp
  | cons i rows ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hrows
    by_cases hn : pre.length ∈ rowFlags d (multiplierSupport d v) i
    · have ht : ∀ j ∈ rows,
          pre.length ∉ rowFlags d (multiplierSupport d v) j := by
        intro j hj hmem
        exact Finset.disjoint_left.mp (hhead j hj) hn hmem
      simp only [List.map_cons, List.prod_cons]
      rw [product_rowProbability_append _ _ _ _ _ _ false ht,
        product_rowProbability_append _ _ _ _ _ _ true ht,
        rowProbability_branch d s v i pre p]
      ring
    · simp only [List.map_cons, List.prod_cons]
      rw [rowProbability_append_of_not_mem _ _ _ _ _ _ false hn,
        rowProbability_append_of_not_mem _ _ _ _ _ _ true hn,
        ih htail]
      ring

/-- Exact conditional expectations satisfy the two-branch averaging identity.
Disjointness ensures that the newly exposed flag affects at most one row. -/
theorem eventProbability_branch (d : ℕ) (s v : List ℤ) (pre : List Bool) (p : ℚ) :
    eventProbability d s v pre p =
      (1-p) * eventProbability d s v (pre ++ [false]) p +
      p * eventProbability d s v (pre ++ [true]) p :=
  product_rowProbability_branch _ _ _ _ _ _ (selectedRows_pairwise d v)

theorem eventProbability_nonneg (d : ℕ) (s v : List ℤ) (pre : List Bool)
    (p : ℚ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    0 ≤ eventProbability d s v pre p := by
  apply List.prod_nonneg
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact rowProbability_nonneg _ _ _ _ _ _ hp hp'

/-- The joint survival probability is bounded by the number of disjoint tests. -/
theorem eventProbability_le_pow {d : ℕ} (hd : 0 < d) (s v : List ℤ)
    (hs : Signs (IdealCVP.ofList (d := d) s))
    (hm : 2 ≤ (multiplierSupport d v).card)
    (p : ℚ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hmp : ((multiplierSupport d v).card : ℚ) * p ≤ 1/2) :
    eventProbability d s v [] p ≤ (1-p/2)^(selectedRows d v).length := by
  have hbase : (0 : ℚ) ≤ 1-p/2 := by linarith
  have hbound (rows : List ℕ) (hr : ∀ i ∈ rows, i < d) :
      (rows.map (fun i => rowProbability d s v i [] p)).prod ≤
        (1-p/2)^rows.length := by
    induction rows with
    | nil => simp
    | cons i rows ih =>
      have htail : ∀ j ∈ rows, j < d := fun j hj => hr j (by simp [hj])
      have hrow := rowProbability_le_one_sub_half hd s v i (hr i (by simp))
        hs hm p hp hp' hmp
      have htail0 : (0 : ℚ) ≤
          (rows.map (fun i => rowProbability d s v i [] p)).prod := by
        apply List.prod_nonneg
        intro x hx
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
        exact rowProbability_nonneg _ _ _ _ _ _ hp hp'
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      calc
        _ ≤ (1-p/2)*(1-p/2)^rows.length :=
          mul_le_mul hrow (ih htail) htail0 hbase
        _ = _ := by rw [pow_succ]; ring
  exact hbound _ (fun i hi => selectedRows_lt d v hi)

def eventIndicator (d : ℕ) (s v : List ℤ) (flags : ℕ → Bool) : ℚ :=
  if (selectedRows d v).all (fun i =>
    decide (rowValue d s v i flags = -1 ∨ rowValue d s v i flags = 1)) then 1 else 0

/-- Once all degree-many flags are exposed, the exact probability is the
zero-or-one indicator of the selected convolution rows being signs. -/
theorem eventProbability_terminal (d : ℕ) (s v : List ℤ) (pre : List Bool)
    (p : ℚ) (hd : 0 < d) (hp : d ≤ pre.length) :
    eventProbability d s v pre p =
      eventIndicator d s v (fun j => pre.getD j false) := by
  unfold eventProbability eventIndicator
  have hmap :
      (selectedRows d v).map (fun i => rowProbability d s v i pre p) =
        (selectedRows d v).map (fun i =>
          rowIndicator d s v i (fun j => pre.getD j false)) := by
    apply List.map_congr_left
    intro i _
    exact rowProbability_terminal _ _ _ _ _ _ hd hp
  rw [hmap]
  simp only [rowIndicator]
  generalize selectedRows d v = rows
  induction rows with
  | nil => simp
  | cons i rows ih =>
    by_cases hrow : rowValue d s v i (fun j => pre.getD j false) = -1 ∨
        rowValue d s v i (fun j => pre.getD j false) = 1
    · simpa only [List.map_cons, List.prod_cons, List.all_cons, hrow,
        ite_true, decide_true, Bool.true_and, one_mul] using ih
    · simp only [List.map_cons, List.prod_cons, List.all_cons, hrow,
        ite_false, decide_false, Bool.false_and, Bool.false_eq_true, zero_mul]

end Power2ModuleSVP.AnchorTests
