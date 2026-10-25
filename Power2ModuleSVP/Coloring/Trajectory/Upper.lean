module

public import Power2ModuleSVP.Coloring.Trajectory.Potential

/-!
# Upper

Heavy-row protection and uniform terminal upper weights.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP.PartialColoringAlg

open scoped BigOperators

theorem outside_heavy_weight {r m : ℕ} (w : Fin m → ℚ) (hw : ∀ i, 0 ≤ w i)
    (i : Fin m) (hi : i ∉ heavyRows (r := r) w) :
    (((r + 7) / 8 : ℕ) : ℚ) * w i ≤ ∑ j, w j := by
  let l := (List.finRange m).mergeSort (fun i j => decide (w j ≤ w i))
  let k := (r + 7) / 8
  have hperm : l.Perm (List.finRange m) := List.mergeSort_perm _ _
  have hlen : l.length = m := by simpa using hperm.length_eq
  have himem : i ∈ l := hperm.mem_iff.mpr (by simp)
  have hitake : i ∉ l.take k := hi
  have hk : k ≤ l.length := by
    by_contra hn
    have he : l.take k = l := List.take_of_length_le (by omega)
    exact hitake (he.symm ▸ himem)
  have hidrop : i ∈ l.drop k := by
    have h := himem
    rw [← List.take_append_drop k l, List.mem_append] at h
    exact h.resolve_left hitake
  have hsorted : l.Pairwise (fun j t => w t ≤ w j) := by
    have hs := List.pairwise_mergeSort
      (le := fun i j : Fin m => decide (w j ≤ w i))
      (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; exact hbc.trans hab)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
      (List.finRange m)
    simpa only [decide_eq_true_eq] using hs
  have hcross : ∀ j ∈ l.take k, w i ≤ w j := by
    rw [← List.take_append_drop k l] at hsorted
    exact fun j hj => (List.pairwise_append.mp hsorted).2.2 j hj i hidrop
  have hn : (l.take k).Nodup := (hperm.nodup_iff.mpr (List.nodup_finRange m)).take
  have hcard : (l.take k).toFinset.card = k := by
    rw [List.toFinset_card_of_nodup hn, List.length_take, min_eq_left hk]
  calc
    _ = ∑ _j ∈ (l.take k).toFinset, w i := by simp [hcard, k]
    _ ≤ ∑ j ∈ (l.take k).toFinset, w j := by
      apply Finset.sum_le_sum
      intro j hj
      exact hcross j (List.mem_toFinset.mp hj)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => hw j)

theorem outside_heavy_lt_half {r m : ℕ} (hr : 0 < r) (s : State r m)
    (hw : ∀ i, 0 ≤ s.w i) (hpot : potential s < (r : ℚ) / 16)
    (i : Fin m) (hi : i ∉ heavyRows (r := r) s.w) : s.w i < 1 / 2 := by
  have h := outside_heavy_weight s.w hw i hi
  have hk : r ≤ 8 * ((r + 7) / 8) := by omega
  have hk' : (r : ℚ) ≤ 8 * (((r + 7) / 8 : ℕ) : ℚ) := by exact_mod_cast hk
  have hmul := mul_le_mul_of_nonneg_right hk' (hw i)
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  unfold potential at hpot
  nlinarith

theorem heavy_row_increment {r m : ℕ} (a : Fin m → Row r) (s : State r m)
    (i : Fin m) (hi : i ∈ heavyRows (r := r) s.w) : rowIncrement a s i = 0 := by
  have hm : (a i).a ∈ constraints a s := by
    simp only [constraints, List.mem_cons, List.mem_append, List.mem_map]
    exact Or.inr (Or.inl (Or.inr ⟨i, hi, rfl⟩))
  have h := direction_orthogonal a s _ hm
  simp [rowIncrement, dot_smul_right, h]

theorem heavy_next_weight {r m : ℕ} (hr : 0 < r) (a : Fin m → Row r)
    (hl : ∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ)) (s : State r m)
    (hw : ∀ i, 0 ≤ s.w i) (i : Fin m) (hi : i ∈ heavyRows (r := r) s.w) :
    (nextState a s).w i ≤ s.w i + mesh r m := by
  rw [nextState_weight, heavy_row_increment a s i hi]
  norm_num only [zero_pow (by decide : 2 ≠ 0), add_zero, mul_one]
  have hround := (roundUp_bounds (mesh_pos r m) (s.w i * damping a i)).2
  have h := mul_le_mul_of_nonneg_left (damping_bounds hr a hl i).2 (hw i)
  nlinarith

theorem outside_heavy_next_weight {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (s : State r m) (hx : RationalCube s.x)
    (hw : ∀ i, 0 ≤ s.w i) (hhalf : ¬r ≤ 2 * signCoordinateCount s.x)
    (hpot : potential s < (r : ℚ) / 16)
    (i : Fin m) (hi : i ∉ heavyRows (r := r) s.w) :
    (nextState a s).w i ≤ 3 / 2 + mesh r m := by
  have hr : 0 < r := by have := hp.dimension; omega
  have hsmall := outside_heavy_lt_half hr s hw hpot i hi
  have ht := rowIncrement_abs_le a x hp s hx hhalf i
  have ht' := abs_le.mp ht
  have hquad : 0 ≤ 1 + rowIncrement a s i + rowIncrement a s i ^ 2 := by nlinarith
  have hquad' : 1 + rowIncrement a s i + rowIncrement a s i ^ 2 ≤ 3 := by
    nlinarith [(sq_le_one_iff_abs_le_one _).mpr ht]
  have hρ := damping_bounds hr a hp.threshold_sq_le i
  have hmul : 0 ≤ s.w i * damping a i := mul_nonneg (hw i) (by linarith [hρ.1])
  have hwρ : s.w i * damping a i ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hρ.2 (hw i)
    nlinarith
  have hup := mul_le_mul hwρ hquad' hquad (by norm_num : (0 : ℚ) ≤ 1 / 2)
  have hround := (roundUp_bounds (mesh_pos r m)
    (s.w i * damping a i * (1 + rowIncrement a s i + rowIncrement a s i ^ 2))).2
  rw [nextState_weight]
  linarith

/-- A remaining-fuel invariant. Its mesh allowance is deliberately generous;
the sharper consumed-step count is reserved for the lower-weight estimate. -/
theorem walk_weight_upper {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (fuel : ℕ) (s : State r m) (hx : RationalCube s.x)
    (hw : ∀ i, 0 ≤ s.w i)
    (hpot : potential s + (fuel : ℚ) * m * mesh r m < (r : ℚ) / 16)
    (k : ℕ) (hweight : ∀ i, s.w i ≤ 3 / 2 + k * mesh r m) :
    ∀ i, (walk a fuel s).w i ≤ 3 / 2 + (k + fuel : ℕ) * mesh r m := by
  have hr : 0 < r := by have := hp.dimension; omega
  have hη := (mesh_pos r m).le
  induction fuel generalizing s k with
  | zero => simpa [walk] using hweight
  | succ fuel ih =>
    simp only [walk]
    split_ifs with hhalf
    · intro i
      have h := hweight i
      push_cast
      have hnon : 0 ≤ (fuel + 1 : ℚ) * mesh r m := by positivity
      nlinarith
    · have hn := nextState_potential a x hp s hx hw hhalf
      have hpn : potential (nextState a s) + (fuel : ℚ) * m * mesh r m < (r : ℚ) / 16 := by
        push_cast at hpot
        nlinarith
      have hpnow : potential s < (r : ℚ) / 16 := by
        have hnon : 0 ≤ (fuel + 1 : ℕ) * (m : ℚ) * mesh r m := by positivity
        linarith
      have hwn : ∀ i, (nextState a s).w i ≤ 3 / 2 + (k + 1 : ℕ) * mesh r m := by
        intro i
        by_cases hi : i ∈ heavyRows (r := r) s.w
        · have h := heavy_next_weight hr a hp.threshold_sq_le s hw i hi
          have hk := hweight i
          push_cast
          linarith
        · have h := outside_heavy_next_weight a x hp s hx hw hhalf hpnow i hi
          push_cast
          have hnon : 0 ≤ (k : ℚ) * mesh r m := by positivity
          nlinarith
      have hi := ih (nextState a s) (nextState_cube hr a s hx)
        (nextState_weight_nonneg hr a hp.threshold_sq_le s hw) hpn (k + 1) hwn
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hi

theorem run_terminal_weight_upper {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (i : Fin m) : ((run a x).w i : ℝ) < 2 := by
  have hr : 0 < r := by have := hp.dimension; omega
  have hr' : (64 : ℝ) ≤ r := by exact_mod_cast hp.dimension
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by have := i.isLt; omega)
  have hη : (0 : ℝ) ≤ mesh r m := by exact_mod_cast (mesh_pos r m).le
  have hbudget := mesh_budget r m
  have hinit := initialState_potential a x hp
  have hpot : potential (initialState a x) + (stepBudget r : ℚ) * m * mesh r m <
      (r : ℚ) / 16 := by
    apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    nlinarith
  have hweight : ∀ j, (initialState a x).w j ≤ 3 / 2 + (1 : ℕ) * mesh r m := by
    intro j
    have h := (initialWeight_enclosure (m := m) hr (a j).threshold
      (hp.threshold_sq_le j)).2.le
    have he : Real.exp (-((a j).threshold : ℝ) ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    have h' : (initialWeight r m (a j).threshold : ℝ) ≤ 3 / 2 + (mesh r m : ℝ) := by
      linarith
    change initialWeight r m (a j).threshold ≤ 3 / 2 + (1 : ℕ) * mesh r m
    norm_num only [Nat.cast_one, one_mul]
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact h'
  have hwalk := walk_weight_upper a x hp (stepBudget r) (initialState a x) hp.cube
    (initialState_weights_nonneg a x hp) hpot 1 hweight i
  have hwalk' : ((run a x).w i : ℝ) ≤ 3 / 2 +
      (1 + (stepBudget r : ℝ)) * (mesh r m : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hwalk
    simpa [run] using h
  have hnon : (0 : ℝ) ≤ ((stepBudget r : ℝ) + 1) * (mesh r m : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hm hnon
  nlinarith

end Power2ModuleSVP.PartialColoringAlg
