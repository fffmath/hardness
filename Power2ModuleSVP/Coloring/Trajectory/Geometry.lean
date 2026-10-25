module

public import Power2ModuleSVP.Coloring.Trajectory.Projector

/-!
# Geometry

Dimension, direction, and boundary estimates for the rational walk.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP.PartialColoringAlg

open scoped BigOperators

theorem finRange_filter_length {r : ℕ} (p : Fin r → Prop) [DecidablePred p] :
    ((List.finRange r).filter p).length = (Finset.univ.filter p).card := by
  simpa only [List.toFinset_finRange, List.countP_eq_length_filter] using
    ((List.nodup_finRange r).card_eq_countP (P := p)).symm

theorem constraints_length_bound {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (s : State r m)
    (hhalf : ¬r ≤ 2 * signCoordinateCount s.x) :
    4 * (constraints a s).length ≤ 3 * r := by
  have hs := coloring_small_threshold_count (by omega : 0 < r)
    (fun i => (a i).threshold) hp.threshold_nonneg hp.entropy
  have hh : (heavyRows (r := r) s.w).length ≤ (r + 7) / 8 := by
    exact List.length_take_le _ _
  have he : (constraints a s).length = 1 + signCoordinateCount s.x +
      (heavyRows (r := r) s.w).length +
      (Finset.univ.filter fun i => (a i).threshold ≤ 1).card := by
    simp only [constraints, List.length_cons, List.length_append, List.length_map,
      finRange_filter_length, signCoordinateCount]
    omega
  have hr := hp.dimension
  omega

theorem constraints_trace_bound {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (s : State r m)
    (hhalf : ¬r ≤ 2 * signCoordinateCount s.x) :
    (r : ℚ) / 4 ≤ projectorTrace (constraints a s) := by
  have hc : 4 * ((constraints a s).length : ℚ) ≤ 3 * (r : ℚ) := by
    exact_mod_cast constraints_length_bound a x hp s hhalf
  linarith [projectorTrace_lower (constraints a s)]

theorem direction_norm {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (s : State r m)
    (hhalf : ¬r ≤ 2 * signCoordinateCount s.x) :
    (1 : ℚ) / 4 < dot (direction a s) (direction a s) ∧
      dot (direction a s) (direction a s) ≤ 1 := by
  have hr : (0 : ℚ) < r := by exact_mod_cast (show 0 < r by have := hp.dimension; omega)
  have ht := constraints_trace_bound a x hp s hhalf
  have hn := bestColumn_nonzero_of_trace (quadraticRows a s) (constraints a s) (by linarith)
  have hb := normalize_bounds _ hn
  simp only [direction, cachedColumns_eq]
  unfold orient
  split_ifs <;> simpa [dot] using hb

theorem energy_smul {r : ℕ} (b : List (ℚ × Vec r)) (v : Vec r) (c : ℚ) :
    energy b (c • v) = c ^ 2 * energy b v := by
  simp only [energy, dot_smul_right, mul_pow,
    ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro row _
  ring

theorem energy_neg {r : ℕ} (b : List (ℚ × Vec r)) (v : Vec r) :
    energy b (-v) = energy b v := by
  have hn : -v = (-1 : ℚ) • v := by ext j; simp
  rw [hn, energy_smul]
  norm_num

theorem direction_energy_le {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (s : State r m) (hw : ∀ i, 0 ≤ s.w i)
    (hhalf : ¬r ≤ 2 * signCoordinateCount s.x) :
    energy (quadraticRows a s) (direction a s) ≤
      4 / (r : ℚ) * ∑ i, s.w i * (a i).threshold ^ 2 := by
  let b := quadraticRows a s
  let C := constraints a s
  let q := bestColumn b (columns C)
  have hr : (0 : ℚ) < r := by exact_mod_cast (show 0 < r by have := hp.dimension; omega)
  have ht : (r : ℚ) / 4 ≤ projectorTrace C := constraints_trace_bound a x hp s hhalf
  have hn : q ≠ 0 := bestColumn_nonzero_of_trace b C (by linarith)
  have hqpos : 0 < dot q q := lt_of_le_of_ne (dot_self_nonneg _)
    (Ne.symm ((dot_self_eq_zero _).not.mpr hn))
  have hscore : 0 ≤ score b q := div_nonneg (quadraticRows_energy_nonneg a s hw q)
    (dot_self_nonneg _)
  have hb := bestColumn_trace_bound a s C hw hp.row_norm_le
  have hscoreBound : score b q ≤ 4 / (r : ℚ) * ∑ i, s.w i * (a i).threshold ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left ht hscore
    change score b q * projectorTrace C ≤ _ at hb
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hr).mpr
    nlinarith
  have hnorm := (normalize_bounds q hn).2
  have hscale : (normScale (dot q q))⁻¹ ^ 2 * dot q q ≤ 1 := by
    simpa [normalize, dot_smul_left, dot_smul_right, ← mul_assoc, ← pow_two] using hnorm
  have heq : energy b (normalize q) = score b q *
      ((normScale (dot q q))⁻¹ ^ 2 * dot q q) := by
    rw [normalize, energy_smul, score]
    field_simp
  have he : energy b (normalize q) ≤ score b q := by
    rw [heq]
    simpa using mul_le_mul_of_nonneg_left hscale hscore
  have hdir : energy b (direction a s) = energy b (normalize q) := by
    simp only [direction, cachedColumns_eq]
    unfold orient
    split_ifs
    · rfl
    · exact energy_neg _ _
  rw [hdir]
  exact he.trans hscoreBound

theorem dot_sq_le {r : ℕ} (u v : Vec r) : dot u v ^ 2 ≤ dot u u * dot v v := by
  simpa only [dot, pow_two] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v

theorem direction_inner_nonneg {r m : ℕ} (a : Fin m → Row r) (s : State r m) :
    0 ≤ dot s.x (direction a s) := orient_nonneg _ _

private theorem minFold_lt_one (l : List ℚ) (h : l.foldr min 1 < 1) :
    ∃ q ∈ l, l.foldr min 1 = q := by
  induction l with
  | nil => simp at h
  | cons q l ih =>
    simp only [List.foldr_cons] at h ⊢
    by_cases hq : q ≤ l.foldr min 1
    · exact ⟨q, by simp, min_eq_left hq⟩
    · obtain ⟨v, hv, he⟩ := ih (by rwa [min_eq_right (le_of_not_ge hq)] at h)
      exact ⟨v, by simp [hv], (min_eq_right (le_of_not_ge hq)).trans he⟩

theorem truncated_step_new_sign {r m : ℕ} (a : Fin m → Row r) (s : State r m)
    (htr : stepFraction s.x (direction a s) < 1) :
    ∃ j, (s.x j ≠ -1 ∧ s.x j ≠ 1) ∧
      ((nextState a s).x j = -1 ∨ (nextState a s).x j = 1) := by
  obtain ⟨v, hv, hv'⟩ := minFold_lt_one _ htr
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
  have he : stepFraction s.x (direction a s) = capacity s.x (direction a s) j := hv'
  have hz : direction a s j ≠ 0 := by
    intro hz
    simp [capacity, hz] at he
    linarith
  have hf : s.x j ≠ -1 ∧ s.x j ≠ 1 := by
    constructor <;> intro hj
    all_goals
      have hc : coordinate j ∈ constraints a s := by
        simp only [constraints, List.mem_cons, List.mem_append, List.mem_map]
        exact Or.inr (Or.inl (Or.inl ⟨j, by simp [hj], rfl⟩))
      have ho := direction_orthogonal a s _ hc
      exact hz (by simpa using ho)
  refine ⟨j, hf, ?_⟩
  change s.x j + stepSize r * (stepFraction s.x (direction a s) * direction a s j) = -1 ∨
    s.x j + stepSize r * (stepFraction s.x (direction a s) * direction a s j) = 1
  rw [he]
  unfold capacity
  have hr : r ≠ 0 := by intro hr; subst r; exact Fin.elim0 j
  have hΔ : stepSize r ≠ 0 := (stepSize_pos (Nat.pos_of_ne_zero hr)).ne'
  split_ifs with hp hn
  · right
    field_simp [hΔ, hz]
    ring
  · left
    field_simp [hΔ, hz]
    ring
  · exact False.elim (hz (by linarith))

theorem truncated_step_count {r m : ℕ} (a : Fin m → Row r) (s : State r m)
    (htr : stepFraction s.x (direction a s) < 1) :
    signCoordinateCount s.x + 1 ≤ signCoordinateCount (nextState a s).x := by
  obtain ⟨j, hj, hj'⟩ := truncated_step_new_sign a s htr
  have hsub : (Finset.univ.filter fun j => s.x j = -1 ∨ s.x j = 1) ⊂
      (Finset.univ.filter fun j => (nextState a s).x j = -1 ∨ (nextState a s).x j = 1) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro k hk
      have hk' := (Finset.mem_filter.mp hk).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [nextState_fixed a s k hk']
      exact hk'
    · intro he
      have : j ∈ Finset.univ.filter fun j => s.x j = -1 ∨ s.x j = 1 := by
        rw [he]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩
      exact (Finset.mem_filter.mp this).2.elim hj.1 hj.2
  exact Finset.card_lt_card hsub

theorem nextState_norm_identity {r m : ℕ} (a : Fin m → Row r) (s : State r m) :
    dot (nextState a s).x (nextState a s).x = dot s.x s.x +
      2 * stepSize r * stepFraction s.x (direction a s) * dot s.x (direction a s) +
      stepSize r ^ 2 * stepFraction s.x (direction a s) ^ 2 *
        dot (direction a s) (direction a s) := by
  simp only [nextState, dot_add_left, dot_add_right, dot_smul_left, dot_smul_right]
  rw [dot_comm (direction a s) s.x]
  ring

theorem nextState_norm_mono {r m : ℕ} (hr : 0 < r) (a : Fin m → Row r)
    (s : State r m) (hx : RationalCube s.x) :
    dot s.x s.x ≤ dot (nextState a s).x (nextState a s).x := by
  rw [nextState_norm_identity]
  have hα := (stepFraction_bounds hr s.x (direction a s) hx).1
  have hlin := direction_inner_nonneg a s
  have hΔ := (stepSize_pos hr).le
  have h₁ := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) hΔ) hα) hlin
  have h₂ := mul_nonneg (mul_nonneg (sq_nonneg (stepSize r))
    (sq_nonneg (stepFraction s.x (direction a s)))) (dot_self_nonneg (direction a s))
  linarith

theorem full_step_norm_progress {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (s : State r m)
    (hhalf : ¬r ≤ 2 * signCoordinateCount s.x)
    (hfull : stepFraction s.x (direction a s) = 1) :
    dot s.x s.x + stepSize r ^ 2 / 4 < dot (nextState a s).x (nextState a s).x := by
  rw [nextState_norm_identity, hfull]
  have hr : 0 < r := by have := hp.dimension; omega
  have hlin := mul_nonneg (stepSize_pos hr).le (direction_inner_nonneg a s)
  have hnorm := (direction_norm a x hp s hhalf).1
  have hpos := mul_pos (sq_pos_of_pos (stepSize_pos hr)) (sub_pos.mpr hnorm)
  nlinarith

end Power2ModuleSVP.PartialColoringAlg
