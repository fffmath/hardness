import Power2ModuleSVP.FlatFrontend3Words

/-! Finite block evaluations for the concrete word. -/
namespace Power2ModuleSVP
namespace FlatFrontend
open scoped BigOperators
noncomputable section

theorem sum_block {M T m : ℕ} (h : T + m ≤ M) (f : ℕ → ℂ) (z : ℂ) :
    (∑ j ∈ Finset.range M,
      (if T ≤ j ∧ j < T + m then f (j - T) else 0) * z ^ j) =
      z ^ T * ∑ j ∈ Finset.range m, f j * z ^ j := by
  have hsub : Finset.Ico T (T + m) ⊆ Finset.range M := by
    intro j hj
    simp only [Finset.mem_Ico, Finset.mem_range] at *
    omega
  calc
    _ = ∑ j ∈ Finset.Ico T (T + m), f (j - T) * z ^ j := by
      rw [← Finset.sum_subset hsub]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [ite_eq_left (Finset.mem_Ico.mp hj)]
      · intro j _ hj
        have : ¬ (T ≤ j ∧ j < T + m) := by simpa only [Finset.mem_Ico] using hj
        simp only [ite_eq_right this, zero_mul]
    _ = ∑ j ∈ Finset.range m, f j * z ^ (T + j) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left]
    _ = _ := by simp only [pow_add, Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

theorem block_parameters (N : ℕ) : 0 < blockShift N ∧ 2 ^ stage N ≤ blockShift N := by
  constructor
  · unfold blockShift; positivity
  · unfold blockShift
    exact Nat.pow_le_pow_right (by omega) (by omega)

theorem cosineSelected_iff (N j : ℕ) : cosineSelected N j = true ↔
    (blockShift N ≤ j ∧ j < blockShift N + 2 ^ stage N) ∨
    (2 * blockShift N ≤ j ∧ j < 2 * blockShift N + 2 ^ stage N) := by
  simp [cosineSelected]

theorem cosineCoefficient_split (N j : ℕ) :
    (cosineCoefficient N j : ℂ) =
      (if blockShift N ≤ j ∧ j < blockShift N + 2 ^ stage N then
        ((rudinShapiroP (stage N)).coeff (j - blockShift N) : ℂ) else 0) +
      (if 2 * blockShift N ≤ j ∧ j < 2 * blockShift N + 2 ^ stage N then
        ((rudinShapiroQ (stage N)).coeff (j - 2 * blockShift N) : ℂ) else 0) := by
  have hp := block_parameters N
  unfold cosineCoefficient
  dsimp only
  split_ifs with h₁ h₂
  · omega
  · simp only [(rsWords_coeff _ _).1, add_zero]
  · simp only [(rsWords_coeff _ _).2, zero_add]
  · simp

theorem removedCoefficient_split (N j : ℕ) :
    (if cosineSelected N j then (rudinShapiroCoefficient j : ℂ) else 0) =
      (if blockShift N ≤ j ∧ j < blockShift N + 2 ^ stage N then
        ((rudinShapiroP (stage N)).coeff (j - blockShift N) : ℂ) else 0) +
      (if 2 * blockShift N ≤ j ∧ j < 2 * blockShift N + 2 ^ stage N then
        ((rudinShapiroP (stage N)).coeff (j - 2 * blockShift N) : ℂ) else 0) := by
  have hp := block_parameters N
  have hb (T : ℕ) (hT : T = blockShift N ∨ T = 2 * blockShift N)
      (hj : T ≤ j ∧ j < T + 2 ^ stage N) :
      rudinShapiroCoefficient j = (rudinShapiroP (stage N)).coeff (j - T) := by
    have hlt : j - T < 2 ^ stage N := by omega
    have hh := rudinShapiro_seed_blocks (k := stage N) hlt
    rcases hT with rfl | rfl
    · have he := hh.1
      change rudinShapiroCoefficient (blockShift N + (j - blockShift N)) = _ at he
      rw [Nat.add_sub_cancel' hj.1] at he
      exact he
    · have he := hh.2
      change rudinShapiroCoefficient (2 * blockShift N + (j - 2 * blockShift N)) = _ at he
      rw [Nat.add_sub_cancel' hj.1] at he
      exact he
  by_cases h₁ : blockShift N ≤ j ∧ j < blockShift N + 2 ^ stage N
  · have h₂ : ¬ (2 * blockShift N ≤ j ∧ j < 2 * blockShift N + 2 ^ stage N) := by omega
    rw [ite_eq_left ((cosineSelected_iff N j).mpr (Or.inl h₁)),
      ite_eq_left h₁, ite_eq_right h₂, add_zero, hb _ (Or.inl rfl) h₁]
  · by_cases h₂ : 2 * blockShift N ≤ j ∧ j < 2 * blockShift N + 2 ^ stage N
    · rw [ite_eq_left ((cosineSelected_iff N j).mpr (Or.inr h₂)),
        ite_eq_right h₁, ite_eq_left h₂, zero_add, hb _ (Or.inr rfl) h₂]
    · rw [ite_eq_right (by simpa [cosineSelected_iff] using And.intro h₁ h₂),
        ite_eq_right h₁, ite_eq_right h₂, zero_add]

theorem cosine_block_evaluation {N : ℕ}
    (hfit : 2 * blockShift N + 2 ^ stage N ≤ N + 1) (z : ℂ) :
    (∑ j ∈ Finset.range (N + 1), (cosineCoefficient N j : ℂ) * z ^ j) =
      z ^ blockShift N * rsEval (rudinShapiroP (stage N)) z +
      z ^ (2 * blockShift N) * rsEval (rudinShapiroQ (stage N)) z := by
  simp_rw [cosineCoefficient_split, add_mul]
  rw [Finset.sum_add_distrib,
    sum_block (T := blockShift N) (m := 2 ^ stage N) (by omega)
      (fun j => ((rudinShapiroP (stage N)).coeff j : ℂ)) z,
    sum_block hfit (fun j => ((rudinShapiroQ (stage N)).coeff j : ℂ)) z]
  have hP : (rudinShapiroP (stage N)).natDegree < 2 ^ stage N := by
    rw [(rudinShapiro_natDegree _).1]
    have : 0 < 2 ^ stage N := by positivity
    omega
  have hQ : (rudinShapiroQ (stage N)).natDegree < 2 ^ stage N := by
    rw [(rudinShapiro_natDegree _).2]
    have : 0 < 2 ^ stage N := by positivity
    omega
  simp only [show (∑ j ∈ Finset.range (2 ^ stage N),
    ((rudinShapiroP (stage N)).coeff j : ℂ) * z ^ j) =
      rsEval (rudinShapiroP (stage N)) z from rsPrefixEval_eq_eval hP z,
    show (∑ j ∈ Finset.range (2 ^ stage N),
    ((rudinShapiroQ (stage N)).coeff j : ℂ) * z ^ j) =
      rsEval (rudinShapiroQ (stage N)) z from rsPrefixEval_eq_eval hQ z]

theorem removed_block_evaluation {N : ℕ}
    (hfit : 2 * blockShift N + 2 ^ stage N ≤ N + 1) (z : ℂ) :
    (∑ j ∈ Finset.range (N + 1),
      (if cosineSelected N j then (rudinShapiroCoefficient j : ℂ) else 0) * z ^ j) =
      z ^ blockShift N * rsEval (rudinShapiroP (stage N)) z +
      z ^ (2 * blockShift N) * rsEval (rudinShapiroP (stage N)) z := by
  simp_rw [removedCoefficient_split, add_mul]
  rw [Finset.sum_add_distrib,
    sum_block (T := blockShift N) (m := 2 ^ stage N) (by omega)
      (fun j => ((rudinShapiroP (stage N)).coeff j : ℂ)) z,
    sum_block hfit (fun j => ((rudinShapiroP (stage N)).coeff j : ℂ)) z]
  have hP : (rudinShapiroP (stage N)).natDegree < 2 ^ stage N := by
    rw [(rudinShapiro_natDegree _).1]
    have : 0 < 2 ^ stage N := by positivity
    omega
  simp only [show (∑ j ∈ Finset.range (2 ^ stage N),
    ((rudinShapiroP (stage N)).coeff j : ℂ) * z ^ j) =
      rsEval (rudinShapiroP (stage N)) z from rsPrefixEval_eq_eval hP z]

end
end FlatFrontend
end Power2ModuleSVP
