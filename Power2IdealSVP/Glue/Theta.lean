import Power2IdealSVP.Ideal.Theta
import Power2IdealSVP.Spin.Defs

/-!
# Identification of the two sparse-spin objectives

Paper: `paper/power2-ideal-svp.txt`, equations (1) and (2).
The prefix-sum and support-rank descriptions enumerate the same coefficient arrays.
-/

namespace Power2IdealSVP.Glue

open Power2ModuleSVP (Coeff)
open Power2IdealSVP

private def prefixCard {n : ℕ} (σ : Coeff n) (k : ℕ) : ℕ :=
  ((Spin.support σ).filter fun i => i.val < k).card

private theorem prefixCard_zero {n : ℕ} (σ : Coeff n) : prefixCard σ 0 = 0 := by
  simp [prefixCard]

private theorem prefixCard_all {n : ℕ} (σ : Coeff n) :
    prefixCard σ n = (Spin.support σ).card := by simp [prefixCard]

private theorem prefixCard_rank {n : ℕ} (σ : Coeff n) (i : Fin n) :
    prefixCard σ i.val = Spin.supportRank σ i := rfl

private theorem prefixCard_succ {n : ℕ} (σ : Coeff n) (i : Fin n) :
    prefixCard σ (i.val + 1) = prefixCard σ i.val + if σ i = 0 then 0 else 1 := by
  classical
  by_cases hi : σ i = 0
  · have he : (Spin.support σ).filter (fun j => j.val < i.val + 1) =
        (Spin.support σ).filter (fun j => j.val < i.val) := by
      ext j
      simp only [Finset.mem_filter, Spin.mem_support]
      constructor
      · rintro ⟨hj, hj'⟩
        refine ⟨hj, ?_⟩
        have hne : j.val ≠ i.val := fun h => hj (Fin.ext h ▸ hi)
        omega
      · rintro ⟨hj, hj'⟩
        exact ⟨hj, by omega⟩
    unfold prefixCard
    rw [he]
    simp only [hi, ↓reduceIte, add_zero]
  · have he : (Spin.support σ).filter (fun j => j.val < i.val + 1) =
        insert i ((Spin.support σ).filter (fun j => j.val < i.val)) := by
      ext j
      simp only [Finset.mem_filter, Spin.mem_support, Finset.mem_insert]
      constructor
      · rintro ⟨hj, hj'⟩
        by_cases hji : j = i
        · exact Or.inl hji
        · exact Or.inr ⟨hj, by
            have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
            omega⟩
      · rintro (rfl | ⟨hj, hj'⟩)
        · exact ⟨hi, by omega⟩
        · exact ⟨hj, by omega⟩
    have hnot : i ∉ (Spin.support σ).filter (fun j => j.val < i.val) := by simp
    unfold prefixCard
    rw [he, Finset.card_insert_of_notMem hnot]
    simp only [hi, ↓reduceIte]

private theorem prefix_rank_formula {n : ℕ} (σ : Coeff n) (η : ℤ)
    (he : ∀ i, σ i ≠ 0 → σ i = η * (-1) ^ Spin.supportRank σ i) :
    ∀ k ≤ n, 2 * Ideal.prefixSum σ k = η * (1 - (-1) ^ prefixCard σ k) := by
  intro k hk
  induction k with
  | zero => simp [prefixCard_zero]
  | succ k ih =>
    have hk' : k < n := by omega
    let i : Fin n := ⟨k, hk'⟩
    have hp := Ideal.prefixSum_succ σ i
    have hc := prefixCard_succ σ i
    have ih' := ih (by omega)
    change Ideal.prefixSum σ (k + 1) = Ideal.prefixSum σ k + σ i at hp
    change prefixCard σ (k + 1) = prefixCard σ k + _ at hc
    rw [hp, hc]
    by_cases hi : σ i = 0
    · simp only [hi, ↓reduceIte, add_zero]
      exact ih'
    · simp only [hi, ↓reduceIte, pow_succ]
      have he' := he i hi
      rw [← prefixCard_rank] at he'
      change σ i = η * (-1) ^ prefixCard σ k at he'
      rw [he']
      linear_combination ih'

/-- The rank and prefix definitions of odd alternation agree. -/
theorem oddAlternating_iff {n : ℕ} (σ : Coeff n) :
    Ideal.OddAlternating σ ↔ Spin.OddAlternating σ := by
  classical
  constructor
  · intro hσ
    obtain ⟨η, hη, ht, hp⟩ := hσ
    have hstep (i : Fin n) (hi : σ i ≠ 0) :
        σ i = η - 2 * Ideal.prefixSum σ i.val := by
      have h0 := hp i.val (by omega)
      have h1 := hp (i.val + 1) (by omega)
      have hs := Ideal.prefixSum_succ σ i
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> omega
    have hformula : ∀ k ≤ n,
        2 * Ideal.prefixSum σ k = η * (1 - (-1) ^ prefixCard σ k) := by
      intro k hk
      induction k with
      | zero => simp [prefixCard_zero]
      | succ k ih =>
        have hk' : k < n := by omega
        let i : Fin n := ⟨k, hk'⟩
        have hs := Ideal.prefixSum_succ σ i
        have hc := prefixCard_succ σ i
        have ih' := ih (by omega)
        change Ideal.prefixSum σ (k + 1) = Ideal.prefixSum σ k + σ i at hs
        change prefixCard σ (k + 1) = prefixCard σ k + _ at hc
        rw [hs, hc]
        by_cases hi : σ i = 0
        · simp only [hi, ↓reduceIte, add_zero]
          exact ih'
        · simp only [hi, ↓reduceIte, pow_succ]
          have he := hstep i hi
          change σ i = η - 2 * Ideal.prefixSum σ k at he
          linear_combination 2 * he - ih'
    refine ⟨fun i => Ideal.OddAlternating.ternary ⟨η, hη, ht, hp⟩ i, ?_, η, hη, ?_⟩
    · have hs : Ideal.spinSupport σ = Spin.support σ := rfl
      rw [← hs]
      exact Ideal.OddAlternating.odd_card ⟨η, hη, ht, hp⟩
    · intro i hi
      have he := hstep i (Spin.mem_support σ i |>.mp hi)
      have hf := hformula i.val (by omega)
      rw [prefixCard_rank] at hf
      linear_combination he - hf
  · intro hσ
    obtain ⟨η, hη, he⟩ := hσ.2.2
    have hf := prefix_rank_formula σ η (fun i hi => he i ((Spin.mem_support σ i).mpr hi))
    refine ⟨η, hη, ?_, ?_⟩
    · have ht := hf n le_rfl
      rw [Ideal.prefixSum_all, prefixCard_all, hσ.2.1.neg_one_pow] at ht
      omega
    · intro k hk
      have ht := hf k hk
      rcases neg_one_pow_eq_or ℤ (prefixCard σ k) with he | he
      · left
        rw [he] at ht
        omega
      · right
        rw [he] at ht
        omega

/-- Both finite objectives have the same value for every positive degree and multiplier. -/
theorem thetaOf_eq_Theta {n : ℕ} (hn : 0 < n) (G : Coeff n) :
    Ideal.thetaOf hn G = Spin.Theta G := by
  apply le_antisymm
  · apply (Spin.le_Theta_iff hn G _).mpr
    obtain ⟨σ, hσ, hf⟩ := (Ideal.le_thetaOf_iff hn G _).mp le_rfl
    exact ⟨σ, (oddAlternating_iff σ).mp hσ, fun i hi =>
      hf i ((Spin.mem_support σ i).mp hi)⟩
  · apply (Ideal.le_thetaOf_iff hn G _).mpr
    obtain ⟨σ, hσ, hf⟩ := (Spin.le_Theta_iff hn G _).mp le_rfl
    exact ⟨σ, (oddAlternating_iff σ).mpr hσ, fun i hi =>
      hf i ((Spin.mem_support σ i).mpr hi)⟩

end Power2IdealSVP.Glue
