import Power2ModuleSVP.FlatFrontend2Main
import Power2ModuleSVP.RudinShapiroWave

/-! Exact pairing of the implemented background word. -/
namespace Power2ModuleSVP
namespace FlatFrontend
open scoped BigOperators

theorem cosineCoefficient_sign {N j : ℕ} (h : cosineSelected N j = true) :
    cosineCoefficient N j = -1 ∨ cosineCoefficient N j = 1 := by
  simp only [cosineSelected, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold cosineCoefficient
  dsimp only
  rcases h with h | h
  · rw [ite_eq_left h, (rsWords_coeff _ _).1]
    exact ((rudinShapiro_coefficients _).1 _ (by omega)).1
  · split_ifs with h₁
    · rw [(rsWords_coeff _ _).1]
      exact ((rudinShapiro_coefficients _).1 _ (by omega)).1
    · rw [(rsWords_coeff _ _).2]
      exact ((rudinShapiro_coefficients _).1 _ (by omega)).2

theorem cosineCoefficient_unselected {N j : ℕ} (h : cosineSelected N j = false) :
    cosineCoefficient N j = 0 := by
  simp only [cosineSelected, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    decide_eq_false_iff_not] at h
  unfold cosineCoefficient
  dsimp only
  split_ifs with h₁ h₂
  · rcases h.1 with h | h <;> omega
  · rcases h.2 with h | h <;> omega
  · rfl

theorem seedIntegerSign_of_sign {z : ℤ} (h : z = -1 ∨ z = 1) :
    seedIntegerSign z = z := by
  rcases h with rfl | rfl <;> norm_num [seedIntegerSign]

theorem background_pair {d j : ℕ} (hd : d = 4 * seedN d + 4)
    (hj : j < seedN d) :
    let N := seedN d
    let c := cosineCoefficient N (j + 1)
    let s := rudinShapiroCoefficient (j + 1)
    (background d).getD (2 * N + (2 * j + 2)) 1 =
      (if cosineSelected N (j + 1) then c else s) ∧
    (background d).getD (2 * N - (2 * j + 2)) 1 =
      (if cosineSelected N (j + 1) then c else -s) := by
  have hh : 2 * seedN d + (2 * j + 2) < d := by omega
  have hl : 2 * seedN d - (2 * j + 2) < d := by omega
  have hdiv : (2 * seedN d - (2 * seedN d - (2 * j + 2))) / 2 = j + 1 := by omega
  have hp : (2 * seedN d + (2 * j + 2) - 2 * seedN d) / 2 = j + 1 := by omega
  have hs : (stablePrefix (seedN d + 1)).getD (j + 1) 1 =
      rudinShapiroCoefficient (j + 1) := by
    have hb : j + 1 < (stablePrefix (seedN d + 1)).length := by
      rw [stablePrefix_length]; omega
    simpa only [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hb, Option.getD_some] using
      (stablePrefix_coeff (m := seedN d + 1) (j := j + 1) (by omega))
  have eval (i : ℕ) (hi : i < d) : (background d).getD i 1 =
      (if i = 2 * seedN d then 1
      else if i < 4 * seedN d + 1 ∧ i % 2 = 0 then
        let j := if i < 2 * seedN d then (2 * seedN d - i) / 2
          else (i - 2 * seedN d) / 2
        if cosineSelected (seedN d) j then cosineCoefficient (seedN d) j
        else if i < 2 * seedN d then -(stablePrefix (seedN d + 1)).getD j 1
          else (stablePrefix (seedN d + 1)).getD j 1
      else 1) := by
    simp only [background, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi, Option.map_some, Option.getD_some]
  dsimp only
  constructor
  · rw [eval _ hh, ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩]
    simp only [ite_eq_right (show ¬ 2 * seedN d + (2 * j + 2) < 2 * seedN d by omega), hp, hs]
  · rw [eval _ hl, ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩]
    simp only [ite_eq_left (show 2 * seedN d - (2 * j + 2) < 2 * seedN d by omega), hdiv, hs]

theorem background_pair_sum {d j : ℕ} (hd : d = 4 * seedN d + 4)
    (hj : j < seedN d) :
    ((seedIntegerSign ((background d).getD (2 * seedN d + (2 * j + 2)) 1) : ℝ) +
      seedIntegerSign ((background d).getD (2 * seedN d - (2 * j + 2)) 1)) / 2 =
      (cosineCoefficient (seedN d) (j + 1) : ℝ) := by
  obtain ⟨hp, hm⟩ := background_pair hd hj
  rw [hp, hm]
  cases h : cosineSelected (seedN d) (j + 1) with
  | true =>
    simp only [↓reduceIte, seedIntegerSign_of_sign (cosineCoefficient_sign h)]
    ring
  | false =>
    have hs := rudinShapiroCoefficient_sign (j + 1)
    have hn : -rudinShapiroCoefficient (j + 1) = -1 ∨
        -rudinShapiroCoefficient (j + 1) = 1 := by omega
    simp only [Bool.false_eq_true, ↓reduceIte, seedIntegerSign_of_sign hs,
      seedIntegerSign_of_sign hn, Int.cast_neg, cosineCoefficient_unselected h,
      Int.cast_zero]
    ring

theorem background_pair_sub {d j : ℕ} (hd : d = 4 * seedN d + 4)
    (hj : j < seedN d) :
    ((seedIntegerSign ((background d).getD (2 * seedN d + (2 * j + 2)) 1) : ℝ) -
      seedIntegerSign ((background d).getD (2 * seedN d - (2 * j + 2)) 1)) / 2 =
      if cosineSelected (seedN d) (j + 1) then 0
      else (rudinShapiroCoefficient (j + 1) : ℝ) := by
  obtain ⟨hp, hm⟩ := background_pair hd hj
  rw [hp, hm]
  cases h : cosineSelected (seedN d) (j + 1) with
  | true => simp
  | false =>
    have hs := rudinShapiroCoefficient_sign (j + 1)
    have hn : -rudinShapiroCoefficient (j + 1) = -1 ∨
        -rudinShapiroCoefficient (j + 1) = 1 := by omega
    simp only [Bool.false_eq_true, ↓reduceIte, seedIntegerSign_of_sign hs,
      seedIntegerSign_of_sign hn, Int.cast_neg]
    ring

theorem cosine_eq_sum {d : ℕ} (hd : d = 4 * seedN d + 4) (θ : ℝ) :
    cosine d θ = ∑ j ∈ Finset.range (seedN d),
      (cosineCoefficient (seedN d) (j + 1) : ℝ) * Real.cos ((2 * (j : ℝ) + 2) * θ) := by
  unfold cosine
  apply Finset.sum_congr rfl
  intro j hj
  rw [background_pair_sum hd (Finset.mem_range.mp hj)]

theorem evenPart_eq_sum {d : ℕ} (hd : d = 4 * seedN d + 4) (θ : ℝ) :
    evenPart d θ = ∑ j ∈ Finset.range (seedN d),
      (if cosineSelected (seedN d) (j + 1) then 0
        else (rudinShapiroCoefficient (j + 1) : ℝ)) * Real.sin ((2 * (j : ℝ) + 2) * θ) := by
  unfold evenPart
  apply Finset.sum_congr rfl
  intro j hj
  rw [background_pair_sub hd (Finset.mem_range.mp hj)]

end FlatFrontend
end Power2ModuleSVP
