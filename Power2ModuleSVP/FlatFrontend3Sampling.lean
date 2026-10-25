import Power2ModuleSVP.FlatFrontend3Polynomial

/-! Transfer of the exact inclusive marker to continuous cosine values. -/
namespace Power2ModuleSVP
namespace FlatFrontend
open scoped BigOperators
noncomputable section

def sampleError (N : ℕ) : ℚ := (4 * (N : ℚ) + 2) * fineError N

theorem cosinePolynomialValue_cast (N : ℕ) (q : ℚ) :
    (cosinePolynomialValue N q : ℝ) =
      ((cosinePolynomial N).map (Int.castRingHom ℝ)).eval (q : ℝ) := by
  rw [cosinePolynomialValue_spec]
  change (Rat.castHom ℝ) (((cosinePolynomial N).map (Int.castRingHom ℚ)).eval q) = _
  rw [← Polynomial.eval₂_at_apply, Polynomial.eval₂_eq_eval_map, Polynomial.map_map]
  rfl

theorem markedCell_iff (N j : ℕ) : markedCell N j = true ↔
    ∃ r, j * gridRatio N ≤ r ∧ r ≤ (j + 1) * gridRatio N ∧
      |cosinePolynomialValue N (gridSample N r)| ≤ 3 * height N / 4 := by
  simp only [markedCell, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨r, hr, hm⟩
    exact ⟨j * gridRatio N + r, by omega, by nlinarith, hm⟩
  · rintro ⟨r, hl, hr, hm⟩
    refine ⟨r - j * gridRatio N, by
      have : r ≤ j * gridRatio N + gridRatio N := by nlinarith
      omega, ?_⟩
    simpa only [Nat.add_sub_cancel' hl] using hm

/-- Pointwise enclosure for the exact integer-polynomial comparison used
by the executable marker. -/
theorem grid_cosine_value_error {d : ℕ} (hd : d = 4 * seedN d + 4)
    (hN : 0 < seedN d) {r : ℕ} (hr : r ≤ gridSize (seedN d)) :
    |(cosinePolynomialValue (seedN d) (gridSample (seedN d) r) : ℝ) -
      cosine d (seedFineAngle (gridSize (seedN d)) r)| ≤
        8 * (seedN d : ℝ) ^ 3 * (sampleError (seedN d) : ℝ) := by
  rw [cosinePolynomialValue_cast, ← implementedCosineData_polynomial,
    ← implementedCosineData_angle hd]
  have he := (implementedCosineData (seedN d)).polynomial_sub_bound
    (gridSample_mem (seedN d) r)
    (show Real.cos (seedFineAngle (gridSize (seedN d)) r) ∈ Set.Icc (-1) 1 from
      ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  rw [abs_sub_comm] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [abs_sub_comm]
  exact gridSample_error hN hr (gridSize_positive hN)

theorem markedCell_cosine_witness {d j : ℕ} (hd : d = 4 * seedN d + 4)
    (hN : 0 < seedN d)
    (hbudget : 8 * (seedN d : ℝ) ^ 3 * (sampleError (seedN d) : ℝ) ≤ (height (seedN d) : ℝ) / 16)
    (hj : j < seedN d / 2) (hm : markedCell (seedN d) j = true) :
    ∃ r, j * gridRatio (seedN d) ≤ r ∧ r ≤ (j + 1) * gridRatio (seedN d) ∧
      |cosine d (seedFineAngle (gridSize (seedN d)) r)| ≤ 13 * (height (seedN d) : ℝ) / 16 := by
  obtain ⟨r, hl, hr, hm⟩ := (markedCell_iff _ _).mp hm
  have hr' : r ≤ gridSize (seedN d) :=
    hr.trans (Nat.mul_le_mul_right _ (by omega))
  refine ⟨r, hl, hr, ?_⟩
  have he := (grid_cosine_value_error hd hN hr').trans hbudget
  have hm' : |(cosinePolynomialValue (seedN d) (gridSample (seedN d) r) : ℝ)| ≤
      3 * (height (seedN d) : ℝ) / 4 := by exact_mod_cast hm
  have ht := abs_sub_abs_le_abs_sub
    (cosine d (seedFineAngle (gridSize (seedN d)) r))
    (cosinePolynomialValue (seedN d) (gridSample (seedN d) r) : ℝ)
  rw [abs_sub_comm] at ht
  linarith

/-- The other direction uses an unmarked sample and its angular distance.
This is the local ingredient for covering the complement of the runs. -/
theorem unmarkedCell_cosine_bound {d j r : ℕ} (hd : d = 4 * seedN d + 4)
    (hN : 0 < seedN d)
    (hbudget : 8 * (seedN d : ℝ) ^ 3 * (sampleError (seedN d) : ℝ) ≤ (height (seedN d) : ℝ) / 16)
    (hj : j < seedN d / 2) (hl : j * gridRatio (seedN d) ≤ r)
    (hr : r ≤ (j + 1) * gridRatio (seedN d))
    (hm : markedCell (seedN d) j = false) {θ : ℝ}
    (hspacing : 2 * (seedN d : ℝ) ^ 2 * |θ - seedFineAngle (gridSize (seedN d)) r| ≤
      Real.pi * (height (seedN d) : ℝ) / 64) :
    5 * (height (seedN d) : ℝ) / 8 < |cosine d θ| := by
  have hr' : r ≤ gridSize (seedN d) :=
    hr.trans (Nat.mul_le_mul_right _ (by omega))
  have he := (grid_cosine_value_error hd hN hr').trans hbudget
  have hgood : 3 * height (seedN d) / 4 <
      |cosinePolynomialValue (seedN d) (gridSample (seedN d) r)| := by
    by_contra h
    have htrue := (markedCell_iff _ _).mpr ⟨r, hl, hr, le_of_not_gt h⟩
    rw [hm] at htrue
    contradiction
  have hgood' : 3 * (height (seedN d) : ℝ) / 4 <
      |(cosinePolynomialValue (seedN d) (gridSample (seedN d) r) : ℝ)| := by exact_mod_cast hgood
  have ha := (implementedCosineData (seedN d)).angle_sub_bound θ
    (seedFineAngle (gridSize (seedN d)) r)
  rw [implementedCosineData_angle hd, implementedCosineData_angle hd] at ha
  have hdiff := ha.trans hspacing
  have ht := abs_sub_abs_le_abs_sub
    (cosinePolynomialValue (seedN d) (gridSample (seedN d) r) : ℝ)
    (cosine d (seedFineAngle (gridSize (seedN d)) r))
  have ht' := abs_sub_abs_le_abs_sub (cosine d (seedFineAngle (gridSize (seedN d)) r))
    (cosine d θ)
  rw [abs_sub_comm] at ht'
  have hh : (0 : ℝ) < height (seedN d) := by exact_mod_cast height_positive hN
  have hpi := mul_lt_mul_of_pos_right Real.pi_lt_four hh
  linarith

/-- Exact reduced-variable identity for every rational sample in the unit
interval; no transcendental approximation is used in this equality. -/
theorem cosinePolynomialValue_reduced (N : ℕ) (q : ℚ)
    (hq : (q : ℝ) ∈ Set.Icc (-1) 1) :
    (cosinePolynomialValue N q : ℝ) =
      ((reducedCosinePolynomial N).map (Int.castRingHom ℝ)).eval (2 * (q : ℝ) ^ 2 - 1) := by
  have hshape : 4 * N + 4 = 4 * seedN (4 * N + 4) + 4 := by rw [seedN_four]
  have hpoly := cosine_eq_polynomial hshape (Real.arccos (q : ℝ))
  have hred := cosine_eq_reducedPolynomial hshape (Real.arccos (q : ℝ))
  rw [seedN_four, Real.cos_arccos hq.1 hq.2] at hpoly
  rw [seedN_four, Real.cos_two_mul, Real.cos_arccos hq.1 hq.2] at hred
  rw [cosinePolynomialValue_cast, ← hpoly, hred]

def reducedGridNode (N r : ℕ) : ℝ := 2 * (gridSample N r : ℝ) ^ 2 - 1

theorem reducedGridNode_mem (N r : ℕ) : reducedGridNode N r ∈ Set.Icc (-1) 1 := by
  have hq := gridSample_mem N r
  have hs : (gridSample N r : ℝ) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr (abs_le.mpr hq)
  dsimp [reducedGridNode]
  constructor <;> nlinarith [sq_nonneg (gridSample N r : ℝ)]

theorem markedCell_reduced_iff (N j : ℕ) : markedCell N j = true ↔
    ∃ r, j * gridRatio N ≤ r ∧ r ≤ (j + 1) * gridRatio N ∧
      |((reducedCosinePolynomial N).map (Int.castRingHom ℝ)).eval (reducedGridNode N r)| ≤
        3 * (height N : ℝ) / 4 := by
  rw [markedCell_iff]
  constructor
  · rintro ⟨r, hl, hr, hm⟩
    refine ⟨r, hl, hr, ?_⟩
    rw [reducedGridNode, ← cosinePolynomialValue_reduced N _ (gridSample_mem N r)]
    exact_mod_cast hm
  · rintro ⟨r, hl, hr, hm⟩
    refine ⟨r, hl, hr, ?_⟩
    rw [reducedGridNode, ← cosinePolynomialValue_reduced N _ (gridSample_mem N r)] at hm
    exact_mod_cast hm

end
end FlatFrontend
end Power2ModuleSVP
