import Power2ModuleSVP.FlatFrontend.Geometry.Complement
import Power2ModuleSVP.FlatFrontend.Geometry.Count
import Power2ModuleSVP.FlatFrontend.Geometry.Ordering

/-!
# Certificate

Unconditional geometry and preparation of the original rational frontend.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP
namespace FlatFrontend
noncomputable section
set_option exponentiation.threshold 1024

theorem markedRun_count {d : ℕ} (hd : Dyadic d) (hlarge : 2 ^ 512 ≤ d) :
    intervalCount d * 2 ^ 66 ≤ seedN d := by
  have hc := cutoff_seedN hlarge
  have hN : 0 < seedN d := lt_of_lt_of_le (by positivity : 0 < 2 ^ 509) hc.1
  have hshape := dyadic_shape hd ((by norm_num : 4 ≤ 2 ^ 512).trans hlarge)
  have hfit : 2 * blockShift (seedN d) + 2 ^ stage (seedN d) ≤ seedN d + 1 := by
    have := block_fits hc.2
    have := (block_parameters (seedN d)).1
    omega
  let p := (reducedCosinePolynomial (seedN d)).map (Int.castRingHom ℝ)
  have hleft : p.eval 1 = (2 : ℝ) ^ (stageIndex (seedN d) + 1) := by
    have hh := cosine_eq_reducedPolynomial hshape 0
    simp only [mul_zero, Real.cos_zero] at hh
    exact hh.symm.trans (cosine_axes hshape hfit).1
  have hright : p.eval (-1) = (2 : ℝ) ^ (stageIndex (seedN d) + 1) := by
    have hh := cosine_eq_reducedPolynomial hshape (Real.pi / 2)
    rw [mul_div_cancel₀ Real.pi (by norm_num : (2 : ℝ) ≠ 0), Real.cos_pi] at hh
    exact hh.symm.trans (cosine_axes hshape hfit).2
  have hh := height_small hc.2
  have hτ : (0 : ℝ) < 3 * (height (seedN d) : ℝ) / 4 := by
    have he : (0 : ℝ) < height (seedN d) := by exact_mod_cast height_positive hN
    positivity
  have hdegree : intervalCount d ≤ p.natDegree := by
    apply intervals_count_le_degree (gridRatio_positive hN) p hτ
      (by rw [hright, abs_of_pos (by positivity)]; exact hh)
      (by rw [hleft, abs_of_pos (by positivity)]; exact hh)
      (reducedGridNode (seedN d))
      (fun r _ => reducedGridNode_mem _ _)
      (reducedGridNode_antitone ((by norm_num : 2 ^ 100 ≤ 2 ^ 509).trans hc.1))
    intro j _
    exact markedCell_reduced_iff _ _
  have hcount : intervalCount d ≤ stageWidth (stage (seedN d)) :=
    hdegree.trans (reducedCosinePolynomial_real_degree _)
  exact (Nat.mul_le_mul_right _ hcount).trans (stage_admissible_at_cutoff hlarge)

/-- All six analytic and combinatorial fields hold for the unchanged scan. -/
theorem markedRunEstimates {d : ℕ} (hd : Dyadic d) (hlarge : 2 ^ 512 ≤ d) :
    MarkedRunEstimates d where
  width := (markedRun_width_clearances hd hlarge).1
  left_clearance := (markedRun_width_clearances hd hlarge).2.1
  right_clearance := (markedRun_width_clearances hd hlarge).2.2
  count := markedRun_count hd hlarge
  cosine_good := fun θ hout => cosine_good hd hlarge θ hout
  even_bound := evenPart_bound hd hlarge

/-- The concrete rational scan satisfies marked-run geometry at every admissible degree. -/
theorem markedRunGeometryHypothesis_holds : MarkedRunGeometryHypothesis :=
  fun _ hd hlarge => markedRunEstimates hd hlarge

/-- The concrete rational frontend satisfies all flat-seed preparation obligations. -/
theorem flatFrontend_preparation : FlatSeedPreparationHypothesis flatFrontend :=
  flatFrontend_preparation_of_geometry markedRunGeometryHypothesis_holds

end
end FlatFrontend
end Power2ModuleSVP
