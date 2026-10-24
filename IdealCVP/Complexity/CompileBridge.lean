import IdealCVP.Complexity.CompileList

/-! # Correctness of the total list-interface reference compiler -/
namespace IdealCVP

namespace MaskedSys

theorem paddedSystem_hasSolution_iff (S : MaskedSys) :
    S.paddedSystem.HasSolution ↔ S.toSystem.HasSolution := by
  constructor
  · rintro ⟨ξ, hμ, hr⟩
    refine ⟨(fun j => ξ j.succ), ?_, ?_⟩
    · intro j hj
      exact hμ j.succ hj
    · funext i
      have hi := congrFun hr i.succ
      simpa [MaskedSystem.residual, paddedSystem, Fin.sum_univ_succ] using hi
  · rintro ⟨ξ, hμ, hr⟩
    refine ⟨Fin.cases true ξ, ?_, ?_⟩
    · intro j
      refine Fin.cases (by simp [paddedSystem]) (fun j => ?_) j
      simpa only [paddedSystem, Fin.cases_succ] using hμ j
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [MaskedSystem.residual, paddedSystem, Fin.sum_univ_succ]
      · have hi := congrFun hr i
        simpa [MaskedSystem.residual, paddedSystem, Fin.sum_univ_succ] using hi

end MaskedSys

theorem cvpNoInput_not_mem : cvpNoInput ∉ PrincipalCVP := by
  rintro ⟨_, q, hq⟩
  have hn := sqNorm_nonneg (Cyclotomic.mul (ofList (d := cvpNoInput.1) cvpNoInput.2.1) q -
    ofList cvpNoInput.2.2.1)
  change _ ≤ (-1 : ℤ) at hq
  omega

/-- The reference code lists exactly the existing compiler's coefficients. -/
theorem compileList_eq (S : MaskedSys) (hw : S.WellFormed) :
    compileList S = toCVPInput S.reductionData.toPrincipalCVPInstance := by
  simp only [compileList, hw, ↓reduceIte]

/-- Correctness is unconditional, including every degenerate and malformed input. -/
theorem compileList_correct (S : MaskedSys) :
    S.Feasible ↔ compileList S ∈ PrincipalCVP := by
  by_cases hw : S.WellFormed
  · rw [compileList_eq S hw, toCVPInput_mem_iff]
    change S.Feasible ↔ CVPYes S.reductionData.lattice S.reductionData.T S.reductionData.Δ
    rw [← S.reductionData.compiler_correct]
    exact ⟨fun h => (S.paddedSystem_hasSolution_iff).mpr h.2,
      fun h => ⟨hw, (S.paddedSystem_hasSolution_iff).mp h⟩⟩
  · simp only [MaskedSys.Feasible, hw, false_and, compileList, ↓reduceIte]
    exact iff_false_intro cvpNoInput_not_mem |>.symm

end IdealCVP
