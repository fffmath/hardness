import Power2ModuleSVP.ReductionMapAux

/-! Polynomial-time composition for the total coset and module reductions.
In particular the anchor is run on the computed unary final ring degree. -/
namespace Power2ModuleSVP
open Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[fun_prop] theorem threeSATToAffine_polytime :
    ComputableTidilyInPolyTime threeSATToAffine encCNF encAffine := by
  have he : sourceMap = threeSATToAffine := funext sourceMap_eq_threeSATToAffine
  rw [← he]
  exact sourceMap_polytime

@[fun_prop] theorem cosetReduction_polytime :
    ComputableTidilyInPolyTime cosetReduction encCNF encCoset := by
  have hL : ComputableTidilyInPolyTime (fun f => (sourceMap f).1)
      encCNF encUnary := (fst _ _).comp sourceMap_polytime
  exact packCoset_polytime.comp ((packingDegree_polytime.comp hL).prod sourceMap_polytime)

/-- The degree supplied to the anchor has a native unary-output certificate. -/
@[fun_prop] theorem moduleReductionDegree_polytime (k0 : ℕ) :
    ComputableTidilyInPolyTime (moduleReductionDegree k0) encCNF encUnary :=
  (modulePackingDegree_polytime k0).comp ((fst _ _).comp sourceMap_polytime)

@[fun_prop] theorem moduleReduction_polytime (k0 : ℕ) (J : ℕ → List ℤ)
    (hJ : ComputableTidilyInPolyTime J encUnary (encList encIntBin)) :
    ComputableTidilyInPolyTime (moduleReduction k0 J) encCNF encSVP := by
  have hd := moduleReductionDegree_polytime k0
  have hc := packCoset_polytime.comp (hd.prod sourceMap_polytime)
  exact triangularInput_polytime.comp (hc.prod (hJ.comp hd))

@[fun_prop] theorem threeSATToModule_polytime (k0 : ℕ) (J : ℕ → List ℤ)
    (hJ : ComputableTidilyInPolyTime J encUnary (encList encIntBin)) :
    ComputableTidilyInPolyTime (threeSATToModule k0 J) encCNF encSVP := by
  have he : moduleReduction k0 J = threeSATToModule k0 J :=
    funext (moduleReduction_eq k0 J)
  rw [← he]
  exact moduleReduction_polytime k0 J hJ

theorem threeSAT_polyTimeReducible_coset :
    PolyTimeReducible encCNF encCoset ThreeSAT CosetLang :=
  ⟨cosetReduction, cosetReduction_polytime, cosetReduction_correct⟩

theorem threeSAT_polyTimeReducible_moduleSVP_of (hJ : RigidAnchorFamilyHypothesis) :
    PolyTimeReducible encCNF encSVP ThreeSAT ModuleSVPLang := by
  obtain ⟨k0, J, htime, hfamily⟩ := hJ.exists_family
  exact ⟨moduleReduction k0 J, moduleReduction_polytime k0 J htime,
    moduleReduction_correct k0 J hfamily⟩

end Power2ModuleSVP
