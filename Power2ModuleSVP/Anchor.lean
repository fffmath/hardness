import Power2ModuleSVP.Problem

/-!
The uniform algorithmic hypothesis for the rigid anchors. Existence of a
separate sign vector at each degree would not supply the time certificate.
-/
namespace Power2ModuleSVP

/-- One uniform native multitape machine, with a fixed polynomial bound on
unary degree, produces rigid sign polynomials above a fixed dyadic cutoff.
This is the boundary specified in PLAN section 5; no anchor is asserted here. -/
structure RigidAnchorFamilyHypothesis : Prop where
  exists_family :
    ∃ (k0 : ℕ) (J : ℕ → List ℤ),
      Turing.MultiTapeTM.ComputableTidilyInPolyTime J
        Turing.MultiTapeTM.encUnary
        (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encIntBin) ∧
      ∀ d : ℕ, Dyadic d → 2^k0 ≤ d →
        (J d).length = d ∧
        Signs (IdealCVP.ofList (d := d) (J d)) ∧
        Rigid (IdealCVP.ofList (d := d) (J d))

end Power2ModuleSVP
