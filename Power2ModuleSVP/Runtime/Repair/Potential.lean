import Power2ModuleSVP.Runtime.Repair.Probability

/-!
# Potential

Exact polynomial-time evaluation of the repair potential on all inputs.

Paper: `paper/power2svp.pdf`, Section 5 (Theorems 3–4 and deterministic anchor repair).
-/
namespace Power2ModuleSVP.AnchorRepairRuntime
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] List.getD AnchorRepair.screeningBound
  eventFraction candidateList fractionSum

/-- Fraction representation of the repair probability parameter. -/
def probabilityParameter (d : ℕ) : Fraction :=
  ((8 * AnchorRepair.screeningBound ^ 3 * Nat.log2 d : ℕ), (max 1 d : ℕ))

attribute [local irreducible] probabilityParameter

/-- The `probabilityParameter` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem probabilityParameter_polytime :
    ComputableTidilyInPolyTime probabilityParameter encUnary encFraction := by
  unfold probabilityParameter encFraction
  fun_prop

/-- The probability parameter fraction has positive denominator and the specified value. -/
theorem probabilityParameter_spec (d : ℕ) :
    0 < (probabilityParameter d).2 ∧
      fractionValue (probabilityParameter d) = AnchorRepair.flipProbability d := by
  refine ⟨by unfold probabilityParameter; positivity, ?_⟩
  by_cases hd : d = 0
  · simp [probabilityParameter, fractionValue, AnchorRepair.flipProbability, hd]
  · have he : max 1 d = d := max_eq_right (by omega)
    simp [probabilityParameter, fractionValue, AnchorRepair.flipProbability, he]

/-- Repair data together with the flag prefix already exposed. -/
abbrev PotentialInput := (ℕ × List ℤ) × List Bool
/-- Encoding of repair data and the exposed Boolean prefix. -/
abbrev encPotentialInput := encPair encRepairInput (encList encBool)

/-- Fraction representation of the penalty for the exposed flag prefix. -/
def penaltyFraction (d : ℕ) (pre : List Bool) : Fraction :=
  (((pre.count true : ℕ) : ℤ) * (probabilityParameter d).2 +
      (probabilityParameter d).1 * ((d - pre.length : ℕ) : ℤ),
    (probabilityParameter d).2 * ((AnchorRepair.flipBudget d : ℕ) + 1))

attribute [local irreducible] penaltyFraction

/-- The `penaltyFraction` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem penaltyFraction_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × List Bool => penaltyFraction a.1 a.2)
    (encPair encUnary (encList encBool)) encFraction := by
  unfold penaltyFraction encFraction
  fun_prop

/-- The penalty fraction has positive denominator and the semantic penalty value. -/
theorem penaltyFraction_spec (d : ℕ) (pre : List Bool) :
    0 < (penaltyFraction d pre).2 ∧
      fractionValue (penaltyFraction d pre) = AnchorRepair.penalty d pre := by
  obtain ⟨hp, hpv⟩ := probabilityParameter_spec d
  refine ⟨?_, ?_⟩
  · unfold penaltyFraction
    exact mul_pos hp (by positivity)
  rw [AnchorRepair.penalty, ← hpv]
  have hpq : ((probabilityParameter d).2 : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold penaltyFraction fractionValue
  push_cast
  field_simp

/-- Compute the repair potential with a fixed local enumeration budget. -/
def potentialFractionWith (n : ℕ) (a : PotentialInput) : Fraction :=
  fractionAdd (penaltyFraction a.1.1 a.2,
    fractionSum ((candidateList n a.1.1).map fun v =>
      eventFraction n
        ((a.1.1, (a.1.2, v)), (a.2, probabilityParameter a.1.1))))

/-- Compute the repair potential using the prescribed fixed budget. -/
def potentialFraction : PotentialInput → Fraction :=
  potentialFractionWith AnchorRepair.screeningBound

/-- The `potentialFractionWith` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem potentialFractionWith_polytime (n : ℕ) :
    ComputableTidilyInPolyTime (potentialFractionWith n) encPotentialInput encFraction := by
  have hd := (fst encRepairInput (encList encBool)).fst'
  have hs := (fst encRepairInput (encList encBool)).snd'
  have hp := snd encRepairInput (encList encBool)
  have hpen := penaltyFraction_polytime.comp (hd.prod hp)
  have hlist := (candidateList_polytime n).comp hd
  have hc : ComputableTidilyInPolyTime
      (fun a : PotentialInput × List ℤ =>
        eventFraction n
          ((a.1.1.1, (a.1.1.2, a.2)), (a.1.2, probabilityParameter a.1.1.1)))
      (encPair encPotentialInput (encList encIntBin)) encFraction := by
    have hinput := fst encPotentialInput (encList encIntBin)
    have hd' := hd.comp hinput
    have hs' := hs.comp hinput
    have hp' := hp.comp hinput
    have hv := snd encPotentialInput (encList encIntBin)
    exact ((eventFraction_polytime n).comp
      ((hd'.prod (hs'.prod hv)).prod
        (hp'.prod (probabilityParameter_polytime.comp hd')))).of_enc_eq
          (fun _ => congrArg encFraction (by rfl))
  have hm := mapWithInput (encIn := encPotentialInput)
    (encA := encList encIntBin) (encB := encFraction)
    (f := fun (a : PotentialInput) (v : List ℤ) =>
      eventFraction n
        ((a.1.1, (a.1.2, v)), (a.2, probabilityParameter a.1.1))) hlist hc
  exact (fractionAdd_polytime.comp
    (hpen.prod (fractionSum_polytime.comp hm))).of_enc_eq
      (fun a => congrArg encFraction (by unfold potentialFractionWith; rfl))

/-- The `potentialFraction` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem potentialFraction_polytime :
    ComputableTidilyInPolyTime potentialFraction encPotentialInput encFraction :=
  potentialFractionWith_polytime AnchorRepair.screeningBound

/-- The executable potential fraction has positive denominator and the semantic potential value. -/
theorem potentialFraction_spec (a : PotentialInput) :
    0 < (potentialFraction a).2 ∧
      fractionValue (potentialFraction a) = AnchorRepair.potential a.1.1 a.1.2 a.2 := by
  have he (v : List ℤ) (hv : v ∈ candidateList AnchorRepair.screeningBound a.1.1) :
      0 < (eventFraction AnchorRepair.screeningBound
        ((a.1.1, (a.1.2, v)), (a.2, probabilityParameter a.1.1))).2 ∧
      fractionValue (eventFraction AnchorRepair.screeningBound
        ((a.1.1, (a.1.2, v)), (a.2, probabilityParameter a.1.1))) =
        AnchorTests.eventProbability a.1.1 a.1.2 v a.2 (AnchorRepair.flipProbability a.1.1) := by
    rw [candidateList_eq] at hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have hs := (AnchorRepair.candidate_support_bounds w hw).2
    obtain ⟨hp, hpv⟩ := probabilityParameter_spec a.1.1
    simpa only [hpv] using eventFraction_spec AnchorRepair.screeningBound
      ((a.1.1, (a.1.2, IdealCVP.toList w)), (a.2, probabilityParameter a.1.1)) hp hs
  have hpos : ∀ f ∈ (candidateList AnchorRepair.screeningBound a.1.1).map
      (fun v => eventFraction AnchorRepair.screeningBound
        ((a.1.1, (a.1.2, v)), (a.2, probabilityParameter a.1.1))), 0 < f.2 := by
    intro f hf
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hf
    exact (he v hv).1
  obtain ⟨hs, hsv⟩ := fractionSum_spec _ hpos
  obtain ⟨hp, hpv⟩ := penaltyFraction_spec a.1.1 a.2
  obtain ⟨h, hv⟩ := fractionAdd_spec _ _ hp hs
  refine ⟨h, hv.trans ?_⟩
  rw [hpv, hsv]
  unfold AnchorRepair.potential
  congr 1
  rw [List.map_map]
  simp only [Function.comp_def]
  have hm : ((candidateList AnchorRepair.screeningBound a.1.1).map fun v =>
      fractionValue (eventFraction AnchorRepair.screeningBound
        ((a.1.1, (a.1.2, v)), (a.2, probabilityParameter a.1.1)))) =
      (candidateList AnchorRepair.screeningBound a.1.1).map fun v =>
        AnchorTests.eventProbability a.1.1 a.1.2 v a.2 (AnchorRepair.flipProbability a.1.1) := by
    apply List.map_congr_left
    intro v hv
    exact (he v hv).2
  rw [hm, candidateList_eq, List.map_map]
  rfl

/-- A single fixed polynomial bounds both fraction components throughout the
potential interface, including arbitrary coefficients and malformed prefixes. -/
theorem potentialFraction_bits_polyBounded :
    PolyBounded (fun a => (encPotentialInput a).length)
      (fun a => fractionBits (potentialFraction a)) :=
  fractionBits_polyBounded_of potentialFraction_polytime

end Power2ModuleSVP.AnchorRepairRuntime
