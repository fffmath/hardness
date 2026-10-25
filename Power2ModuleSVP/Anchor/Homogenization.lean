import Power2ModuleSVP.Coset.ParityBlock
import Power2ModuleSVP.Anchor.Family
import Power2ModuleSVP.Coset.Packing

/-!
# Homogenization

Semantic rank-two homogenization (`prop:conditional-module`).

Paper: `paper/power2svp.pdf`, Section 3.3 (Proposition 1, homogenization).
-/
namespace Power2ModuleSVP
open IdealCVP.Cyclotomic

theorem SignedMonomial.mul_surjective {d : ℕ} (hd : Dyadic d) {v : Coeff d}
    (hv : SignedMonomial v) : Function.Surjective (mul v) := by
  let : Fact (∃ k, d = 2^k) := ⟨hd⟩
  have hu : IsUnit (toQuot v) := by
    obtain ⟨j, rfl | rfl⟩ := hv
    · rw [IdealCVP.ModuleSIVP.toQuot_monomial]
      exact (IdealCVP.ModuleSIVP.root_isUnit (d := d)).pow _
    · have hn : toQuot (-monomial j 1) = -toQuot (monomial j 1) := by
        simp [toQuot, Finset.sum_neg_distrib]
      rw [hn, IdealCVP.ModuleSIVP.toQuot_monomial]
      exact ((IdealCVP.ModuleSIVP.root_isUnit (d := d)).pow _).neg
  obtain ⟨a, ha⟩ := hu
  intro u
  obtain ⟨w, hw⟩ := (toQuot_bijective hd.pos).surjective (↑a⁻¹ * toQuot u)
  refine ⟨w, (toQuot_bijective hd.pos).injective ?_⟩
  rw [toQuot_mul hd.pos, hw, ← ha, ← _root_.mul_assoc]
  simp

/-- A rigid sign anchor turns a unit-cube coset point into precisely a
nonzero unit-cube vector in the triangular module. -/
theorem homogenization {d : ℕ} (hd : Dyadic d)
    (g h J : Coeff d) (_hg : g ≠ 0) (he : EvenCoeffs g)
    (hJs : Signs J) (hJ : Rigid J) :
    CosetYes g h ↔ ModuleYes (g,0) (h,J) := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, coeffOne hd.pos, ?_, ?_, ?_⟩
    · simpa [moduleVector] using (show (mul g u + h, J) ≠ 0 from by
        intro hz
        exact hJs.ne_zero hd.pos (congrArg Prod.snd hz))
    · simpa [moduleVector, add_comm] using hu
    · simpa [moduleVector] using hJs.cube
  · rintro ⟨u, v, hn, h1, h2⟩
    simp only [moduleVector, coeff_mul_zero_left, zero_add] at hn h1 h2
    rcases hJ v h2 with rfl | hv
    · have hz := even_cube_eq_zero (even_mul_left he u) (by simpa using h1)
      simp [hz] at hn
    · obtain ⟨u', hu'⟩ := hv.mul_surjective hd u
      refine ⟨u', (hv.cube_mul_iff _).mp ?_⟩
      have hid : mul v (h + mul g u') = mul g u + mul h v := by
        rw [mul_add, IdealCVP.Cyclotomic.mul_comm v h, IdealCVP.Cyclotomic.mul_comm v (mul g u'),
          coeff_mul_assoc hd.pos, IdealCVP.Cyclotomic.mul_comm u' v, hu']
        exact add_comm _ _
      rwa [hid]

/-- A nonzero integral coefficient vector has coefficient maximum at least one. -/
theorem one_le_pairSup {d : ℕ} {z : Coeff d × Coeff d} (hz : z ≠ 0) :
    1 ≤ pairSup z := by
  by_contra! hn
  have h0 : pairSup z = 0 := by omega
  apply hz
  apply Prod.ext <;> funext i
  · have hb : (z.1 i).natAbs ≤ pairSup z :=
      (Finset.le_sup (f := fun i => (z.1 i).natAbs) (Finset.mem_univ i)).trans
        (Nat.le_max_left _ _)
    have : (z.1 i).natAbs = 0 := by omega
    simpa using this
  · have hb : (z.2 i).natAbs ≤ pairSup z :=
      (Finset.le_sup (f := fun i => (z.2 i).natAbs) (Finset.mem_univ i)).trans
        (Nat.le_max_right _ _)
    have : (z.2 i).natAbs = 0 := by omega
    simpa using this

theorem pairSup_le_one_iff {d : ℕ} (z : Coeff d × Coeff d) :
    pairSup z ≤ 1 ↔ Cube z.1 ∧ Cube z.2 := by
  simp only [pairSup, max_le_iff, ← cube_iff_coeffSup_le]

/-- Attained minimum one on YES; the integral gap is at least two on NO. -/
theorem homogenization_minimum {d : ℕ} (hd : Dyadic d)
    (g h J : Coeff d) (hg : g ≠ 0) (he : EvenCoeffs g)
    (hJs : Signs J) (hJ : Rigid J) :
    (CosetYes g h → FirstMinimum (g,0) (h,J) 1) ∧
    (¬CosetYes g h → ∀ u v, moduleVector (g,0) (h,J) u v ≠ 0 →
      2 ≤ pairSup (moduleVector (g,0) (h,J) u v)) := by
  have hc := homogenization hd g h J hg he hJs hJ
  constructor
  · intro hy
    obtain ⟨u,v,hn,h1,h2⟩ := hc.mp hy
    refine ⟨⟨u,v,hn, Nat.le_antisymm ((pairSup_le_one_iff _).mpr ⟨h1,h2⟩)
      (one_le_pairSup hn)⟩, fun _ _ hn => one_le_pairSup hn⟩
  · intro hn u v hz
    by_contra! hb
    have hcube := (pairSup_le_one_iff (moduleVector (g,0) (h,J) u v)).mp (by omega)
    exact hn (hc.mpr ⟨u,v,hz,hcube⟩)

/-- The executable column convention for the triangular basis. -/
def triangularInput (x : CosetInput) (J : List ℤ) : SVPInput :=
  (x.1, ((x.2.1, List.replicate x.1 0), (x.2.2,J)))

theorem ofList_replicate_zero (d : ℕ) :
    IdealCVP.ofList (d := d) (List.replicate d (0 : ℤ)) = 0 := by
  ext i
  simp [IdealCVP.ofList, List.getD_eq_getElem?_getD, i.isLt]

/-- Nonsingularity is proved in the existing quotient domain. -/
theorem triangular_independent {d : ℕ} (hd : Dyadic d)
    (g h J : Coeff d) (hg : g ≠ 0) (hJ : J ≠ 0) :
    @IdealCVP.ModuleSIVP.Independent d ⟨hd⟩ (toQuot g, 0) (toQuot h, toQuot J) := by
  let : Fact (∃ k, d = 2^k) := ⟨hd⟩
  rw [IdealCVP.ModuleSIVP.independent_iff]
  simp only [zero_mul, sub_zero]
  apply mul_ne_zero
  · simpa only [← quotEquiv_apply hd.pos] using
      (map_ne_zero_iff (quotEquiv hd.pos) (quotEquiv hd.pos).injective).mpr hg
  · simpa only [← quotEquiv_apply hd.pos] using
      (map_ne_zero_iff (quotEquiv hd.pos) (quotEquiv hd.pos).injective).mpr hJ

theorem triangularInput_wellFormed (x : CosetInput) (hx : x.WellFormed)
    (J : List ℤ) (hlen : J.length = x.1)
    (hJs : Signs (IdealCVP.ofList (d := x.1) J)) :
    (triangularInput x J).WellFormed := by
  let : Fact (∃ k, x.1 = 2^k) := ⟨hx.1⟩
  refine ⟨hx.1, hx.2.1, by simp [triangularInput], hx.2.2.1, hlen, ?_⟩
  change IdealCVP.listIndependent x.1 _ _ = true
  apply (IdealCVP.listIndependent_iff _ _).mpr
  simpa [triangularInput, IdealCVP.listRingPair, ofList_replicate_zero] using
    triangular_independent hx.1 _ _ _ hx.2.2.2.1 (hJs.ne_zero hx.1.pos)

/-- Language-level homogenization, including shape and nonsingularity. -/
theorem triangularInput_correct (x : CosetInput) (hx : x.WellFormed)
    (J : List ℤ) (hlen : J.length = x.1)
    (hJs : Signs (IdealCVP.ofList (d := x.1) J))
    (hJ : Rigid (IdealCVP.ofList (d := x.1) J)) :
    x ∈ CosetLang ↔ triangularInput x J ∈ ModuleSVPLang := by
  have hw := triangularInput_wellFormed x hx J hlen hJs
  change (_ ∧ _) ↔ (_ ∧ _)
  simp only [hx, hw, true_and]
  simpa only [triangularInput, ofList_replicate_zero] using
    homogenization hx.1 _ _ _ hx.2.2.2.1 hx.2.2.2.2 hJs hJ

/-- The existing basis construction supplies a free rank-two module. -/
theorem triangular_free {d : ℕ} [Fact (∃ k, d = 2 ^ k)]
    (g h J : Coeff d) (hg : g ≠ 0) (hJs : Signs J) :
    Nonempty (Module.Basis (Fin 2) (Rd d)
      (IdealCVP.ModuleSIVP.basisSpan (toQuot g,0) (toQuot h,toQuot J))) := by
  have hd : Dyadic d := (show ∃ k, d = 2^k from Fact.out)
  exact ⟨IdealCVP.ModuleSIVP.generalBasis _ _
    (triangular_independent hd g h J hg (hJs.ne_zero hd.pos))⟩

/-- The first-minimum and integral-gap conclusion for packed affine inputs. -/
theorem packed_module_minimum (hSep : NormSeparationHypothesis)
    (q : AffineInput) (hq : q.WellFormed) (D : ℕ) (hDy : Dyadic D)
    (hD : 16 * q.1 ^ 3 ≤ D) (J : Coeff D) (hJs : Signs J) (hJ : Rigid J) :
    let g := IdealCVP.ofList (d := D) (packCoset D q).2.1
    let h := IdealCVP.ofList (d := D) (packCoset D q).2.2
    (AffineYes q → FirstMinimum (g,0) (h,J) 1) ∧
    (¬AffineYes q → ∀ u v, moduleVector (g,0) (h,J) u v ≠ 0 →
      2 ≤ pairSup (moduleVector (g,0) (h,J) u v)) := by
  have hw := packCoset_wellFormed q hq D hDy hD
  have hc0 := packCoset_correct hSep q hq D hDy hD
  change AffineYes q ↔ (packCoset D q).WellFormed ∧ CosetYes
    (IdealCVP.ofList (d := D) (packCoset D q).2.1)
    (IdealCVP.ofList (d := D) (packCoset D q).2.2) at hc0
  have hc : AffineYes q ↔ CosetYes
      (IdealCVP.ofList (d := D) (packCoset D q).2.1)
      (IdealCVP.ofList (d := D) (packCoset D q).2.2) :=
    ⟨fun h => (hc0.mp h).2,fun h => hc0.mpr ⟨hw,h⟩⟩
  have hg : IdealCVP.ofList (d := D) (packCoset D q).2.1 ≠ 0 := hw.2.2.2.1
  have he : EvenCoeffs (IdealCVP.ofList (d := D) (packCoset D q).2.1) := hw.2.2.2.2
  have hm := homogenization_minimum hDy
    (IdealCVP.ofList (d := D) (packCoset D q).2.1)
    (IdealCVP.ofList (d := D) (packCoset D q).2.2) J hg he hJs hJ
  exact ⟨fun h => hm.1 (hc.mp h), fun h => hm.2 (fun h' => h (hc.mpr h'))⟩

/-- Total semantic composition. The coset is constructed at the final module
ring degree from the start. -/
def threeSATToModule (k0 : ℕ) (J : ℕ → List ℤ)
    (f : Cslib.Logic.PL.CNF ℕ) : SVPInput :=
  let q := threeSATToAffine f
  let D := modulePackingDegree k0 q.1
  triangularInput (packCoset D q) (J D)

/-- 3SAT-to-module correctness given a rigid sign anchor at the chosen degree.
No runtime claim for the composite map is made here. -/
theorem threeSAT_module_correct (hSep : NormSeparationHypothesis)
    (f : Cslib.Logic.PL.CNF ℕ) (k0 : ℕ) (J : ℕ → List ℤ)
    (hlen : (J (modulePackingDegree k0 (threeSATToAffine f).1)).length =
      modulePackingDegree k0 (threeSATToAffine f).1)
    (hJs : Signs (IdealCVP.ofList (d := modulePackingDegree k0 (threeSATToAffine f).1)
      (J (modulePackingDegree k0 (threeSATToAffine f).1))))
    (hJ : Rigid (IdealCVP.ofList (d := modulePackingDegree k0 (threeSATToAffine f).1)
      (J (modulePackingDegree k0 (threeSATToAffine f).1)))) :
    f ∈ Cslib.Complexity.ThreeSAT ↔ threeSATToModule k0 J f ∈ ModuleSVPLang := by
  let q := threeSATToAffine f
  let D := modulePackingDegree k0 q.1
  have hq := threeSATToAffine_wellFormed f
  have hdy := modulePackingDegree_dyadic k0 q.1
  have hlarge := modulePackingDegree_large k0 q.1
  exact (threeSATToAffine_correct f).trans
    ((packCoset_correct hSep q hq D hdy hlarge).trans
      (triangularInput_correct (packCoset D q)
        (packCoset_wellFormed q hq D hdy hlarge) (J D) hlen hJs hJ))

/-- The precise uniform anchor boundary suffices for a semantic SAT reduction.
The included native-machine certificate concerns the anchor family only. -/
theorem exists_threeSAT_module_reduction (hSep : NormSeparationHypothesis)
    (hAnchor : RigidAnchorFamilyHypothesis) :
    ∃ (k0 : ℕ) (J : ℕ → List ℤ),
      Turing.MultiTapeTM.ComputableTidilyInPolyTime J
        Turing.MultiTapeTM.encUnary
        (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encIntBin) ∧
      ∀ f : Cslib.Logic.PL.CNF ℕ,
        f ∈ Cslib.Complexity.ThreeSAT ↔ threeSATToModule k0 J f ∈ ModuleSVPLang := by
  obtain ⟨k0,J,htime,hfamily⟩ := hAnchor.exists_family
  refine ⟨k0,J,htime,fun f => ?_⟩
  obtain ⟨hlen,hJs,hJ⟩ := hfamily _ (modulePackingDegree_dyadic _ _)
    (modulePackingDegree_cutoff _ _)
  exact threeSAT_module_correct hSep f k0 J hlen hJs hJ

/-- The attained first minimum is one exactly for YES cosets. -/
theorem homogenization_firstMinimum_iff {d : ℕ} (hd : Dyadic d)
    (g h J : Coeff d) (hg : g ≠ 0) (he : EvenCoeffs g)
    (hJs : Signs J) (hJ : Rigid J) :
    CosetYes g h ↔ FirstMinimum (g,0) (h,J) 1 := by
  constructor
  · exact (homogenization_minimum hd g h J hg he hJs hJ).1
  · rintro ⟨⟨u,v,hn,hnorm⟩,_⟩
    have hcube := (pairSup_le_one_iff _).mp (le_of_eq hnorm)
    exact (homogenization hd g h J hg he hJs hJ).mpr ⟨u,v,hn,hcube⟩

/-- Every semantic module output has exact array lengths and nonsingular
columns, on both satisfiable and unsatisfiable formulas. -/
theorem threeSATToModule_wellFormed (f : Cslib.Logic.PL.CNF ℕ)
    (k0 : ℕ) (J : ℕ → List ℤ)
    (hlen : (J (modulePackingDegree k0 (threeSATToAffine f).1)).length =
      modulePackingDegree k0 (threeSATToAffine f).1)
    (hJs : Signs (IdealCVP.ofList (d := modulePackingDegree k0 (threeSATToAffine f).1)
      (J (modulePackingDegree k0 (threeSATToAffine f).1)))) :
    (threeSATToModule k0 J f).WellFormed :=
  triangularInput_wellFormed _
    (packCoset_wellFormed _ (threeSATToAffine_wellFormed f) _
      (modulePackingDegree_dyadic _ _) (modulePackingDegree_large _ _)) _ hlen hJs

end Power2ModuleSVP
