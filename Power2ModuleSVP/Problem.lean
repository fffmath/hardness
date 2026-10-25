import Power2ModuleSVP.Coset.Coefficient

/-!
# Problem

Unit coefficient-sup-norm coset and rank-two module languages.
Generators are stored as columns; malformed arrays are rejected.

Paper: `paper/power2svp.pdf`, Sections 1.1–2 (decision languages and coefficient embeddings).
-/
namespace Power2ModuleSVP

/-- Stored degree, coset generator, and translation coefficient arrays. -/
abbrev CosetInput := IdealCVP.RingArgs
/-- Stored degree and two rank-two module generators. -/
abbrev SVPInput := IdealCVP.PairRingArgs
/-- Binary encoding of the degree and the two coset coefficient arrays. -/
def encCoset : CosetInput ↪ List Bool := IdealCVP.encRingArgs
/-- Binary encoding of the degree and the two stored module generators. -/
def encSVP : SVPInput ↪ List Bool := IdealCVP.encPairRingArgs

/-- The principal coset contains a vector in the coefficient unit cube. -/
def CosetYes {d : ℕ} (g h : Coeff d) : Prop :=
  ∃ u : Coeff d, Cube (h + IdealCVP.Cyclotomic.mul g u)

/-- The module vector obtained from the two stored generators and ring multipliers. -/
def moduleVector {d : ℕ} (a b : Coeff d × Coeff d)
    (u v : Coeff d) : Coeff d × Coeff d :=
  (IdealCVP.Cyclotomic.mul a.1 u + IdealCVP.Cyclotomic.mul b.1 v,
   IdealCVP.Cyclotomic.mul a.2 u + IdealCVP.Cyclotomic.mul b.2 v)

/-- The generated module contains a nonzero vector in the coefficient unit cube. -/
def ModuleYes {d : ℕ} (a b : Coeff d × Coeff d) : Prop :=
  ∃ u v : Coeff d, moduleVector a b u v ≠ 0 ∧
    Cube (moduleVector a b u v).1 ∧ Cube (moduleVector a b u v).2

/-- A dyadic input with exact-length arrays and a nonzero even coset generator. -/
def CosetInput.WellFormed (x : CosetInput) : Prop :=
  Dyadic x.1 ∧ x.2.1.length = x.1 ∧ x.2.2.length = x.1 ∧
    IdealCVP.ofList (d := x.1) x.2.1 ≠ 0 ∧
    EvenCoeffs (IdealCVP.ofList (d := x.1) x.2.1)

/-- A dyadic input with exact-length arrays and independent module generators. -/
def SVPInput.WellFormed (x : SVPInput) : Prop :=
  Dyadic x.1 ∧ x.2.1.1.length = x.1 ∧ x.2.1.2.length = x.1 ∧
    x.2.2.1.length = x.1 ∧ x.2.2.2.length = x.1 ∧
    IdealCVP.listIndependent x.1 x.2.1 x.2.2 = true

/-- The encoded unit-cube principal-coset decision language. -/
def CosetLang : Set CosetInput := {x | CosetInput.WellFormed x ∧
  CosetYes (IdealCVP.ofList (d := x.1) x.2.1) (IdealCVP.ofList (d := x.1) x.2.2)}
/-- The encoded unit-threshold rank-two module shortest-vector language. -/
def ModuleSVPLang : Set SVPInput := {x | SVPInput.WellFormed x ∧
  ModuleYes
    (IdealCVP.ofList (d := x.1) x.2.1.1, IdealCVP.ofList (d := x.1) x.2.1.2)
    (IdealCVP.ofList (d := x.1) x.2.2.1, IdealCVP.ofList (d := x.1) x.2.2.2)}
/-- Binary strings encoding members of the principal-coset language. -/
def CosetBits : Set (List Bool) := encCoset '' CosetLang
/-- Binary strings encoding members of the module shortest-vector language. -/
def ModuleSVPBits : Set (List Bool) := encSVP '' ModuleSVPLang

theorem encCoset_mem_iff (x : CosetInput) : encCoset x ∈ CosetBits ↔ x ∈ CosetLang := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact encCoset.injective he ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

theorem encSVP_mem_iff (x : SVPInput) : encSVP x ∈ ModuleSVPBits ↔ x ∈ ModuleSVPLang := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact encSVP.injective he ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

/-- The coefficient maximum norm attains its least nonzero value at `r`. -/
def FirstMinimum {d : ℕ} (a b : Coeff d × Coeff d) (r : ℕ) : Prop :=
  (∃ u v, moduleVector a b u v ≠ 0 ∧ pairSup (moduleVector a b u v) = r) ∧
  ∀ u v, moduleVector a b u v ≠ 0 → r ≤ pairSup (moduleVector a b u v)

end Power2ModuleSVP
