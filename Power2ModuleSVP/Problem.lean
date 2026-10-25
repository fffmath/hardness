import Power2ModuleSVP.Coset.Coefficient

/-!
# Problem

Unit coefficient-sup-norm coset and rank-two module languages.
Generators are stored as columns; malformed arrays are rejected.

Paper: `paper/power2svp.pdf`, Sections 1.1–2 (decision languages and coefficient embeddings).
-/
namespace Power2ModuleSVP

abbrev CosetInput := IdealCVP.RingArgs
abbrev SVPInput := IdealCVP.PairRingArgs
/-- Binary encoding of the degree and the two coset coefficient arrays. -/
def encCoset : CosetInput ↪ List Bool := IdealCVP.encRingArgs
/-- Binary encoding of the degree and the two stored module generators. -/
def encSVP : SVPInput ↪ List Bool := IdealCVP.encPairRingArgs

def CosetYes {d : ℕ} (g h : Coeff d) : Prop :=
  ∃ u : Coeff d, Cube (h + IdealCVP.Cyclotomic.mul g u)

def moduleVector {d : ℕ} (a b : Coeff d × Coeff d)
    (u v : Coeff d) : Coeff d × Coeff d :=
  (IdealCVP.Cyclotomic.mul a.1 u + IdealCVP.Cyclotomic.mul b.1 v,
   IdealCVP.Cyclotomic.mul a.2 u + IdealCVP.Cyclotomic.mul b.2 v)

def ModuleYes {d : ℕ} (a b : Coeff d × Coeff d) : Prop :=
  ∃ u v : Coeff d, moduleVector a b u v ≠ 0 ∧
    Cube (moduleVector a b u v).1 ∧ Cube (moduleVector a b u v).2

def CosetInput.WellFormed (x : CosetInput) : Prop :=
  Dyadic x.1 ∧ x.2.1.length = x.1 ∧ x.2.2.length = x.1 ∧
    IdealCVP.ofList (d := x.1) x.2.1 ≠ 0 ∧
    EvenCoeffs (IdealCVP.ofList (d := x.1) x.2.1)

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
def CosetBits : Set (List Bool) := encCoset '' CosetLang
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

def FirstMinimum {d : ℕ} (a b : Coeff d × Coeff d) (r : ℕ) : Prop :=
  (∃ u v, moduleVector a b u v ≠ 0 ∧ pairSup (moduleVector a b u v) = r) ∧
  ∀ u v, moduleVector a b u v ≠ 0 → r ≤ pairSup (moduleVector a b u v)

end Power2ModuleSVP
