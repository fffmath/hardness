import Rank2ModuleSVP.PrimeCyclotomic
import IdealCVP.Complexity.GeneralModule
import IdealCVP.Complexity.X3CList
import IdealCVP.Complexity.SatToX3C
import IdealCVP.Sidon

/-! The exact rank-two module-SVP problem in power-basis list encoding.
The encoding and the complexitylib ambient types are reused from IdealCVP. -/
namespace Rank2ModuleSVP
open scoped BigOperators
noncomputable section

/-- `(q, (m₁₁,m₁₂), (m₂₁,m₂₂), S)`, with signed binary coefficients. -/
abbrev SVPInput := ℕ × ((List ℤ × List ℤ) × ((List ℤ × List ℤ) × ℤ))

/-- Unary dimension, binary integers, and self-delimiting lists and pairs.
This is an actual embedding, so malformed bit strings can be rejected. -/
def encSVP : SVPInput ↪ List Bool := IdealCVP.encModuleSIVP

def powerCoeffs {q : ℕ} [NeZero q] (l : List ℤ) : Coeff ℤ q :=
  fun a => if a.val < q-1 then l.getD a.val 0 else 0

def powerElement {q : ℕ} [NeZero q] (l : List ℤ) : IntegerRing q := classOf (powerCoeffs l)

def powerPair {q : ℕ} [NeZero q] (p : List ℤ × List ℤ) : IntegerRing q × IntegerRing q :=
  (powerElement p.1, powerElement p.2)

/-- The two module generators are columns of the determinant. -/
def determinant {q : ℕ} [NeZero q] (u v : IntegerRing q × IntegerRing q) : IntegerRing q :=
  u.1*v.2 - u.2*v.1

def moduleVector {q : ℕ} [NeZero q] (m₁ m₂ : IntegerRing q × IntegerRing q)
    (z w : IntegerRing q) : IntegerRing q × IntegerRing q :=
  (z*m₁.1 + w*m₂.1, z*m₁.2 + w*m₂.2)

/-- Exact decision-SVP uses a nonzero module vector and an integer squared threshold. -/
def SVPYes {q : ℕ} [NeZero q] (m₁ m₂ : IntegerRing q × IntegerRing q) (S : ℤ) : Prop :=
  ∃ z w : IntegerRing q, moduleVector m₁ m₂ z w ≠ 0 ∧
    pairNormSq (moduleVector m₁ m₂ z w) ≤ S

namespace SVPInput
abbrev q (x : SVPInput) := x.1
abbrev m₁ (x : SVPInput) := x.2.1
abbrev m₂ (x : SVPInput) := x.2.2.1
abbrev threshold (x : SVPInput) := x.2.2.2

/-- Primality supplies the finite-index instance needed to interpret coefficients. -/
def WellFormed (x : SVPInput) : Prop :=
  ∃ hp : x.q.Prime,
    letI : NeZero x.q := ⟨hp.ne_zero⟩
    x.q ≠ 2 ∧
    x.m₁.1.length = x.q-1 ∧ x.m₁.2.length = x.q-1 ∧
    x.m₂.1.length = x.q-1 ∧ x.m₂.2.length = x.q-1 ∧
    determinant (powerPair (q := x.q) x.m₁) (powerPair (q := x.q) x.m₂) ≠ 0 ∧ 0 ≤ x.threshold

theorem prime {x : SVPInput} (h : x.WellFormed) : x.q.Prime := h.choose

end SVPInput

/-- Malformed inputs are excluded. NP membership is a subsequent obligation. -/
def ModuleSVPLang : Set SVPInput := {x | ∃ h : x.WellFormed,
  letI : NeZero x.q := ⟨(SVPInput.prime h).ne_zero⟩
  SVPYes (powerPair (q := x.q) x.m₁) (powerPair (q := x.q) x.m₂) x.threshold}

/-- The same language as a language of bit strings. -/
def ModuleSVPBits : Set (List Bool) := encSVP '' ModuleSVPLang

theorem encSVP_mem_iff (x : SVPInput) : encSVP x ∈ ModuleSVPBits ↔ x ∈ ModuleSVPLang := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact encSVP.injective he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end
end Rank2ModuleSVP
