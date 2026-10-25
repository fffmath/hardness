import Complexity.Computability.Complexity.Problems.ExactThreeSAT
import Mathlib.Tactic

/-!
# The positive exactly-one source

Translate disjunctive exact-three SAT into positive exactly-one triples. Tagged variables handle
freshness and repeated input literals. Runtime/Source certifies the executable translation.

Paper: `paper/power2svp.pdf`, Section 4 (Proposition 2 and Lemmas 5–6).
-/
namespace Power2ModuleSVP
namespace BooleanSource
open scoped BigOperators
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

/-- Computable coefficient value of a Boolean bit. -/
def bit (b : Bool) : ℕ := if b then 1 else 0

@[simp] theorem bit_false : bit false = 0 := rfl
@[simp] theorem bit_true : bit true = 1 := rfl

theorem bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> decide

abbrev Triple (V : Type*) := V × V × V

/-- Exactly one of the three positive variables is set. -/
def One {V : Type*} (a : V → Bool) (c : Triple V) : Prop :=
  bit (a c.1) + bit (a c.2.1) + bit (a c.2.2) = 1

def Satisfies {V : Type*} (a : V → Bool) (cs : List (Triple V)) : Prop :=
  ∀ c ∈ cs, One a c

def Satisfiable {V : Type*} (cs : List (Triple V)) : Prop :=
  ∃ a : V → Bool, Satisfies a cs

def Distinct {V : Type*} (c : Triple V) : Prop :=
  c.1 ≠ c.2.1 ∧ c.1 ≠ c.2.2 ∧ c.2.1 ≠ c.2.2

/-- The three fixed clauses really force one true and three false variables. -/
theorem force_gadget (t a b d : Bool) :
    (bit t + bit a + bit b = 1 ∧ bit t + bit a + bit d = 1 ∧
      bit t + bit b + bit d = 1) ↔
    (t = true ∧ a = false ∧ b = false ∧ d = false) := by
  cases t <;> cases a <;> cases b <;> cases d <;> decide

theorem complement_gadget (x nx : Bool) :
    bit x + bit nx + bit false = 1 ↔ nx = !x := by
  cases x <;> cases nx <;> decide

/-- A selector can be set only when the literal is true. -/
theorem selector_gadget (s l : Bool) :
    (∃ z : Bool, bit s + bit (!l) + bit z = 1) ↔
    (s = true → l = true) := by
  cases s <;> cases l <;> decide

/-- A disjunctive formula with three literal occurrences per row. A literal's
Boolean tag is the value of its variable making it true, as in complexitylib. -/
abbrev ThreeFormula (v r : ℕ) := Fin r → Fin 3 → Fin v × Bool

def literalValue {v : ℕ} (a : Fin v → Bool) (l : Fin v × Bool) : Bool :=
  a l.1 == l.2

def ThreeSatisfiable {v r : ℕ} (f : ThreeFormula v r) : Prop :=
  ∃ a : Fin v → Bool, ∀ j, ∃ k, literalValue a (f j k) = true

/-- Four constant tags, two copies of each input, and six variables per row. -/
abbrev GadgetVar (v r : ℕ) := Fin 4 ⊕ ((Fin v × Bool) ⊕ (Fin r × Fin 3 × Bool))

def tVar {v r : ℕ} : GadgetVar v r := .inl 0
def aVar {v r : ℕ} : GadgetVar v r := .inl 1
def bVar {v r : ℕ} : GadgetVar v r := .inl 2
def dVar {v r : ℕ} : GadgetVar v r := .inl 3
def xVar {v r : ℕ} (i : Fin v) (b : Bool) : GadgetVar v r := .inr (.inl (i,b))
def sVar {v r : ℕ} (j : Fin r) (k : Fin 3) : GadgetVar v r := .inr (.inr (j,k,true))
def zVar {v r : ℕ} (j : Fin r) (k : Fin 3) : GadgetVar v r := .inr (.inr (j,k,false))

def forceClauses (v r : ℕ) : List (Triple (GadgetVar v r)) :=
  [(tVar,aVar,bVar), (tVar,aVar,dVar), (tVar,bVar,dVar)]

def complementClause {v r : ℕ} (i : Fin v) : Triple (GadgetVar v r) :=
  (xVar i true, xVar i false, aVar)

def choiceClause {v r : ℕ} (j : Fin r) : Triple (GadgetVar v r) :=
  (sVar j 0, sVar j 1, sVar j 2)

def implicationClause {v r : ℕ} (f : ThreeFormula v r) (j : Fin r) (k : Fin 3) :
    Triple (GadgetVar v r) :=
  (sVar j k, xVar (f j k).1 (!(f j k).2), zVar j k)

/-- Explicit finite output; each row uses one selector triple and three implications. -/
def positiveEncoding {v r : ℕ} (f : ThreeFormula v r) : List (Triple (GadgetVar v r)) :=
  forceClauses v r ++ List.ofFn (complementClause (r := r)) ++
    List.ofFn (choiceClause (v := v)) ++
    (List.ofFn fun j : Fin r => List.ofFn fun k : Fin 3 => implicationClause f j k).flatten

/-- A convenient interface equivalent to satisfaction of the explicit list. -/
theorem satisfies_encoding_iff {v r : ℕ} (f : ThreeFormula v r) (a : GadgetVar v r → Bool) :
    Satisfies a (positiveEncoding f) ↔
      (One a (tVar,aVar,bVar) ∧ One a (tVar,aVar,dVar) ∧ One a (tVar,bVar,dVar)) ∧
      (∀ i, One a (complementClause i)) ∧
      (∀ j, One a (choiceClause j)) ∧
      (∀ j k, One a (implicationClause f j k)) := by
  simp only [Satisfies, positiveEncoding, List.mem_append, List.mem_ofFn,
    List.mem_flatten, forceClauses, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · intro h
    refine ⟨⟨h _ (Or.inl (Or.inl (Or.inl (Or.inl rfl)))),
      h _ (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl))))),
      h _ (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr rfl)))))⟩,
      fun i => h _ (Or.inl (Or.inl (Or.inr ⟨i,rfl⟩))),
      fun j => h _ (Or.inl (Or.inr ⟨j,rfl⟩)), fun j k => ?_⟩
    exact h _ (Or.inr ⟨_, ⟨j,rfl⟩, List.mem_ofFn.mpr ⟨k,rfl⟩⟩)
  · rintro ⟨⟨ht,ha,hb⟩, hx, hs, hz⟩ c (((hf | ⟨i,rfl⟩) | ⟨j,rfl⟩) | hi)
    · rcases hf with rfl | rfl | rfl
      · exact ht
      · exact ha
      · exact hb
    · exact hx i
    · exact hs j
    · obtain ⟨cs,⟨j,rfl⟩,hc⟩ := hi
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hc
      exact hz j k

/-- The gadget uses no repeated variables within any positive triple. -/
theorem positiveEncoding_distinct {v r : ℕ} (f : ThreeFormula v r) :
    ∀ c ∈ positiveEncoding f, Distinct c := by
  intro c hc
  simp only [positiveEncoding, List.mem_append, List.mem_ofFn,
    List.mem_flatten] at hc
  rcases hc with ((hc | hc) | hc) | hc
  · simp only [forceClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      norm_num [Distinct, tVar, aVar, bVar, dVar]
  · obtain ⟨i,rfl⟩ := hc
    simp [Distinct, complementClause, xVar, aVar]
  · obtain ⟨j,rfl⟩ := hc
    norm_num [Distinct, choiceClause, sVar]
  · obtain ⟨cs,⟨j,rfl⟩,hc⟩ := hc
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hc
    simp [Distinct, implicationClause, sVar, xVar, zVar]

theorem positiveEncoding_length {v r : ℕ} (f : ThreeFormula v r) :
    (positiveEncoding f).length = 3 + v + 4 * r := by
  simp [positiveEncoding, forceClauses, List.length_flatten, List.sum_ofFn,
    Finset.sum_const, mul_comm]
  omega

/-- Soundness: the positive gadget yields a satisfying assignment of the original rows. -/
theorem positiveEncoding_sound {v r : ℕ} (f : ThreeFormula v r)
    (h : Satisfiable (positiveEncoding f)) : ThreeSatisfiable f := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨hf, hx, hs, hz⟩ := (satisfies_encoding_iff f a).mp ha
  have hfixed := (force_gadget (a tVar) (a aVar) (a bVar) (a dVar)).mp hf
  have hcomp (i : Fin v) : a (xVar i false) = !(a (xVar i true)) := by
    apply (complement_gadget _ _).mp
    simpa [One, complementClause, hfixed.2.1] using hx i
  refine ⟨fun i => a (xVar i true), fun j => ?_⟩
  have hchoice := hs j
  have hex : ∃ k : Fin 3, a (sVar j k) = true := by
    by_contra hn
    have hh : ∀ k : Fin 3, a (sVar j k) = false := by
      intro k
      cases he : a (sVar j k) <;> simp_all
    simp [One, choiceClause, hh] at hchoice
  obtain ⟨k,hk⟩ := hex
  refine ⟨k, ?_⟩
  have hi := hz j k
  have hnot : a (xVar (f j k).1 (!(f j k).2)) = false := by
    have hbound := bit_le_one (a (zVar j k))
    simp only [One, implicationClause, hk, bit_true] at hi
    cases he : a (xVar (f j k).1 (!(f j k).2)) <;> simp_all <;> omega
  cases he : (f j k).2 <;> simp [literalValue, he, hcomp] at hnot ⊢ <;> simpa using hnot

/-- Completeness: choose one true occurrence in each disjunctive row. -/
theorem positiveEncoding_complete {v r : ℕ} (f : ThreeFormula v r)
    (h : ThreeSatisfiable f) : Satisfiable (positiveEncoding f) := by
  classical
  obtain ⟨a,ha⟩ := h
  choose chosen hc using ha
  let lit (j : Fin r) (k : Fin 3) := literalValue a (f j k)
  let sel (j : Fin r) (k : Fin 3) : Bool := decide (k = chosen j)
  let assignment : GadgetVar v r → Bool
    | .inl i => decide (i = 0)
    | .inr (.inl (i,b)) => a i == b
    | .inr (.inr (j,k,b)) => if b then sel j k else lit j k && !(sel j k)
  refine ⟨assignment, (satisfies_encoding_iff f assignment).mpr ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [One, assignment, tVar, aVar, bVar, dVar]
  · intro i
    cases hi : a i <;> simp [One, complementClause, assignment, xVar, aVar, hi]
  · intro j
    have hj := (chosen j).isLt
    change bit (sel j 0) + bit (sel j 1) + bit (sel j 2) = 1
    interval_cases he : (chosen j).val <;>
      simp [sel, Fin.ext_iff, he]
  · intro j k
    have hsel : sel j k = true → lit j k = true := by
      simp only [sel, decide_eq_true_eq]
      rintro rfl
      exact hc j
    have hneg : (a (f j k).1 == !(f j k).2) = !(lit j k) := by
      dsimp [lit, literalValue]
      cases a (f j k).1 <;> cases (f j k).2 <;> decide
    change bit (sel j k) + bit (a (f j k).1 == !(f j k).2) +
      bit (lit j k && !(sel j k)) = 1
    rw [hneg]
    cases hs : sel j k <;> cases hl : lit j k <;> simp_all


/-- Pure mathematical correctness of the positive exactly-one translation. -/
theorem positiveEncoding_correct {v r : ℕ} (f : ThreeFormula v r) :
    ThreeSatisfiable f ↔ Satisfiable (positiveEncoding f) :=
  ⟨positiveEncoding_complete f, positiveEncoding_sound f⟩

/-- The same three-occurrence formula in the established complexitylib CNF type. -/
def toCNF {v r : ℕ} (f : ThreeFormula v r) : Cslib.Logic.PL.CNF ℕ :=
  List.ofFn fun j : Fin r => List.ofFn fun k : Fin 3 => ((f j k).1.val, (f j k).2)

/-- The finite-variable semantic source agrees with the existing CNF semantics. -/
theorem toCNF_satisfiable_iff {v r : ℕ} (f : ThreeFormula v r) :
    (toCNF f).Satisfiable ↔ ThreeSatisfiable f := by
  classical
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨fun i => a i.val, fun j => ?_⟩
    have hj := (Cslib.Logic.PL.CNF.eval_eq_true_iff a _).mp ha _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
    obtain ⟨l,hl,he⟩ := (Cslib.Logic.PL.Clause.eval_eq_true_iff a _).mp hj
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hl
    exact ⟨k, by simpa [literalValue] using he⟩
  · rintro ⟨a,ha⟩
    let extension : ℕ → Bool := fun i => if h : i < v then a ⟨i,h⟩ else false
    refine ⟨extension, (Cslib.Logic.PL.CNF.eval_eq_true_iff extension _).mpr ?_⟩
    intro c hc
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
    obtain ⟨k,hk⟩ := ha j
    apply (Cslib.Logic.PL.Clause.eval_eq_true_iff extension _).mpr
    refine ⟨_, List.mem_ofFn.mpr ⟨k,rfl⟩, ?_⟩
    simpa [extension, literalValue] using hk

/-- This is a formula of the NP-complete, disjunctive `ExactThreeSAT` source.
No new encoding or Cook–Levin argument is introduced. -/
theorem toCNF_mem_ExactThreeSAT_iff {v r : ℕ} (f : ThreeFormula v r) :
    toCNF f ∈ Cslib.Complexity.ExactThreeSAT ↔ ThreeSatisfiable f := by
  have hlen : ∀ c ∈ toCNF f, c.length = 3 := by
    intro c hc
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
    simp
  exact (and_iff_right hlen).trans (toCNF_satisfiable_iff f)

/-- A finite, explicit numbering of all fresh variables. -/
def variableCode {v r : ℕ} : GadgetVar v r → ℕ
  | .inl i => i.val
  | .inr (.inl (i,b)) => 4+2*i.val+(if b then 1 else 0)
  | .inr (.inr (j,k,b)) => 4+2*v+6*j.val+2*k.val+(if b then 1 else 0)

theorem variableCode_bound {v r : ℕ} (u : GadgetVar v r) :
    variableCode u < 4+2*v+6*r := by
  rcases u with i | (⟨i,b⟩ | ⟨j,k,b⟩)
  · simp only [variableCode]; have := i.isLt; omega
  · have := i.isLt
    cases b <;> simp only [variableCode, Bool.false_eq_true, ↓reduceIte] <;> omega
  · have := j.isLt; have := k.isLt
    cases b <;> simp only [variableCode, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The tags occupy disjoint intervals, so numbering cannot identify variables. -/
theorem variableCode_injective {v r : ℕ} :
    Function.Injective (variableCode : GadgetVar v r → ℕ) := by
  intro u w h
  rcases u with i | (⟨i,b⟩ | ⟨j,k,b⟩) <;>
    rcases w with ii | (⟨ii,bb⟩ | ⟨jj,kk,bb⟩)
  all_goals simp only [variableCode] at h
  all_goals try (have := i.isLt)
  all_goals try (have := ii.isLt)
  all_goals try (have := j.isLt)
  all_goals try (have := jj.isLt)
  all_goals try (have := k.isLt)
  all_goals try (have := kk.isLt)
  all_goals try (cases b)
  all_goals try (cases bb)
  all_goals try simp only [Bool.false_eq_true, ↓reduceIte] at h
  all_goals try simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, Fin.ext_iff]
  all_goals try omega
  all_goals repeat' apply And.intro
  all_goals first | trivial | omega

/-- Computable finite-index version of the numbering. -/
def variableFin {v r : ℕ} (u : GadgetVar v r) : Fin (4+2*v+6*r) :=
  ⟨variableCode u, variableCode_bound u⟩

theorem variableFin_injective {v r : ℕ} :
    Function.Injective (variableFin : GadgetVar v r → Fin (4+2*v+6*r)) := by
  intro u w h
  exact variableCode_injective (congrArg Fin.val h)

end BooleanSource
end Power2ModuleSVP
