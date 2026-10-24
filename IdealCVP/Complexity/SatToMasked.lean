import IdealCVP.Complexity.Problem
import Complexity.Computability.Complexity.Problems.SubsetSum

/-! # Exact 3SAT to masked Boolean equations

Column labels separate literals from clause-local auxiliary variables. Densifying
these finite supports cannot merge repeated literal occurrences within a row.
-/
namespace IdealCVP
open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open scoped List

namespace SatToMasked

abbrev Column := ℕ × ℕ

def encColumn : Column ↪ List Bool := encPair encNat encNat

def denseRow (cs r : List Column) : List Bool := cs.map fun c => decide (c ∈ r)

def denseSystem (cs : List Column) (rs : List (List Column)) : MaskedSys :=
  (cs.length, rs.map (denseRow cs), List.replicate rs.length true,
    List.replicate cs.length true)

theorem denseRow_sum (cs r : List Column) (hcs : cs.Nodup) (hr : r.Nodup)
    (hsub : ∀ c ∈ r, c ∈ cs) (τ : Column → Bool) (ξ : Fin cs.length → Bool)
    (hξ : ∀ j, ξ j = τ cs[j.val]) :
    (∑ j : Fin cs.length, bit ((denseRow cs r).getD j.val false) * bit (ξ j)) =
      (r.map fun c => bit (τ c)).sum := by
  have hsum (f : Column → ℤ) :
      (∑ j : Fin cs.length, f cs[j.val]) = (cs.map f).sum := by
    rw [← List.sum_ofFn]
    change (List.ofFn (f ∘ cs.get)).sum = _
    rw [← List.map_ofFn, List.ofFn_get]
  calc
    _ = ∑ j : Fin cs.length, if cs[j.val] ∈ r then bit (τ cs[j.val]) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : cs[j.val] ∈ r <;>
        simp [denseRow, List.getD_eq_getElem?_getD, hξ j, bit, h]
    _ = (cs.map fun c => if c ∈ r then bit (τ c) else 0).sum := hsum (fun c => if c ∈ r then bit (τ c) else 0)
    _ = ∑ c ∈ cs.toFinset, if c ∈ r then bit (τ c) else 0 :=
      (List.sum_toFinset _ hcs).symm
    _ = ∑ c ∈ r.toFinset, bit (τ c) := by
      rw [← Finset.sum_filter]
      congr 1
      ext c
      simp only [Finset.mem_filter, List.mem_toFinset]
      exact ⟨fun h => h.2, fun h => ⟨hsub c h, h⟩⟩
    _ = _ := List.sum_toFinset _ hr

theorem denseSystem_wellFormed (cs : List Column) (rs : List (List Column)) :
    (denseSystem cs rs).WellFormed := by
  simp [MaskedSys.WellFormed, MaskedSys.cols, MaskedSys.rows, MaskedSys.rhs,
    MaskedSys.mask, denseSystem, denseRow]

/-- Finite supports and dense rows have exactly the same Boolean solutions. -/
theorem denseSystem_feasible_iff (cs : List Column) (rs : List (List Column))
    (hcs : cs.Nodup) (hrs : ∀ r ∈ rs, r.Nodup ∧ ∀ c ∈ r, c ∈ cs) :
    (denseSystem cs rs).Feasible ↔
      ∃ τ : Column → Bool, ∀ r ∈ rs, (r.map fun c => bit (τ c)).sum = 1 := by
  have hrow (i : Fin rs.length) :
      (rs.map (denseRow cs)).getD i.val [] = denseRow cs rs[i.val] := by
    simp [List.getD_eq_getElem?_getD]
  constructor
  · rintro ⟨_, ξ, _, heq⟩
    let v : Fin cs.length → Bool := ξ
    let τ : Column → Bool := fun c => (List.ofFn v).getD (cs.idxOf c) false
    have hv (j : Fin cs.length) : v j = τ cs[j.val] := by
      simp [τ, List.getD_eq_getElem?_getD, hcs.idxOf_getElem j.val j.isLt]
    refine ⟨τ, fun r hr => ?_⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hr
    have he := congrFun heq ⟨i.val, by simpa [MaskedSys.rows, denseSystem] using i.isLt⟩
    change (∑ j : Fin cs.length,
      bit (((rs.map (denseRow cs)).getD i.val []).getD j.val false) * bit (v j)) -
      bit ((List.replicate rs.length true).getD i.val false) = 0 at he
    rw [hrow i] at he
    have hb : (List.replicate rs.length true).getD i.val false = true := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, i.isLt]
    rw [hb] at he
    simp only [List.getElem_replicate, bit_true, sub_eq_zero] at he
    rw [denseRow_sum cs rs[i.val] hcs (hrs _ (List.getElem_mem i.isLt)).1
      (hrs _ (List.getElem_mem i.isLt)).2 τ v hv] at he
    simpa only [← hi, List.get_eq_getElem] using he
  · rintro ⟨τ, hτ⟩
    refine ⟨denseSystem_wellFormed cs rs, (fun j => τ cs[j.val]), ?_, ?_⟩
    · intro j _
      have hj : j.val < cs.length := j.isLt
      simp [MaskedSys.toSystem, MaskedSys.mask, denseSystem,
        List.getD_eq_getElem?_getD, List.getElem?_replicate, hj]
    · funext i
      have hi : i.val < rs.length := by simpa [MaskedSys.rows, denseSystem] using i.isLt
      change (∑ j : Fin cs.length,
        bit (((rs.map (denseRow cs)).getD i.val []).getD j.val false) * bit (τ cs[j.val])) -
        bit ((List.replicate rs.length true).getD i.val false) = 0
      rw [hrow ⟨i.val, hi⟩]
      have hb : (List.replicate rs.length true).getD i.val false = true := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hi]
      rw [hb]
      simp only [List.getElem_replicate, bit_true, sub_eq_zero]
      change (∑ j : Fin cs.length, bit ((denseRow cs rs[i.val]).getD j.val false) *
        bit (τ cs[j.val])) = 1
      rw [denseRow_sum cs rs[i.val] hcs (hrs _ (List.getElem_mem hi)).1
        (hrs _ (List.getElem_mem hi)).2 τ _ (fun _ => rfl)]
      exact hτ _ (List.getElem_mem hi)

/-- Schaefer's three equations, in literal truth values. -/
def Gadget (l₁ l₂ l₃ a b c e : Bool) : Prop :=
  bit (!l₁) + bit a + bit b = 1 ∧
  bit b + bit l₂ + bit c = 1 ∧
  bit c + bit e + bit (!l₃) = 1

/-- Exhaustive Boolean proof; it also checks the signs in the gadget. -/
theorem gadget_iff (l₁ l₂ l₃ : Bool) :
    (∃ a b c e, Gadget l₁ l₂ l₃ a b c e) ↔ (l₁ || l₂ || l₃) = true := by
  cases l₁ <;> cases l₂ <;> cases l₃ <;>
    simp [Gadget, Bool.exists_bool, bit]

/-- The positive/negative literal columns, four private columns per clause, and
one dummy column. Variable labels themselves remain binary data. -/
def columns (φ : CNF ℕ) : List Column :=
  [(0, 6)] ++ ((ThreeSAT.distinctVars φ) ×ˢ [0, 1]) ++
    ((List.range φ.length) ×ˢ [2, 3, 4, 5])

def literalColumn (l : Literal ℕ) : Column := (l.1, if l.2 then 0 else 1)
def negColumn (l : Literal ℕ) : Column := (l.1, if l.2 then 1 else 0)

def clauseRows (j : ℕ) (c : Clause ℕ) : List (List Column) :=
  [[negColumn (c.getD 0 (0, true)), (j, 2), (j, 3)],
   [(j, 3), literalColumn (c.getD 1 (0, true)), (j, 4)],
   [(j, 4), (j, 5), negColumn (c.getD 2 (0, true))]]

def supports (φ : CNF ℕ) : List (List Column) :=
  [[(0, 6)]] ++ ((ThreeSAT.distinctVars φ).map fun v => [(v, 0), (v, 1)]) ++
    ((List.range φ.length).flatMap fun j => clauseRows j (φ.getD j []))

def noSystem : MaskedSys := (1, [[false]], [true], [true])

/-- Malformed clauses map to a fixed NO system. The dummy equation makes both
sizes positive even for the empty CNF. -/
def reduce (φ : CNF ℕ) : MaskedSys :=
  if φ.all (fun c => c.length == 3) then denseSystem (columns φ) (supports φ)
  else noSystem

theorem nodup_columns (φ : CNF ℕ) : (columns φ).Nodup := by
  have hv := (ThreeSAT.nodup_distinctVars (φ := φ)).product
    (by decide : ([0, 1] : List ℕ).Nodup)
  have ha := (List.nodup_range (n := φ.length)).product
    (by decide : ([2, 3, 4, 5] : List ℕ).Nodup)
  simp only [columns, List.nodup_append]
  refine ⟨⟨by simp, hv, ?_⟩, ha, ?_⟩
  · rintro a ha ⟨v, t⟩ hb he
    simp only [List.mem_singleton] at ha
    simp only [List.mem_product, List.mem_cons, List.not_mem_nil, or_false] at hb
    have ht : 6 = t := by simpa only [ha] using congrArg Prod.snd he
    omega
  · rintro ⟨v, t⟩ ha ⟨w, u⟩ hb he
    simp only [List.mem_append, List.mem_singleton, List.mem_product,
      List.mem_cons, List.not_mem_nil, or_false] at ha hb
    have ht : t = u := congrArg Prod.snd he
    rcases ha with ha | ha
    · have : t = 6 := congrArg Prod.snd ha
      omega
    · omega

theorem literal_mem_columns {φ : CNF ℕ} {l : Literal ℕ}
    (hl : l.1 ∈ ThreeSAT.distinctVars φ) :
    literalColumn l ∈ columns φ ∧ negColumn l ∈ columns φ := by
  cases h : l.2 <;> simp [columns, literalColumn, negColumn, h, hl]

theorem supports_valid (φ : CNF ℕ) (hw : ∀ c ∈ φ, c.length = 3) :
    ∀ r ∈ supports φ, r.Nodup ∧ ∀ c ∈ r, c ∈ columns φ := by
  intro r hr
  simp only [supports, List.mem_append, List.mem_singleton, List.mem_map,
    List.mem_flatMap, List.mem_range] at hr
  rcases hr with (rfl | ⟨v, hv, rfl⟩) | ⟨j, hj, hr⟩
  · simp [columns]
  · constructor
    · simp
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [columns, hv]
  · have hget : φ.getD j [] = φ[j] := List.getD_eq_getElem _ _ hj
    have hc := hw _ (List.getElem_mem hj)
    obtain ⟨l₁, l₂, l₃, he⟩ := List.length_eq_three.mp hc
    have hvar (l : Literal ℕ) (hl : l ∈ [l₁, l₂, l₃]) :
        l.1 ∈ ThreeSAT.distinctVars φ :=
      ThreeSAT.mem_distinctVars_of_mem (j := j) (by rw [hget, he]; exact hl)
    have h₁ := literal_mem_columns (hvar l₁ (by simp))
    have h₂ := literal_mem_columns (hvar l₂ (by simp))
    have h₃ := literal_mem_columns (hvar l₃ (by simp))
    have haux (t : ℕ) (ht : t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5) :
        (j, t) ∈ columns φ := by
      simp [columns, hj, ht]
    have hn (l : Literal ℕ) (t : ℕ) (ht : 2 ≤ t) :
        negColumn l ≠ (j, t) ∧ literalColumn l ≠ (j, t) := by
      cases h : l.2 <;> simp [negColumn, literalColumn, h] <;> omega
    simp only [clauseRows, hget, he, List.getD_cons_zero, List.getD_cons_succ,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp [hn l₁ 2 (by omega), hn l₁ 3 (by omega)]
      · intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl
        · exact h₁.2
        · exact haux 2 (by simp)
        · exact haux 3 (by simp)
    · refine ⟨?_, ?_⟩
      · simp [Ne.symm (hn l₂ 3 (by omega)).2, (hn l₂ 4 (by omega)).2]
      · intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl
        · exact haux 3 (by simp)
        · exact h₂.1
        · exact haux 4 (by simp)
    · refine ⟨?_, ?_⟩
      · simp [Ne.symm (hn l₃ 4 (by omega)).1, Ne.symm (hn l₃ 5 (by omega)).1]
      · intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl
        · exact haux 4 (by simp)
        · exact haux 5 (by simp)
        · exact h₃.2

/-- The three-equation truth-table has explicit auxiliary witnesses. -/
theorem gadget_witness (u v w : Bool) (h : (u || v || w) = true) :
    Gadget u v w (u && v) (u && !v) (!u && !v) (w && (u || v)) := by
  cases u <;> cases v <;> cases w <;> simp_all [Gadget, bit]

/-- Truth assignments extended to the private clause columns. -/
def assignment (φ : CNF ℕ) (σ : ℕ → Bool) (p : Column) : Bool :=
  let c := φ.getD p.1 []
  let u := Literal.eval σ (c.getD 0 (0, true))
  let v := Literal.eval σ (c.getD 1 (0, true))
  let w := Literal.eval σ (c.getD 2 (0, true))
  match p.2 with
  | 0 => σ p.1
  | 1 => !σ p.1
  | 2 => u && v
  | 3 => u && !v
  | 4 => !u && !v
  | 5 => w && (u || v)
  | _ => true

theorem assignment_literal (φ : CNF ℕ) (σ : ℕ → Bool) (l : Literal ℕ) :
    assignment φ σ (literalColumn l) = Literal.eval σ l ∧
    assignment φ σ (negColumn l) = !Literal.eval σ l := by
  cases l with
  | mk v b => cases b <;> simp [assignment, literalColumn, negColumn, Literal.eval]

/-- Sparse equations are equivalent to the dummy, complementary pairs and
three local equations for each clause. -/
theorem supports_equations (φ : CNF ℕ) (τ : Column → Bool) :
    (∀ r ∈ supports φ, (r.map fun c => bit (τ c)).sum = 1) ↔
    bit (τ (0, 6)) = 1 ∧
    (∀ v ∈ ThreeSAT.distinctVars φ, bit (τ (v, 0)) + bit (τ (v, 1)) = 1) ∧
    ∀ j < φ.length,
      bit (τ (negColumn ((φ.getD j []).getD 0 (0, true)))) + bit (τ (j, 2)) +
        bit (τ (j, 3)) = 1 ∧
      bit (τ (j, 3)) + bit (τ (literalColumn ((φ.getD j []).getD 1 (0, true)))) +
        bit (τ (j, 4)) = 1 ∧
      bit (τ (j, 4)) + bit (τ (j, 5)) +
        bit (τ (negColumn ((φ.getD j []).getD 2 (0, true)))) = 1 := by
  simp only [supports, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_nil, List.forall_mem_map, List.forall_mem_flatMap]
  simp [clauseRows, add_assoc, and_assoc]

theorem sparse_correct (φ : CNF ℕ) (hw : ∀ c ∈ φ, c.length = 3) :
    (∃ τ : Column → Bool, ∀ r ∈ supports φ, (r.map fun c => bit (τ c)).sum = 1) ↔
      φ.Satisfiable := by
  constructor
  · rintro ⟨τ, hτ⟩
    obtain ⟨_, hpairs, hclauses⟩ := (supports_equations φ τ).mp hτ
    let σ : ℕ → Bool := fun v => τ (v, 0)
    have hneg (v : ℕ) (hv : v ∈ ThreeSAT.distinctVars φ) : τ (v, 1) = !σ v := by
      have hp := hpairs v hv
      dsimp [σ]
      cases h₀ : τ (v, 0) <;> cases h₁ : τ (v, 1) <;> simp_all [bit]
    have hlit (l : Literal ℕ) (hl : l.1 ∈ ThreeSAT.distinctVars φ) :
        τ (literalColumn l) = Literal.eval σ l ∧
        τ (negColumn l) = !Literal.eval σ l := by
      cases l with
      | mk v b => cases b <;> simp [literalColumn, negColumn, Literal.eval, hneg v hl, σ]
    refine ⟨σ, (CNF.eval_eq_true_iff σ φ).mpr fun c hc => ?_⟩
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hc
    have hget : φ.getD j.val [] = c := by
      rw [List.getD_eq_getElem _ _ j.isLt]
      simpa only [List.get_eq_getElem] using hj
    obtain ⟨l₁, l₂, l₃, rfl⟩ := List.length_eq_three.mp (hw c hc)
    have hvars (l : Literal ℕ) (hl : l ∈ [l₁, l₂, l₃]) :
        l.1 ∈ ThreeSAT.distinctVars φ :=
      ThreeSAT.mem_distinctVars_of_mem (j := j.val) (by rw [hget]; exact hl)
    have h₁ := hlit l₁ (hvars _ (by simp))
    have h₂ := hlit l₂ (hvars _ (by simp))
    have h₃ := hlit l₃ (hvars _ (by simp))
    have hg := hclauses j.val j.isLt
    simp only [hget, List.getD_cons_zero, List.getD_cons_succ, h₁.2, h₂.1, h₃.2] at hg
    have ht := (gadget_iff (Literal.eval σ l₁) (Literal.eval σ l₂)
      (Literal.eval σ l₃)).mp ⟨τ (j.val, 2), τ (j.val, 3), τ (j.val, 4), τ (j.val, 5), hg⟩
    simpa [Bool.or_assoc] using ht
  · rintro ⟨σ, hσ⟩
    refine ⟨assignment φ σ, (supports_equations φ _).mpr ⟨rfl, ?_, ?_⟩⟩
    · intro v _
      cases h : σ v <;> simp [assignment, h]
    · intro j hj
      have hc := (CNF.eval_eq_true_iff σ φ).mp hσ _ (List.getElem_mem hj)
      have he := hw _ (List.getElem_mem hj)
      obtain ⟨l₁, l₂, l₃, hls⟩ := List.length_eq_three.mp he
      have hget : φ.getD j [] = [l₁, l₂, l₃] := by
        rw [List.getD_eq_getElem _ _ hj, hls]
      have ht : (Literal.eval σ l₁ || Literal.eval σ l₂ || Literal.eval σ l₃) = true := by
        simpa [hls, Bool.or_assoc] using hc
      have hg := gadget_witness _ _ _ ht
      rw [hget]
      simp only [List.getD_cons_zero, List.getD_cons_succ,
        (assignment_literal φ σ l₁).2, (assignment_literal φ σ l₂).1,
        (assignment_literal φ σ l₃).2]
      simpa only [Gadget, assignment, hget, List.getD_cons_zero, List.getD_cons_succ] using hg

theorem noSystem_not_feasible : ¬ noSystem.Feasible := by
  rintro ⟨_, ξ, _, heq⟩
  have h := congrFun heq ⟨0, by decide⟩
  norm_num [MaskedSystem.residual, MaskedSys.toSystem, MaskedSys.rows,
    MaskedSys.rhs, MaskedSys.cols, noSystem] at h

theorem correct (φ : CNF ℕ) : φ ∈ ExactThreeSAT ↔ (reduce φ).Feasible := by
  by_cases hw : (φ.all fun c => c.length == 3) = true
  · have hwidth : ∀ c ∈ φ, c.length = 3 := by simpa only [List.all_eq_true, beq_iff_eq] using hw
    rw [reduce, if_pos hw, denseSystem_feasible_iff _ _ (nodup_columns φ)
      (supports_valid φ hwidth), sparse_correct φ hwidth]
    exact ⟨And.right, fun h => ⟨hwidth, h⟩⟩
  · rw [reduce, if_neg hw]
    constructor
    · intro h
      exact (hw (by simpa only [List.all_eq_true, beq_iff_eq] using h.1)).elim
    · intro h
      exact (noSystem_not_feasible h).elim

theorem positive_sizes (φ : CNF ℕ) :
    0 < (reduce φ).cols ∧ 0 < (reduce φ).rows.length := by
  unfold reduce
  split
  · simp [denseSystem, columns, supports, MaskedSys.cols, MaskedSys.rows]
  · decide

@[fun_prop] theorem poly_literalColumn :
    ComputableTidilyInPolyTime literalColumn (encPair encNat encBool) encColumn := by
  unfold literalColumn encColumn
  fun_prop

@[fun_prop] theorem poly_negColumn :
    ComputableTidilyInPolyTime negColumn (encPair encNat encBool) encColumn := by
  unfold negColumn encColumn
  fun_prop

/- Keep total lookup opaque during certificate composition: unfolding its
recursive implementation makes definitional equality expand exponentially. -/
attribute [local irreducible] List.getD

@[fun_prop] theorem poly_clauseRows :
    ComputableTidilyInPolyTime (fun p : ℕ × Clause ℕ => clauseRows p.1 p.2)
      (encPair encNat (encList (encPair encNat encBool))) (encList (encList encColumn)) := by
  let ein := encPair encNat (encList (encPair encNat encBool))
  have hj (t : ℕ) : ComputableTidilyInPolyTime
      (fun p : ℕ × Clause ℕ => (p.1, t)) ein encColumn :=
    (fst encNat _).prod (const t)
  have hget (k : ℕ) : ComputableTidilyInPolyTime
      (fun p : ℕ × Clause ℕ => p.2.getD k (0, true)) ein (encPair encNat encBool) :=
    (listGetD (encA := encPair encNat encBool) (0, true)).comp
      ((snd encNat _).prod (const k))
  have row₁ : ComputableTidilyInPolyTime
      (fun p : ℕ × Clause ℕ => [negColumn (p.2.getD 0 (0, true)), (p.1, 2), (p.1, 3)])
      ein (encList encColumn) :=
    cons' (poly_negColumn.comp (hget 0)) (cons' (hj 2) (cons' (hj 3) (const [])))
  have row₂ : ComputableTidilyInPolyTime
      (fun p : ℕ × Clause ℕ => [(p.1, 3), literalColumn (p.2.getD 1 (0, true)), (p.1, 4)])
      ein (encList encColumn) :=
    cons' (hj 3) (cons' (poly_literalColumn.comp (hget 1)) (cons' (hj 4) (const [])))
  have row₃ : ComputableTidilyInPolyTime
      (fun p : ℕ × Clause ℕ => [(p.1, 4), (p.1, 5), negColumn (p.2.getD 2 (0, true))])
      ein (encList encColumn) :=
    cons' (hj 4) (cons' (hj 5) (cons' (poly_negColumn.comp (hget 2)) (const [])))
  exact cons' row₁ (cons' row₂ (cons' row₃ (const [])))

@[fun_prop] theorem poly_columns :
    ComputableTidilyInPolyTime columns encCNF (encList encColumn) := by
  unfold columns SProd.sprod List.instSProd List.product encColumn encCNF
  fun_prop

@[fun_prop] theorem poly_supports :
    ComputableTidilyInPolyTime supports encCNF (encList (encList encColumn)) := by
  unfold supports
  apply ComputableTidilyInPolyTime.listAppend'
  · apply ComputableTidilyInPolyTime.listAppend'
    · fun_prop
    · apply ComputableTidilyInPolyTime.mapWithInput
      · exact ThreeSAT.computableTidilyInPolyTime_distinctVars
      · unfold encColumn
        fun_prop
  · apply ComputableTidilyInPolyTime.flatMapWithInput (encA := encUnary)
    · unfold encCNF
      fun_prop
    · have hinput : ComputableTidilyInPolyTime
          (fun p : CNF ℕ × ℕ => (p.2, p.1.getD p.2 []))
          (encPair encCNF encUnary)
          (encPair encNat (encList (encPair encNat encBool))) :=
        (unary_to_binary.comp (snd encCNF encUnary)).prod
          (listGetD (encA := encList (encPair encNat encBool))
            (encL := encList (encList (encPair encNat encBool))) [])
      have h := poly_clauseRows.comp hinput
      simpa only [Function.comp_def] using h

@[fun_prop] theorem poly_denseRow :
    ComputableTidilyInPolyTime (fun p : List Column × List Column => denseRow p.1 p.2)
      (encPair (encList encColumn) (encList encColumn)) (encList encBool) := by
  have heq : (fun p : List Column × List Column => denseRow p.1 p.2) =
      (fun p => p.1.map fun c => p.2.any fun e => decide (e = c)) := by
    funext p
    unfold denseRow
    congr 1
    funext c
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, List.any_eq_true]
    simp
  rw [heq]
  have hcontains : ComputableTidilyInPolyTime
      (fun p : List Column × Column => p.1.any fun e => decide (e = p.2))
      (encPair (encList encColumn) encColumn) encBool := by
    apply ComputableTidilyInPolyTime.anyWithInput (encA := encColumn) (by fun_prop)
    exact (ComputableTidilyInPolyTime.decide_eq encColumn).comp
      ((ComputableTidilyInPolyTime.snd _ _).prod
        (ComputableTidilyInPolyTime.fst _ _).snd')
  apply ComputableTidilyInPolyTime.mapWithInput (encA := encColumn) (by fun_prop)
  exact hcontains.comp ((ComputableTidilyInPolyTime.fst _ _).snd'.prod
    (ComputableTidilyInPolyTime.snd _ _))

@[fun_prop] theorem poly_denseSystem :
    ComputableTidilyInPolyTime (fun p : List Column × List (List Column) => denseSystem p.1 p.2)
      (encPair (encList encColumn) (encList (encList encColumn))) encMasked := by
  unfold denseSystem encMasked
  fun_prop

@[fun_prop] theorem poly_reduce :
    ComputableTidilyInPolyTime reduce encCNF encMasked := by
  unfold reduce
  fun_prop

end SatToMasked

/-- The total list reduction, including malformed and empty formulas. -/
abbrev satToMasked := SatToMasked.reduce

theorem satToMasked_correct (φ : CNF ℕ) :
    φ ∈ ExactThreeSAT ↔ (satToMasked φ).Feasible := SatToMasked.correct φ

theorem polyTimeReducible_ExactThreeSAT_Masked :
    PolyTimeReducible encCNF encMasked ExactThreeSAT {S | S.Feasible} :=
  ⟨satToMasked, SatToMasked.poly_reduce, satToMasked_correct⟩

theorem maskedSys_npHard : NPHard encMasked {S | S.Feasible} :=
  ExactThreeSAT_npHard.trans polyTimeReducible_ExactThreeSAT_Masked

end IdealCVP
