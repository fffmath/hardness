import Power2ModuleSVP.Runtime.Repair.Rows

/-!
# Probability

Local expectations evaluated with fixed recursion depth. The depth is a
constant of the program; arbitrary multipliers are capped before enumeration.
The exactness theorem only needs the proved support bound for candidates.

Paper: `paper/power2svp.pdf`, Section 5 (Theorems 3–4 and deterministic anchor repair).
-/
namespace Power2ModuleSVP.AnchorRepairRuntime
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] List.getD

abbrev Assignments := List (ℕ × Bool)
abbrev encAssignments := encList (encPair encUnary encBool)

def assignmentGet (a : Assignments) (j : ℕ) : Bool :=
  ((a.find? fun x => decide (x.1 = j)).getD (0,false)).2

attribute [local irreducible] assignmentGet

@[fun_prop] theorem assignmentGet_polytime : ComputableTidilyInPolyTime
    (fun a : Assignments × ℕ => assignmentGet a.1 a.2)
    (encPair encAssignments encUnary) encBool := by
  unfold assignmentGet
  fun_prop

theorem assignmentGet_cons (a : Assignments) (j : ℕ) (b : Bool) :
    assignmentGet ((j,b)::a) = Function.update (assignmentGet a) j b := by
  funext k
  by_cases hj : j = k
  · subst k
    simp [assignmentGet]
  · simp [assignmentGet, hj, Function.update_of_ne (Ne.symm hj)]

abbrev ProbInput := IdealCVP.RingArgs × (ℕ × (List Bool × Fraction))
abbrev encProbInput := encPair IdealCVP.encRingArgs
  (encPair encUnary (encPair (encList encBool) encFraction))

def rowValueList (a : ProbInput) (flags : Assignments) : ℤ :=
  ((supportList a.1.1 a.1.2.2).map fun j =>
    (if j ≤ a.2.1 then (1 : ℤ) else -1) *
      a.1.2.1.getD ((a.2.1+a.1.1-j)%a.1.1) 0 * a.1.2.2.getD j 0 *
      (if assignmentGet flags ((a.2.1+a.1.1-j)%a.1.1) then -1 else 1)).sum

attribute [local irreducible] rowValueList

@[fun_prop] theorem rowValueList_polytime : ComputableTidilyInPolyTime
    (fun a : ProbInput × Assignments => rowValueList a.1 a.2)
    (encPair encProbInput encAssignments) encIntBin := by
  unfold rowValueList
  apply intBin_sum.comp
  apply mapWithInput (encA := encUnary)
  · apply supportList_polytime.comp (g := fun a : ProbInput × Assignments =>
      (a.1.1.1,a.1.1.2.2))
    unfold encSupportInput encProbInput IdealCVP.encRingArgs
    fun_prop
  · have hc : ComputableTidilyInPolyTime
        (fun a : (ProbInput × Assignments) × ℕ => a.1.1)
        (encPair (encPair encProbInput encAssignments) encUnary) encProbInput :=
      (fst _ _).fst'
    have hd := hc.fst'.fst'
    have hs := hc.fst'.snd'.fst'
    have hv := hc.fst'.snd'.snd'
    have hi := hc.snd'.fst'
    have hj := snd (encPair encProbInput encAssignments) encUnary
    have hflags := (fst (encPair encProbInput encAssignments) encUnary).snd'
    have hr := unary_mod.comp
      ((unary_sub.comp ((unary_add.comp (hi.prod hd)).prod hj)).prod hd)
    have hsgn := (unary_le.comp (hj.prod hi)).ite_decide (encB := encIntBin)
      (const (1 : ℤ)) (const (-1 : ℤ))
    have hseed := (listGetD (encA := encIntBin) 0).comp (hs.prod hr)
    have hmult := (listGetD (encA := encIntBin) 0).comp (hv.prod hj)
    have hflip := (assignmentGet_polytime.comp (hflags.prod hr)).ite' (encMid := encIntBin)
      (const (-1 : ℤ)) (const (1 : ℤ))
    exact intBin_mul.comp
      ((intBin_mul.comp ((intBin_mul.comp (hsgn.prod hseed)).prod hmult)).prod hflip)

theorem rowValueList_eq (a : ProbInput) (flags : Assignments) :
    rowValueList a flags =
      AnchorTests.rowValue a.1.1 a.1.2.1 a.1.2.2 a.2.1 (assignmentGet flags) := by
  unfold rowValueList AnchorTests.rowValue
  rw [← supportList_eq]
  exact (List.sum_toFinset _ (show (supportList a.1.1 a.1.2.2).Nodup from
    List.nodup_range.filter _)).symm

def rowFraction (a : ProbInput) (flags : Assignments) : Fraction :=
  (if rowValueList a flags = -1 ∨ rowValueList a flags = 1 then 1 else 0, 1)

attribute [local irreducible] rowFraction

@[fun_prop] theorem rowFraction_polytime : ComputableTidilyInPolyTime
    (fun a : ProbInput × Assignments => rowFraction a.1 a.2)
    (encPair encProbInput encAssignments) encFraction := by
  unfold rowFraction encFraction
  fun_prop

theorem rowFraction_spec (a : ProbInput) (flags : Assignments) :
    0 < (rowFraction a flags).2 ∧ fractionValue (rowFraction a flags) =
      AnchorTests.rowIndicator a.1.1 a.1.2.1 a.1.2.2 a.2.1 (assignmentGet flags) := by
  simp only [rowFraction, fractionValue, AnchorTests.rowIndicator, rowValueList_eq,
    Int.cast_one, div_one]
  split_ifs <;> norm_num

def fractionOneSub (p : Fraction) : Fraction := (p.2-p.1,p.2)

@[fun_prop] theorem fractionOneSub_polytime :
    ComputableTidilyInPolyTime fractionOneSub encFraction encFraction := by
  unfold fractionOneSub encFraction
  fun_prop

theorem fractionOneSub_spec (p : Fraction) (hp : 0 < p.2) :
    0 < (fractionOneSub p).2 ∧ fractionValue (fractionOneSub p) = 1-fractionValue p := by
  refine ⟨hp, ?_⟩
  have hpq : (p.2 : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  simp only [fractionOneSub, fractionValue, Int.cast_sub]
  field_simp

abbrev LocalInput := ProbInput × (List ℕ × Assignments)
abbrev encLocalInput := encPair encProbInput (encPair (encList encUnary) encAssignments)

def localFraction : ℕ → LocalInput → Fraction
  | 0, a => rowFraction a.1 a.2.2
  | n+1, a =>
    match a.2.1 with
    | [] => rowFraction a.1 a.2.2
    | j::js =>
      if j < a.1.2.2.1.length then
        localFraction n (a.1, (js, (j,a.1.2.2.1.getD j false)::a.2.2))
      else
        fractionAdd
          (fractionMul (fractionOneSub a.1.2.2.2,
            localFraction n (a.1, (js, (j,false)::a.2.2))),
           fractionMul (a.1.2.2.2,
            localFraction n (a.1, (js, (j,true)::a.2.2))))

attribute [local irreducible] localFraction

@[fun_prop] theorem localFraction_polytime (n : ℕ) :
    ComputableTidilyInPolyTime (localFraction n) encLocalInput encFraction := by
  have hc := fst encProbInput (encPair (encList encUnary) encAssignments)
  have hv := (snd encProbInput (encPair (encList encUnary) encAssignments)).fst'
  have hf := (snd encProbInput (encPair (encList encUnary) encAssignments)).snd'
  have hh := (headD (encA := encUnary) 0).comp hv
  have ht := (tail (encA := encUnary)).comp hv
  have hp := hc.snd'.snd'.fst'
  have hb := (listGetD (encA := encBool) (encL := encList encBool) false).comp (hp.prod hh)
  have hmk {b : LocalInput → Bool}
      (hbit : ComputableTidilyInPolyTime b encLocalInput encBool) :
      ComputableTidilyInPolyTime
        (fun a : LocalInput => (a.1,(a.2.1.tail,(a.2.1.headD 0,b a)::a.2.2)))
        encLocalInput encLocalInput :=
    hc.prod (ht.prod (cons' (hh.prod hbit) hf))
  induction n with
  | zero =>
    have he : localFraction 0 = fun a : LocalInput => rowFraction a.1 a.2.2 := by
      funext a
      simp only [localFraction]
    rw [he]
    exact (rowFraction_polytime.comp (hc.prod hf)).of_enc_eq (fun _ => rfl)
  | succ n ih =>
    have hrec (b : Bool) : ComputableTidilyInPolyTime
        (fun a : LocalInput => localFraction n (a.1,
          (a.2.1.tail, (a.2.1.headD 0,b)::a.2.2))) encLocalInput encFraction := by
      exact ih.comp (hmk (const b))
    have hfixed : ComputableTidilyInPolyTime
        (fun a : LocalInput => localFraction n (a.1,
          (a.2.1.tail, (a.2.1.headD 0,a.1.2.2.1.getD (a.2.1.headD 0) false)::a.2.2)))
        encLocalInput encFraction := by
      exact ih.comp (hmk hb)
    have he : localFraction (n+1) = fun a : LocalInput =>
        if a.2.1.isEmpty then rowFraction a.1 a.2.2
        else if a.2.1.headD 0 < a.1.2.2.1.length then
          localFraction n (a.1, (a.2.1.tail,
            (a.2.1.headD 0,a.1.2.2.1.getD (a.2.1.headD 0) false)::a.2.2))
        else fractionAdd
          (fractionMul (fractionOneSub a.1.2.2.2,
            localFraction n (a.1, (a.2.1.tail,(a.2.1.headD 0,false)::a.2.2))),
           fractionMul (a.1.2.2.2,
            localFraction n (a.1, (a.2.1.tail,(a.2.1.headD 0,true)::a.2.2)))) := by
      funext a
      rw [localFraction]
      cases a.2.1 <;> rfl
    rw [he]
    have hempty : ComputableTidilyInPolyTime (fun a : LocalInput => a.2.1.isEmpty)
        encLocalInput encBool := (listIsEmpty (encA := encUnary)).comp hv
    have htest : ComputableTidilyInPolyTime
        (fun a : LocalInput => decide (a.2.1.headD 0 < a.1.2.2.1.length))
        encLocalInput encBool := unary_lt.comp (hh.prod ((length encBool).comp hp))
    have hbase : ComputableTidilyInPolyTime (fun a : LocalInput => rowFraction a.1 a.2.2)
        encLocalInput encFraction :=
      (rowFraction_polytime.comp (hc.prod hf)).of_enc_eq (fun _ => rfl)
    have hp : ComputableTidilyInPolyTime (fun a : LocalInput => a.1.2.2.2)
        encLocalInput encFraction := hc.snd'.snd'.snd'
    exact hempty.ite' hbase (htest.ite_decide hfixed
      (fractionAdd_polytime.comp
        ((fractionMul_polytime.comp ((fractionOneSub_polytime.comp hp).prod (hrec false))).prod
          (fractionMul_polytime.comp (hp.prod (hrec true))))))

theorem localFraction_spec (n : ℕ) (a : LocalInput)
    (hp : 0 < a.1.2.2.2.2) (hlen : a.2.1.length ≤ n) :
    0 < (localFraction n a).2 ∧ fractionValue (localFraction n a) =
      AnchorTests.localExpectation (fractionValue a.1.2.2.2) a.2.1
        (AnchorTests.rowIndicator a.1.1.1 a.1.1.2.1 a.1.1.2.2 a.1.2.1)
        (fun j => a.1.2.2.1[j]?) (assignmentGet a.2.2) := by
  induction n generalizing a with
  | zero =>
    have he : a.2.1 = [] := List.length_eq_zero_iff.mp (by omega)
    simpa only [localFraction, he, AnchorTests.localExpectation] using rowFraction_spec a.1 a.2.2
  | succ n ih =>
    rcases a with ⟨ctx, vars, flags⟩
    cases vars with
    | nil =>
      simpa only [localFraction, AnchorTests.localExpectation] using rowFraction_spec ctx flags
    | cons j js =>
      have ht : js.length ≤ n := by simpa using hlen
      have hf := ih (ctx, (js,(j,ctx.2.2.1.getD j false)::flags)) hp ht
      have h0 := ih (ctx, (js,(j,false)::flags)) hp ht
      have h1 := ih (ctx, (js,(j,true)::flags)) hp ht
      dsimp only at *
      simp only [localFraction]
      by_cases hj : j < ctx.2.2.1.length
      · rw [ite_eq_left hj]
        refine ⟨hf.1, ?_⟩
        rw [hf.2, AnchorTests.localExpectation,
          List.getElem?_eq_getElem hj, assignmentGet_cons]
        simp [List.getD_eq_getElem?_getD, hj]
      · rw [ite_eq_right hj]
        obtain ⟨hq, hqv⟩ := fractionOneSub_spec ctx.2.2.2 hp
        obtain ⟨h0p,h0v⟩ := fractionMul_spec _ _ hq h0.1
        obtain ⟨h1p,h1v⟩ := fractionMul_spec _ _ hp h1.1
        obtain ⟨hs,hsv⟩ := fractionAdd_spec _ _ h0p h1p
        refine ⟨hs, ?_⟩
        rw [hsv,h0v,h1v,hqv,h0.2,h1.2, AnchorTests.localExpectation,
          List.getElem?_eq_none_iff.mpr (by omega), assignmentGet_cons, assignmentGet_cons]

def rowProbabilityFraction (n : ℕ) (a : ProbInput) : Fraction :=
  localFraction n (a, (rowVars ((a.1.1,a.1.2.2),a.2.1), []))

@[fun_prop] theorem rowProbabilityFraction_polytime (n : ℕ) :
    ComputableTidilyInPolyTime (rowProbabilityFraction n) encProbInput encFraction := by
  unfold rowProbabilityFraction
  apply (localFraction_polytime n).comp
  have hr : ComputableTidilyInPolyTime
      (fun a : ProbInput => rowVars ((a.1.1,a.1.2.2),a.2.1))
      encProbInput (encList encUnary) := by
    apply rowVars_polytime.comp
    unfold encRowInput encSupportInput encProbInput IdealCVP.encRingArgs
    fun_prop
  unfold encLocalInput
  fun_prop

theorem rowProbabilityFraction_spec (n : ℕ) (a : ProbInput)
    (hp : 0 < a.2.2.2.2)
    (hlen : (AnchorTests.rowVariables a.1.1
      (AnchorTests.multiplierSupport a.1.1 a.1.2.2) a.2.1).length ≤ n) :
    0 < (rowProbabilityFraction n a).2 ∧
      fractionValue (rowProbabilityFraction n a) =
        AnchorTests.rowProbability a.1.1 a.1.2.1 a.1.2.2 a.2.1 a.2.2.1
          (fractionValue a.2.2.2) := by
  have he : assignmentGet [] = fun _ => false := by funext j; simp [assignmentGet]
  simpa only [rowProbabilityFraction, rowVars_eq, he, AnchorTests.rowProbability] using
    localFraction_spec n (a, (rowVars ((a.1.1,a.1.2.2),a.2.1), [])) hp
      (by simpa only [rowVars_eq] using hlen)

abbrev EventInput := IdealCVP.RingArgs × (List Bool × Fraction)
abbrev encEventInput := encPair IdealCVP.encRingArgs (encPair (encList encBool) encFraction)

def eventFraction (n : ℕ) (a : EventInput) : Fraction :=
  fractionProd ((rowsList (a.1.1,a.1.2.2)).map fun i =>
    rowProbabilityFraction n (a.1,(i,a.2)))

@[fun_prop] theorem eventFraction_polytime (n : ℕ) :
    ComputableTidilyInPolyTime (eventFraction n) encEventInput encFraction := by
  unfold eventFraction
  apply fractionProd_polytime.comp
  apply mapWithInput (encA := encUnary)
  · apply rowsList_polytime.comp
    unfold encSupportInput encEventInput IdealCVP.encRingArgs
    fun_prop
  · apply (rowProbabilityFraction_polytime n).comp
    unfold encProbInput encEventInput
    fun_prop

theorem eventFraction_spec (n : ℕ) (a : EventInput)
    (hp : 0 < a.2.2.2)
    (hs : (AnchorTests.multiplierSupport a.1.1 a.1.2.2).card ≤ n) :
    0 < (eventFraction n a).2 ∧
      fractionValue (eventFraction n a) =
        AnchorTests.eventProbability a.1.1 a.1.2.1 a.1.2.2 a.2.1 (fractionValue a.2.2) := by
  have hr (i : ℕ) (hi : i ∈ rowsList (a.1.1,a.1.2.2)) :
      0 < (rowProbabilityFraction n (a.1,(i,a.2))).2 ∧
        fractionValue (rowProbabilityFraction n (a.1,(i,a.2))) =
          AnchorTests.rowProbability a.1.1 a.1.2.1 a.1.2.2 i a.2.1 (fractionValue a.2.2) := by
    apply rowProbabilityFraction_spec n _ hp
    dsimp only
    have hb : ∀ j ∈ AnchorTests.multiplierSupport a.1.1 a.1.2.2, j < a.1.1 := by
      intro j hj
      exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hi' : i < a.1.1 :=
      AnchorTests.selectedRows_lt _ _ (by simpa only [rowsList_eq] using hi)
    exact (AnchorTests.rowVariables_length _ hb hi').le.trans hs
  have hpos : ∀ f ∈ (rowsList (a.1.1,a.1.2.2)).map
      (fun i => rowProbabilityFraction n (a.1,(i,a.2))), 0 < f.2 := by
    intro f hf
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hf
    exact (hr i hi).1
  obtain ⟨hfp,hfv⟩ := fractionProd_spec _ hpos
  refine ⟨hfp, hfv.trans ?_⟩
  unfold AnchorTests.eventProbability
  rw [List.map_map, ← rowsList_eq (a.1.1,a.1.2.2)]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (hr i hi).2

theorem localFraction_bits_polyBounded (n : ℕ) :
    PolyBounded (fun a => (encLocalInput a).length)
      (fun a => fractionBits (localFraction n a)) :=
  fractionBits_polyBounded_of (localFraction_polytime n)

theorem eventFraction_bits_polyBounded (n : ℕ) :
    PolyBounded (fun a => (encEventInput a).length)
      (fun a => fractionBits (eventFraction n a)) :=
  fractionBits_polyBounded_of (eventFraction_polytime n)

end Power2ModuleSVP.AnchorRepairRuntime
