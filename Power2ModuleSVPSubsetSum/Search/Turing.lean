import Power2ModuleSVPSubsetSum.Search.Shortest
import Power2ModuleSVPSubsetSum.Runtime.Reduction
import Power2ModuleSVPSubsetSum.Membership.PolyTime
import IdealCVP.Complexity.Witness
import Complexity.Computability.Complexity.Classes.TFNP
import Complexity.Computability.Complexity.Classes.Oracle
import Complexity.Computability.Probabilistic.Oracle.Composition

/-! # Exact shortest-vector search and its one-query Turing reduction

Paper: `paper/power2svp-subsetsum.pdf`, Corollary 4.4.

Instances use `IdealCVP.encPairRingArgs`; answers encode the two signed-binary coefficient
lists of an actual shortest nonzero vector. Malformed instances have no valid answers.
The decision problem is represented as the search relation returning its one correct bit.
`SearchReducible` is complexitylib's existing search reduction, with native TM certificates.
The deterministic word-query program additionally has complexitylib's strict oracle runtime
certificate, uniformly over arbitrary stateful handlers. It reads a bounded prefix so malformed,
arbitrarily long replies cannot defeat the clock; every valid shortest reply fits in that prefix.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Power2ModuleSVPSubsetSum.Search
open Power2ModuleSVP IdealCVP.Cyclotomic Reduction
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
open Cslib Cslib.Complexity

/-- Two coefficient lists, framed separately, with signed-binary integer entries. -/
def encVector : (List ℤ × List ℤ) ↪ List Bool :=
  encPair (encList encIntBin) (encList encIntBin)

/-- Exact shortest nonzero vector search on dyadic, full-rank rank-two modules.
The answer is the vector itself, rather than a pair of module multipliers. -/
def ExactShortest (x : IdealCVP.PairRingArgs) (word : List Bool) : Prop :=
  Power2ModuleSVP.SVPInput.WellFormed x ∧
    ∃ z : List ℤ × List ℤ, encVector z = word ∧
      z.1.length = x.1 ∧ z.2.length = x.1 ∧
      IsShortest (inputA (x, 0)) (inputB (x, 0))
        (IdealCVP.ofList z.1, IdealCVP.ofList z.2)

/-- A decision language as a search relation: return exactly its correct one-bit answer. -/
def DecisionAnswer {α : Type} (L : Set α) (a : α) (word : List Bool) : Prop :=
  ∃ b : Bool, word = [b] ∧ (a ∈ L ↔ b = true)

/-- Total decoding of the two signed-binary coefficient lists. -/
def vectorDecoder : Decoder encVector :=
  IdealCVP.intBinDecoder.list.pair IdealCVP.intBinDecoder.list

/-- Every wellformed module has an attained nonzero shortest vector. -/
theorem wellFormed_shortest_exists (x : IdealCVP.PairRingArgs)
    (hw : Power2ModuleSVP.SVPInput.WellFormed x) :
    ∃ v, IsShortest (inputA (x, 0)) (inputB (x, 0)) v := by
  have hdet : IdealCVP.ofList (d := x.1) (IdealCVP.listDet x.1 x.2.1 x.2.2) ≠ 0 :=
    (IdealCVP.list_any_ne_zero _ _ (by simp [IdealCVP.listDet, IdealCVP.listSub])).mp
      hw.2.2.2.2.2
  have hA : inputA (x, 0) ≠ 0 := by
    intro hz
    have h1 : IdealCVP.ofList (d := x.1) x.2.1.1 = 0 := congrArg Prod.fst hz
    have h2 : IdealCVP.ofList (d := x.1) x.2.1.2 = 0 := congrArg Prod.snd hz
    apply hdet
    simp only [IdealCVP.listDet, IdealCVP.ofList_listSub,
      IdealCVP.ofList_negacyclicMul, h1, h2, coeff_mul_zero_left, sub_self]
  have he : moduleVector (inputA (x, 0)) (inputB (x, 0)) (coeffOne hw.1.pos) 0 =
      inputA (x, 0) := by
    simp only [moduleVector, mul_coeffOne_right, mul_zero, add_zero]
  obtain ⟨r, hr⟩ := firstMinimum_exists_of_nonzero_vector _ _ _ _ (he ▸ hA)
  exact exists_isShortest_of_firstMinimum hr

/-- The search domain is exactly the wellformed module inputs; malformed inputs have no answer. -/
theorem exactShortest_domain : searchDomain ExactShortest =
    {x | Power2ModuleSVP.SVPInput.WellFormed x} := by
  ext x
  constructor
  · rintro ⟨word, hw, _⟩
    exact hw
  · intro hw
    obtain ⟨v, hv⟩ := wellFormed_shortest_exists x hw
    refine ⟨encVector (IdealCVP.toList v.1, IdealCVP.toList v.2), hw,
      (IdealCVP.toList v.1, IdealCVP.toList v.2), rfl,
      IdealCVP.length_toList _, IdealCVP.length_toList _, ?_⟩
    simpa only [IdealCVP.ofList_toList, Prod.mk.eta] using hv

/-- The query discards the radius, retaining precisely the module instance. -/
def searchQuery (x : List ℕ × ℕ) : IdealCVP.PairRingArgs := (reduce x).1

/-- The actual search query is computable in native polynomial time. -/
@[fun_prop] theorem searchQuery_polytime : ComputableTidilyInPolyTime
    searchQuery encSource IdealCVP.encPairRingArgs :=
  (fst IdealCVP.encPairRingArgs encNat).comp reduce_polytime

attribute [local irreducible] reduce

/-- A shortest vector exists for every module queried by the total reduction. -/
theorem searchQuery_shortest_exists (x : List ℕ × ℕ) :
    ∃ v, IsShortest (inputA (reduce x)) (inputB (reduce x)) v := by
  exact wellFormed_shortest_exists _ (reduce_wellFormed x)

/-- Every query has a valid encoded shortest-vector answer, including the constant cases. -/
theorem searchQuery_has_answer (x : List ℕ × ℕ) :
    searchQuery x ∈ searchDomain ExactShortest := by
  rw [exactShortest_domain]
  exact reduce_wellFormed x

/-- Read both coefficient lists and test the stored decision radius. -/
def answerTest (p : (List ℕ × ℕ) × List Bool) : Bool :=
  let z := vectorDecoder.decode p.2
  Membership.listWithin ((reduce p.1).2, z.1) &&
    Membership.listWithin ((reduce p.1).2, z.2)

/-- Reading and comparing a candidate answer is polynomial time in input and answer length. -/
@[fun_prop] theorem answerTest_polytime : ComputableTidilyInPolyTime
    answerTest (encPair encSource encBits) encBool := by
  have hd := vectorDecoder.computableTidilyInPolyTime.comp (snd encSource encBits)
  have hM := (snd IdealCVP.encPairRingArgs encNat).comp
    (reduce_polytime.comp (fst encSource encBits))
  have h1 := Membership.listWithin_polytime.comp
    (hM.prod ((fst (encList encIntBin) (encList encIntBin)).comp hd))
  have h2 := Membership.listWithin_polytime.comp
    (hM.prod ((snd (encList encIntBin) (encList encIntBin)).comp hd))
  unfold answerTest
  exact bool_and.comp (h1.prod h2)

/-- Every valid shortest answer gives exactly the Subset Sum decision bit. -/
theorem answerTest_correct (x : List ℕ × ℕ) (word : List Bool)
    (h : ExactShortest (searchQuery x) word) :
    x ∈ SubsetSum ↔ answerTest (x, word) = true := by
  obtain ⟨_, z, rfl, hl, hr, hv⟩ := h
  simp only [answerTest, vectorDecoder.decode_enc, Bool.and_eq_true]
  rw [Membership.listWithin_spec _ hl, Membership.listWithin_spec _ hr]
  exact (reduce_search_correct x _ hv).trans (by simp only [pairSup, max_le_iff])

/-- Subset Sum, represented by its correct decision bit, reduces to exact vector search
in complexitylib's native search-reduction interface. -/
theorem subsetSum_searchReducible_exactShortest :
    SearchReducible encSource IdealCVP.encPairRingArgs
      (DecisionAnswer SubsetSum) ExactShortest := by
  refine ⟨searchQuery, (fun p => [answerTest p]), searchQuery_polytime, ?_,
    fun x _ => searchQuery_has_answer x, ?_⟩
  · fun_prop
  · intro x word h
    exact ⟨answerTest (x, word), rfl, answerTest_correct x word h⟩

/-- A unary reply budget includes framing, sign bits, and both length-degree lists.
The radius-zero constant NO case is covered by `2M + 1`. -/
def answerLimit (x : List ℕ × ℕ) : ℕ :=
  3 * (reduce x).1.1 * (2 * ((encNat (2 * (reduce x).2 + 1)).length + 1) + 1) + 1

/-- The number of answer bits to read is polynomial-time computable in unary. -/
@[fun_prop] theorem answerLimit_polytime : ComputableTidilyInPolyTime
    answerLimit encSource encUnary := by
  have h := reduce_polytime
  unfold encSVP IdealCVP.encPairRingArgs at h
  unfold answerLimit
  fun_prop

/-- Every valid shortest reply fits within the budget; no choice of shortest vector matters. -/
theorem answer_length_le (x : List ℕ × ℕ) (word : List Bool)
    (h : ExactShortest (searchQuery x) word) : word.length ≤ answerLimit x := by
  obtain ⟨_, z, rfl, hl, hr, hv⟩ := h
  have hn := reduce_shortest_bound x _ hv
  have hb : pairSup (IdealCVP.ofList (d := (reduce x).1.1) z.1,
      IdealCVP.ofList z.2) ≤ 2 * (reduce x).2 + 1 :=
    hn.trans (max_le (by omega) (by omega))
  have hb1 := (Membership.coeffSup_le_iff _ _).mp ((le_max_left _ _).trans hb)
  have hb2 := (Membership.coeffSup_le_iff _ _).mp ((le_max_right _ _).trans hb)
  have bound (l : List ℤ) (hl : l.length = (reduce x).1.1)
      (hc : ∀ i, (IdealCVP.ofList (d := (reduce x).1.1) l i).natAbs ≤
        2 * (reduce x).2 + 1) :
      (encList encIntBin l).length ≤ (reduce x).1.1 *
        (2 * ((encNat (2 * (reduce x).2 + 1)).length + 1) + 1) := by
    rw [← hl]
    apply length_encList_le
    intro a ha
    simp only [length_encIntBin, encNat_apply, Nat.size_eq_bits_len]
    apply Nat.add_le_add_right
    apply Nat.size_le_size
    exact (Power2ModuleSVP.list_all_iff l hl
      (fun z => z.natAbs ≤ 2 * (reduce x).2 + 1)).mpr hc a ha
  have h1 := bound z.1 hl hb1
  have h2 := bound z.2 hr hb2
  simp only [encVector, length_encPair, answerLimit, Nat.mul_assoc]
  omega

/-- A single polynomial in the binary source length bounds every valid shortest reply. -/
theorem answer_length_polyBounded :
    ∃ c d : ℕ, ∀ x word, ExactShortest (searchQuery x) word →
      word.length ≤ c * ((encSource x).length + 1) ^ d := by
  obtain ⟨c, d, h⟩ := answerLimit_polytime.polyBounded_length.exists_le
  refine ⟨c, d, fun x word hw => (answer_length_le x word hw).trans ?_⟩
  simpa only [encUnary_apply, List.length_replicate] using h x

/-- A deterministic program making exactly one query and reading only a bounded reply prefix. -/
def shortestProgram (x : List ℕ × ℕ) : WordQueryComp Unit Bool :=
  (fun word => answerTest (x, word.take (answerLimit x))) <$>
    OracleComp.query ((), IdealCVP.encPairRingArgs (searchQuery x))

/-- The one-query program has complexitylib's machine-certified strict oracle polynomial time,
uniformly over arbitrary stateful word oracles, including malformed or very long replies. -/
theorem shortestProgram_polytime : Cslib.Probability.IsOraclePPTOn encSource encBool
    (fun x => OracleComp.interpret Cslib.ProbOracleComp.query (shortestProgram x)) := by
  have hq := Cslib.Probability.IsOraclePPTOn.query_take ()
    searchQuery_polytime.encoded answerLimit_polytime
  have hp := hq.map_with (f := fun x word => answerTest (x, word)) answerTest_polytime
  simpa only [shortestProgram, OracleComp.interpret_map, OracleComp.interpret_query,
    Functor.map_map, Function.comp_def] using hp

/-- Every oracle supplying valid shortest vectors makes the one-query program decide Subset Sum. -/
theorem shortestProgram_correct
    (oracle : Unit × List Bool → List Bool)
    (h : ∀ x, Power2ModuleSVP.SVPInput.WellFormed x →
      ExactShortest x (oracle ((), IdealCVP.encPairRingArgs x))) (x : List ℕ × ℕ) :
    x ∈ SubsetSum ↔
      OracleComp.interpret (m := Id) oracle (shortestProgram x) = true := by
  have hx := h (searchQuery x) (reduce_wellFormed x)
  have hl := answer_length_le x _ hx
  change x ∈ SubsetSum ↔ answerTest
    (x, (oracle ((), IdealCVP.encPairRingArgs (searchQuery x))).take (answerLimit x)) = true
  rw [List.take_of_length_le hl]
  exact answerTest_correct x _ hx

/-- The complete query trace contains exactly the encoded module, for every answer handler. -/
theorem shortestProgram_queries (oracle : Unit × List Bool → List Bool) (x : List ℕ × ℕ) :
    OracleComp.queriesWith oracle (shortestProgram x) =
      [((), IdealCVP.encPairRingArgs (searchQuery x))] := by
  simp only [shortestProgram, OracleComp.queriesWith_map, OracleComp.queriesWith_query]

/-- Every NP decision language reduces to exact shortest-vector search using complexitylib's
search reduction on the one-bit decision-answer relation. -/
theorem exactShortest_search_npHard :
    HardUnder (fun enc L S => SearchReducible enc IdealCVP.encPairRingArgs
      (DecisionAnswer L) S) @NP ExactShortest := by
  intro α enc L hL
  obtain ⟨f, hf, hcorrect⟩ := SubsetSum_npHard enc L hL
  have hfirst : SearchReducible enc encSource (DecisionAnswer L)
      (DecisionAnswer SubsetSum) := by
    refine ⟨f, Prod.snd, hf, snd enc encBits, ?_, ?_⟩
    · intro a _
      classical
      exact ⟨[decide (f a ∈ SubsetSum)], _, rfl, by simp⟩
    · rintro a word ⟨b, hb, hbit⟩
      exact ⟨b, hb, (hcorrect a).trans hbit⟩
  exact hfirst.trans subsetSum_searchReducible_exactShortest

/-- Corollary 4.4 in the native oracle machine model: every encoded NP language is decided by
one deterministic polynomial-time word-query program, against every valid exact search oracle.
No run-time certificate or paper claim is assumed as a hypothesis. -/
theorem exactShortest_turing_npHard {α : Type} (enc : α ↪ List Bool) (L : Set α)
    (hL : L ∈ NP enc) :
    ∃ program : α → WordQueryComp Unit Bool,
      Cslib.Probability.IsOraclePPTOn enc encBool
        (fun a => OracleComp.interpret Cslib.ProbOracleComp.query (program a)) ∧
      (∀ (oracle : Unit × List Bool → List Bool),
        (∀ x, Power2ModuleSVP.SVPInput.WellFormed x →
          ExactShortest x (oracle ((), IdealCVP.encPairRingArgs x))) →
        ∀ a, a ∈ L ↔ OracleComp.interpret (m := Id) oracle (program a) = true) ∧
      (∀ a, ∃ query, ∀ oracle : Unit × List Bool → List Bool,
        OracleComp.queriesWith oracle (program a) = [((), query)]) := by
  obtain ⟨f, hf, hcorrect⟩ := SubsetSum_npHard enc L hL
  refine ⟨fun a => shortestProgram (f a), shortestProgram_polytime.preprocess hf, ?_, ?_⟩
  · intro oracle h a
    exact (hcorrect a).trans (shortestProgram_correct oracle h (f a))
  · intro a
    exact ⟨IdealCVP.encPairRingArgs (searchQuery (f a)),
      fun oracle => shortestProgram_queries oracle (f a)⟩

end Power2ModuleSVPSubsetSum.Search
