import Power2ModuleSVPSubsetSum.Runtime.Reduction
import Power2ModuleSVPSubsetSum.Reduction.Correctness
import Power2ModuleSVPSubsetSum.Membership.NP
import Power2ModuleSVPSubsetSum.Search.Turing

/-!
# Decision completeness and exact search hardness of power-of-two module SVP

The native polynomial-time coefficient-list reduction from binary Subset Sum,
its mathematical correctness, and the binary-radius verifier establish
NP-completeness of the coefficient maximum-norm rank-two module problem. Exact shortest-vector
search is NP-hard under deterministic polynomial-time Turing reductions, with one oracle query.

Paper: `paper/power2svp-subsetsum.pdf`, Theorem 1.1 and Corollary 4.4.
-/

namespace Power2ModuleSVPSubsetSum

open Turing.MultiTapeTM Cslib.Complexity

/-- Binary Subset Sum reduces in polynomial time to arbitrary-radius module SVP. -/
theorem subsetSum_polyTimeReducible_moduleSVP :
    PolyTimeReducible (encPair (encList encNat) encNat) encSVP
      Cslib.Complexity.SubsetSum ModuleSVPLang :=
  ⟨reduce, reduce_polytime, reduce_correct⟩

/-- Coefficient maximum-norm rank-two module SVP over dyadic rings is NP-hard. -/
theorem moduleSVP_npHard : NPHard encSVP ModuleSVPLang :=
  Cslib.Complexity.SubsetSum_npHard.trans subsetSum_polyTimeReducible_moduleSVP

/-- Coefficient maximum-norm rank-two module SVP over dyadic rings is NP-complete. -/
theorem moduleSVP_npComplete : NPComplete encSVP ModuleSVPLang :=
  ⟨moduleSVP_mem_NP, moduleSVP_npHard⟩

/-- Exact shortest-vector search is hard for every NP decision language. Decision outputs are
represented by their one correct bit in complexitylib's native search-reduction interface. -/
theorem moduleSVP_search_npHard :
    HardUnder (fun enc L S => SearchReducible enc IdealCVP.encPairRingArgs
      (Search.DecisionAnswer L) S) @NP Search.ExactShortest :=
  Search.exactShortest_search_npHard

/-- Corollary 4.4: every NP language has a deterministic polynomial-time oracle program deciding
it with exactly one call to any oracle returning an exact shortest nonzero module vector. -/
theorem moduleSVP_search_turing_npHard {α : Type} (enc : α ↪ List Bool) (L : Set α)
    (hL : L ∈ NP enc) :
    ∃ program : α → WordQueryComp Unit Bool,
      Cslib.Probability.IsOraclePPTOn enc encBool
        (fun a => Cslib.OracleComp.interpret Cslib.ProbOracleComp.query (program a)) ∧
      (∀ (oracle : Unit × List Bool → List Bool),
        (∀ x, Power2ModuleSVP.SVPInput.WellFormed x →
          Search.ExactShortest x (oracle ((), IdealCVP.encPairRingArgs x))) →
        ∀ a, a ∈ L ↔ Cslib.OracleComp.interpret (m := Id) oracle (program a) = true) ∧
      (∀ a, ∃ query, ∀ oracle : Unit × List Bool → List Bool,
        Cslib.OracleComp.queriesWith oracle (program a) = [((), query)]) :=
  Search.exactShortest_turing_npHard enc L hL

end Power2ModuleSVPSubsetSum
