# hp2n-asearch2: Corollary 4.4 completed

## Result

`Search/Turing.lean` formalizes the full deterministic polynomial-time one-query reduction
from binary Subset Sum to finding an exact shortest nonzero module vector. `Main.lean`
exports both library search-reduction hardness and the explicit oracle-machine theorem for
all NP decision languages. There are no remaining obligations for this task.

## Search problem and encoding

- Input: `IdealCVP.PairRingArgs`, encoded by `IdealCVP.encPairRingArgs`, with unary dyadic degree
  and four signed-binary generator lists in the existing column convention.
- `Search.encVector`: `encPair (encList encIntBin) (encList encIntBin)`.
- `Search.ExactShortest x word`: existing module wellformedness, and an encoded pair of
  exact-length coefficient lists representing an actual shortest nonzero module vector.
- `Search.exactShortest_domain`: the domain equals precisely the wellformed inputs. Shortest
  vectors exist there by the nonzero determinant and natural-number well ordering.
- `Search.DecisionAnswer L a word`: `word` is the single correct decision bit for `a ∈ L`.

## Native complexity interfaces

The old `STATUS-hp2n-asearch.md` predates `reduce_polytime`. That certificate now supplies the
query construction. The library's `ComputableInPolyTimeWithOracle` fixes a language oracle,
while `WordQueryComp Unit Bool` supports word replies. Its underlying `IsOraclePPTOn` has
`query_take`, `map_with`, and `preprocess` combinators, so no new machine/reduction framework
or unproved resource assumption was required.

`SearchReducible` applies directly to the correct-bit decision relation and `ExactShortest`.
For NP hardness the existing `HardUnder` quantifies over NP decision languages with this
adapter: the library's named `NPHard` has a decision-language target, whereas `SearchHard`
expects a class of search relations. The separate explicit oracle theorem establishes the
paper's Turing-reduction interpretation in the library's strict machine model.

`Search.shortestProgram` is deterministic and makes exactly one query. Its runtime certificate
holds against every stateful word handler, even handlers returning malformed or arbitrarily
long answers. It reads at most `answerLimit x` bits, where

```lean
3 * (reduce x).1.1 *
  (2 * ((encNat (2 * (reduce x).2 + 1)).length + 1) + 1) + 1
```

includes signs and all list/pair framing. `answerLimit_polytime` computes that bound in unary.
`answer_length_le` bounds every valid shortest reply by it; `answer_length_polyBounded`
provides a polynomial in the original binary source length. The bound uses `2M + 1`, covering
both the positive gadget and the total map's radius-zero constant NO case. Postprocessing
uses the existing total signed-binary decoder and binary-radius coefficient scans.

## Main exact statements

Open `Power2ModuleSVPSubsetSum.Search`, `Power2ModuleSVPSubsetSum.Reduction`,
`Turing.MultiTapeTM`, and `Cslib.Complexity` for the statements below.

```lean
theorem Search.subsetSum_searchReducible_exactShortest :
    SearchReducible encSource IdealCVP.encPairRingArgs
      (DecisionAnswer SubsetSum) ExactShortest

theorem Search.answer_length_polyBounded :
    ∃ c d : ℕ, ∀ x word, ExactShortest (searchQuery x) word →
      word.length ≤ c * ((encSource x).length + 1) ^ d

theorem Search.shortestProgram_polytime : Cslib.Probability.IsOraclePPTOn encSource encBool
    (fun x => Cslib.OracleComp.interpret Cslib.ProbOracleComp.query (shortestProgram x))

theorem Power2ModuleSVPSubsetSum.moduleSVP_search_npHard :
    HardUnder (fun enc L S => SearchReducible enc IdealCVP.encPairRingArgs
      (DecisionAnswer L) S) @NP ExactShortest

theorem Power2ModuleSVPSubsetSum.moduleSVP_search_turing_npHard
    {α : Type} (enc : α ↪ List Bool) (L : Set α) (hL : L ∈ NP enc) :
    ∃ program : α → WordQueryComp Unit Bool,
      Cslib.Probability.IsOraclePPTOn enc encBool
        (fun a => Cslib.OracleComp.interpret Cslib.ProbOracleComp.query (program a)) ∧
      (∀ (oracle : Unit × List Bool → List Bool),
        (∀ x, Power2ModuleSVP.SVPInput.WellFormed x →
          ExactShortest x (oracle ((), IdealCVP.encPairRingArgs x))) →
        ∀ a, a ∈ L ↔ Cslib.OracleComp.interpret (m := Id) oracle (program a) = true) ∧
      (∀ a, ∃ query, ∀ oracle : Unit × List Bool → List Bool,
        Cslib.OracleComp.queriesWith oracle (program a) = [((), query)])
```

## Verification

Successful final targeted build (exit 0):

```sh
LAKE_CACHE_DIR=/tmp/hardness-lake-cache /workspace/shared/bin/lake-locked build \
  Power2ModuleSVPSubsetSum.Search.Turing Power2ModuleSVPSubsetSum.Main
```

Log: `/tmp/hp2n-asearch2-build6.log`, 7905 jobs. `Search/Shortest.lean` also rebuilt successfully
after replacing its outdated runtime-scope docstring. No new warnings in the changed modules;
existing dependency module-system warnings were replayed.

Successful declaration, axiom, and executable check (exit 0):

```sh
LAKE_CACHE_DIR=/tmp/hardness-lake-cache /workspace/shared/bin/lake-locked env lean \
  /tmp/hp2n-asearch2-check.lean
```

Log: `/tmp/hp2n-asearch2-check.log`. Axiom checks of `exactShortest_domain`,
`subsetSum_searchReducible_exactShortest`, `answer_length_polyBounded`,
`shortestProgram_polytime`, `shortestProgram_correct`, and both Main hardness theorems
report only `propext`, `Classical.choice`, and `Quot.sound`.

Executable checks return `true`/`false` for `( [], 0 )`/`( [], 1 )` with the same actual
shortest vector `([1], [0])`. The bounded oracle program returns the same results; its budgets
are 22 and 16 bits respectively. All changed Lean lines have at most 100 characters;
`git diff --check` passes. No prohibited proof placeholders or new axioms occur.

Files: `Search/Turing.lean` (new), `Main.lean` (exports), `Search/Shortest.lean` (docstring only),
this status note. No fixed problem definitions, library roots, package sources, or lakefile edits.
