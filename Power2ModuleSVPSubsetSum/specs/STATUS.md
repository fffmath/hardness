# Final status — paper A

Decision NP-completeness is unconditional. `moduleSVP_npComplete` (namespace
`Power2ModuleSVPSubsetSum`, module `Main`) pairs binary-radius NP membership with the
native polynomial-time reduction from complexitylib's binary Subset Sum language.
The exact statement is `moduleSVP_npComplete : NPComplete encSVP ModuleSVPLang`.

- Mathematics: negacyclic adjoint/unit/norm API, opposite-pair identities, base-five
  support and multiplier rigidity, Boolean encoding, exact norm, nonzero determinant,
  total correctness, attained YES minimum and additive NO gap are proved.
- Runtime: actual list programs have native tidy multitape-TM certificates. Degrees
  and loop counters are unary; weights, coefficients, scales, and radius are binary.
  Powers of five use the library's intermediate bit-growth certificate. Exact list
  l1 norms are computed, including `rho`; no estimated-scale replacement is made.
- Membership: exact-length signed-binary multiplier lists, radius scans, squared bound
  `2*d*T²`, Cramer coefficient bounds and polynomial framed witness length yield NP.
  `Membership/Radius` remains shared with `Power2IdealSVP`.
- Source boundaries: repeated weights preserve multiplicities; zeros are removed;
  empty/all-zero lists use fixed degree-one identity outputs at radii one/zero.
- Corollary 4.3: `Search.witnessEquiv`, `card_shortVectors`, and executable recovery
  correctness are proved. The bijection counts actual nonzero short vectors as
  `2 * degree * number of satisfying Boolean assignments`, including the zero count.
- Corollary 4.4: complete. `Search/Shortest` proves existence, threshold correctness,
  and coefficient bounds. `Search/Turing` certifies encoded exact vector search and a
  deterministic one-query oracle program. `Main` exports hardness for every NP language.

## Documentation and tidy

README.md states the encoded theorem, exact headline signatures, imports and locked build.
NOTES.md maps the paper to Lean and incorporates API-hp2n-amath.md's detailed signatures.
This record supersedes STATUS-hp2n-amath.md, STATUS-hp2n-arun.md,
STATUS-hp2n-asearch.md, STATUS-hp2n-asearch2.md, STATUS-hp2n-mem.md,
and the adocs progress note.
Those job-local files are removed. AUDIT.md is retained unchanged as historical evidence;
its original paths and prospective obligations predate the completed formalisation.

All Lean modules have a module docstring with a `Paper:` line. Added docstrings to the
remaining public simp API lemmas and wrapped the problem's encoding description.
Corrected `Search/Shortest`'s obsolete claim that reduction runtime was unavailable;
its theorem statements and proofs are unchanged. Final integration tidies `Main` and
`Search/Turing` without changing statements; the root now imports every project module.

Repository-wide reference searches (including `Power2IdealSVP`) found no callers of
`Reduction.pairSup_pos_iff`, `Reduction.not_ModuleYes_zero`, or `Rigidity.M_dominates`;
these elementary unused convenience lemmas were removed. Public paper endpoints and
shared algebra/membership APIs remain available, including uncalled paper-facing results.

## Earlier verification (before final root integration)

The earlier documentation checks exited 0, using the machine-wide build lock:

- Earlier `build Power2ModuleSVPSubsetSum`: successful, 7044 jobs; at that time the root
  imported only Problem. The final full-root check is recorded below.
- Explicit `build` of `Power2ModuleSVPSubsetSum.Main`, `.Search.Witness`,
  `.Search.Shortest`, and `.Rigidity.Bounds`: successful, 7119 jobs, covering the
  changed implementation files. After wrapping a flagged docstring line, the final
  targeted `.Search.Shortest` rebuild passed (7093 jobs) without project warnings.
- `env lean Check.lean`: successful. Exact headline signatures and
  paper-map declaration names elaborate. All 19 axiom reports (decision/runtime,
  correctness/gaps, rigidity/exact norm, witness/recovery, shortest-vector endpoints)
  contain only `propext`, `Classical.choice`, and `Quot.sound`.
- All 36 project Lean files pass the 100-character, module-doc/Paper-reference, and
  forbidden-proof-token scans. README/NOTES links resolve; `git diff --check` passes.

Existing dependency module-system warnings remain; changed project files have no warnings.
No decision, witness-bijection, or Corollary 4.4 obligations remain. Fixed problem
interfaces, dependency sources, and other subprojects are unchanged.

## Corollary 4.4: integrated search and oracle interfaces

Corollary 4.4 is proved in [Search/Turing.lean](../Search/Turing.lean) and exported by
[Main.lean](../Main.lean). The exact statements below use namespace
`Power2ModuleSVPSubsetSum`, with `Turing.MultiTapeTM` and `Cslib.Complexity` open.

```lean
theorem Search.subsetSum_searchReducible_exactShortest :
    SearchReducible Reduction.encSource IdealCVP.encPairRingArgs
      (Search.DecisionAnswer SubsetSum) Search.ExactShortest

theorem moduleSVP_search_npHard :
    HardUnder (fun enc L S => SearchReducible enc IdealCVP.encPairRingArgs
      (Search.DecisionAnswer L) S) @NP Search.ExactShortest

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
        Cslib.OracleComp.queriesWith oracle (program a) = [((), query)])
```

`Search.ExactShortest` takes a module without a radius, encoded by
`IdealCVP.encPairRingArgs`, and returns the actual shortest nonzero vector as two
exact-length signed-binary coefficient lists. Its domain is precisely the wellformed
module inputs. `Search.DecisionAnswer` represents a decision language by its correct bit.
The `HardUnder` statement uses that adapter because `NPHard` itself has a decision target.

The deterministic `Search.shortestProgram` makes exactly one query and tests the
returned vector against the reduction's radius. Its strict `IsOraclePPTOn` certificate
holds against arbitrary stateful word handlers, including malformed or arbitrarily long
replies: it reads only `Search.answerLimit x` bits. Every valid shortest answer fits in
that budget, including signs and list/pair framing; `Search.answer_length_polyBounded`
bounds it by a polynomial in the binary source length. The budget uses `2M + 1` to
cover the radius-zero constant NO case. Correctness holds for every valid shortest-vector
oracle, independent of which shortest vector it returns.

The answer encoding is `Search.encVector := encPair (encList encIntBin)
(encList encIntBin)`. The query uses the existing column convention, unary dyadic degree,
and four signed-binary generator lists. `Search.vectorDecoder` uses the existing total
signed-binary list decoder; postprocessing uses binary-radius coefficient scans.
The exact unary budget is:

```lean
3 * (reduce x).1.1 *
  (2 * ((encNat (2 * (reduce x).2 + 1)).length + 1) + 1) + 1
```

`Search.answerLimit_polytime` computes it in unary, `Search.answer_length_le` bounds
every valid reply, and `Search.answer_length_polyBounded` provides:

```lean
∃ c d : ℕ, ∀ x word, Search.ExactShortest (Search.searchQuery x) word →
  word.length ≤ c * ((Reduction.encSource x).length + 1) ^ d
```

The language-oracle interface `ComputableInPolyTimeWithOracle` is supplemented by
complexitylib's word-reply interface `WordQueryComp Unit Bool`. Its existing `query_take`,
`map_with`, and `preprocess` combinators establish the strict `IsOraclePPTOn` certificate.
`SearchHard` expects a class of search relations; the exported `HardUnder` instead ranges
over NP decision languages through `DecisionAnswer`. No new machine framework or
unproved resource assumption is needed.

### Search implementation verification (hp2n-asearch2)

Successful final targeted build (exit 0):

```sh
lake build \
  Power2ModuleSVPSubsetSum.Search.Turing Power2ModuleSVPSubsetSum.Main
```

The build completed 7905 jobs. `Search/Shortest.lean` also rebuilt successfully
after replacing its outdated runtime-scope docstring. No new warnings in the changed modules;
existing dependency module-system warnings were replayed.

Successful declaration, axiom, and executable check (exit 0):

```sh
lake env lean Check.lean
```

Axiom checks of `exactShortest_domain`,
`subsetSum_searchReducible_exactShortest`, `answer_length_polyBounded`,
`shortestProgram_polytime`, `shortestProgram_correct`, and both Main hardness theorems
report only `propext`, `Classical.choice`, and `Quot.sound`.

Executable checks return `true`/`false` for `( [], 0 )`/`( [], 1 )` with the same actual
shortest vector `([1], [0])`. The bounded oracle program returns the same results; its budgets
are 22 and 16 bits respectively. All changed Lean lines have at most 100 characters;
`git diff --check` passes. No prohibited proof placeholders or new axioms occur.

That implementation changed `Search/Turing.lean` (new), `Main.lean` (exports), and
`Search/Shortest.lean` (docstring only). It made no fixed problem definition, root, package,
or lakefile edits; the subsequent root integration is described below.

## Final documentation integration

The library root imports all project modules, with its module docstring after the imports
as in the other root files. README and NOTES contain the exact search hardness signatures,
encodings, bounded-reply runtime scope, and one-query guarantee. The repository README
lists all five subprojects.

Final commands used the machine-wide build lock:

- `build Power2ModuleSVPSubsetSum`: exit 0, 7912 jobs, including all 37 project modules
  and the root. No project warnings; existing dependency module-system warnings remain.
- `env lean Check.lean`: exit 0. The three documented Corollary 4.4
  signatures elaborate against their actual declarations through the root import.
  `#print axioms` on `moduleSVP_npComplete` and `moduleSVP_search_turing_npHard`
  reports only `propext`, `Classical.choice`, and `Quot.sound` for each.
- Root import coverage, local documentation links, 100-character limits for changed
  Lean files, unchanged theorem/proof bodies, and `git diff --check` pass.

No obligations remain for Paper A.
