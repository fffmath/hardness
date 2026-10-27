# hp2n-asearch progress

## Proved

- `Search/Witness.lean`: the coefficient gadget has unique multipliers; signed monomials
  have exactly `2n` elements; `witnessVector` is the paper's bijection onto actual nonzero
  short module vectors; `witnessEquiv` packages it; `card_shortVectors` proves `2n N_sol`.
- `recover` is an executable adjoint multiplication followed by coefficient tests.
  `recover_correct` proves satisfaction and reconstruction from every short nonzero
  multiplier pair; `recover_signed_boolean` proves it inverts arbitrary signed Boolean shifts.
- No positivity promise is required: these statements hold for all natural weight lists,
  hence for the requested positive-weight inputs before the total map's preprocessing.
- `Search/Shortest.lean`: shortest vectors exist; every shortest answer for the gadget
  decides Subset Sum by comparison with `M`, has norm at most `2M`, and has every coefficient
  bounded by `2M`. `positiveReduce_search` states this for the stored output.
- `reduce_search_correct` gives the threshold equivalence for the total reduction as well.
  `reduce_shortest_bound` gives `max 1 (2M)`; `reduce_two_M_counterexample` formally shows
  why its radius-zero NO output prevents the uncorrected universal `2M` bound.

## Complexitylib survey and remaining scope

Read INFRA.md, both fixed problem interfaces, API-hp2n-amath.md, the Reduction proofs,
and paper A's Corollaries 4.3/4.4. Searched `.lake/packages/complexitylib` without editing it.

Complexitylib DOES contain `Cslib.Complexity.WordQueryComp`,
`ComputableInPolyTimeWithOracle`, `PWithOracle` (`Classes/Oracle.lean`), and
`FNP`, `FPSearch`, `TFNP`, `SolvesSearch`, `SearchReducible`, `SearchHard`
(`Classes/TFNP.lean`). No `TuringReducible` declaration was found. The existing
`SearchReducible` is between search relations; it does not directly express the paper's
reduction from a decision problem to total shortest-vector search.

Full polynomial-time Turing hardness is not claimed: this project currently lacks a
polynomial-time TM certificate for the gadget construction (no Runtime directory), plus
oracle answer encoding/parsing and the one-query program's runtime certificate. The new
file docstrings explicitly state this scope. No new oracle framework or hypotheses standing
for paper claims were introduced. Coefficient bounds alone are not a formal polynomial
source-encoding-length certificate.

## Verification

Successful targeted build (exit 0):

```sh
LAKE_CACHE_DIR=/tmp/hardness-lake-cache /workspace/shared/bin/lake-locked build \
  Power2ModuleSVPSubsetSum.Search.Witness Power2ModuleSVPSubsetSum.Search.Shortest
```

Log: `/tmp/hp2n-asearch-build2.log`. Both new modules built with no new warnings;
existing dependency module-system warnings were replayed. No prohibited proof placeholders,
lines longer than 100 characters, or whitespace errors in the new sources.

Final locked check passed (exit 0):

```sh
LAKE_CACHE_DIR=/tmp/hardness-lake-cache /workspace/shared/bin/lake-locked env lean \
  /tmp/hp2n-asearch-check.lean
```

Log: `/tmp/hp2n-asearch-check.log`. Axiom inspection of `witnessEquiv`,
`card_shortVectors`, `recover_correct`, `positiveReduce_search`, `reduce_search_correct`,
and `reduce_shortest_bound` reports only `propext`, `Classical.choice`, and `Quot.sound`.
Executable recovery of `[false, true]` after a negative degree-four monomial shift with
wraparound returns `[false, true]`.

No mathematical obligations remain for Corollary 4.3 or the stated mathematical core of
Corollary 4.4. The full runtime/encoding certificates described above remain outside this result.

## Exact main interfaces

All declarations below are in `Power2ModuleSVPSubsetSum.Search`, with the existing
`Power2ModuleSVP`, `IdealCVP.Cyclotomic`, and `Reduction` namespaces open.

```lean
noncomputable def witnessEquiv (w : List ℕ) (B : ℕ) :
    (Satisfying w B × SignedUnits (2 * halfDegree w.length)) ≃ ShortVectors w B
```

```lean
theorem card_shortVectors (w : List ℕ) (B : ℕ) :
    Fintype.card (ShortVectors w B) =
      2 * degree w.length * Fintype.card (Satisfying w B)
```

```lean
theorem recover_correct (w : List ℕ) (B : ℕ) (a b : Coeff (2 * halfDegree w.length))
    (hne : moduleVector (gadgetA w B) (gadgetB w B) a b ≠ 0)
    (hshort : pairSup (moduleVector (gadgetA w B) (gadgetB w B) a b) ≤
      (gadget w B).M) :
    (∑ j : Fin w.length, (w.get j : ℤ) * (if recover w a b j then 1 else 0)) = (B : ℤ) ∧
      a = mul b (booleanWord (length_le_outputDegree w.length) (recover w a b))
```

```lean
theorem recover_signed_boolean (w : List ℕ) (ξ : Fin w.length → Bool)
    (b : SignedUnits (2 * halfDegree w.length)) :
    recover w (mul b.val (booleanWord (length_le_outputDegree w.length) ξ)) b.val = ξ
```

```lean
theorem positiveReduce_search (x : List ℕ × ℕ)
    (v : Coeff (positiveReduce x.1 x.2).1.1 × Coeff (positiveReduce x.1 x.2).1.1)
    (hv : IsShortest (inputA (positiveReduce x.1 x.2))
      (inputB (positiveReduce x.1 x.2)) v) :
    (x ∈ Cslib.Complexity.SubsetSum ↔ pairSup v ≤ (positiveReduce x.1 x.2).2) ∧
      pairSup v ≤ 2 * (positiveReduce x.1 x.2).2
```

```lean
theorem reduce_search_correct (x : List ℕ × ℕ)
    (v : Coeff (reduce x).1.1 × Coeff (reduce x).1.1)
    (hv : IsShortest (inputA (reduce x)) (inputB (reduce x)) v) :
    x ∈ Cslib.Complexity.SubsetSum ↔ pairSup v ≤ (reduce x).2
```

```lean
theorem reduce_shortest_bound (x : List ℕ × ℕ)
    (v : Coeff (reduce x).1.1 × Coeff (reduce x).1.1)
    (hv : IsShortest (inputA (reduce x)) (inputB (reduce x)) v) :
    pairSup v ≤ max 1 (2 * (reduce x).2)
```
