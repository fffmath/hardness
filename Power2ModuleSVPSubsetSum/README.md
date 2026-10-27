# Power2ModuleSVPSubsetSum — binary Subset Sum to rank-two module SVP

Lean formalisation of [paper A](paper/power2svp-subsetsum.pdf),
*ModuleSVP^(2)_∞(Z[ζ_(2^k)]) Is NP-Hard*.

For dyadic `n`, let `R_n = ℤ[X]/(X^n + 1)`. Given a nonsingular rank-two basis over
`R_n` and a natural radius `T`, deciding whether its module contains a nonzero vector
of coefficient maximum norm at most `T` is **unconditionally NP-complete** under
deterministic polynomial-time many-one reductions. The degree varies with the input.
The encoding stores the degree in unary, coefficients in signed binary, and radius in
binary. [Problem.lean](Problem.lean) rejects malformed arrays and singular bases.

## Headline Lean statements

Names are in `Power2ModuleSVPSubsetSum` unless qualified. Import
`Power2ModuleSVPSubsetSum` for all modules, including `Main`, `Search.Witness`,
`Search.Shortest`, and `Search.Turing`. `Main` exports decision and search hardness.
Read the signatures below inside namespace `Power2ModuleSVPSubsetSum`, with
`Turing.MultiTapeTM`, `Cslib.Complexity`, and `Power2ModuleSVP` open.

```lean
moduleSVP_mem_NP : ModuleSVPLang ∈ NP encSVP

reduce_polytime : ComputableTidilyInPolyTime reduce
  (encPair (encList encNat) encNat) encSVP

subsetSum_polyTimeReducible_moduleSVP :
  PolyTimeReducible (encPair (encList encNat) encNat) encSVP
    Cslib.Complexity.SubsetSum ModuleSVPLang

moduleSVP_npHard : NPHard encSVP ModuleSVPLang

moduleSVP_npComplete : NPComplete encSVP ModuleSVPLang

reduce_wellFormed (x : List ℕ × ℕ) : (reduce x).WellFormed

reduce_correct : ∀ x : List ℕ × ℕ,
  x ∈ Cslib.Complexity.SubsetSum ↔ reduce x ∈ ModuleSVPLang

reduce_yes_gap (x : List ℕ × ℕ) (hy : x ∈ Cslib.Complexity.SubsetSum) :
  FirstMinimum (inputA (reduce x)) (inputB (reduce x)) (reduce x).2

reduce_no_gap (x : List ℕ × ℕ) (hn : x ∉ Cslib.Complexity.SubsetSum)
    (a b : Coeff (reduce x).1.1)
    (hne : moduleVector (inputA (reduce x)) (inputB (reduce x)) a b ≠ 0) :
  (reduce x).2 + 1 ≤ pairSup (moduleVector (inputA (reduce x)) (inputB (reduce x)) a b)
```

The runtime certificate is in [Runtime/Reduction.lean](Runtime/Reduction.lean),
the gap and correctness statements in [Reduction/Correctness.lean](Reduction/Correctness.lean),
and the completeness assembly in [Main.lean](Main.lean).
Hardness composes complexitylib's binary `SubsetSum_npHard` with the certified total map.
Repeated weights retain their multiplicities. Zero weights are removed, and empty or
all-zero lists dispatch to fixed degree-one identity YES/NO instances at radii one/zero.

Corollary 4.3 is formalised in [Search/Witness.lean](Search/Witness.lean): the actual
nonzero short vectors biject with satisfying Boolean assignments times signed monomials.
With `Reduction` open, its exact endpoints include:

```lean
Search.witnessEquiv (w : List ℕ) (B : ℕ) :
  (Search.Satisfying w B × Search.SignedUnits (2 * halfDegree w.length)) ≃
    Search.ShortVectors w B

Search.card_shortVectors (w : List ℕ) (B : ℕ) :
  Fintype.card (Search.ShortVectors w B) =
    2 * degree w.length * Fintype.card (Search.Satisfying w B)
```

`witnessEquiv` is noncomputable; executable recovery on supplied multipliers is proved
correct by `Search.recover_correct` and `Search.recover_signed_boolean`.
[Search/Shortest.lean](Search/Shortest.lean) proves shortest-vector existence,
threshold correctness for every shortest answer, and coefficient bounds: `2M` for the
paper gadget and `max 1 (2M)` for the total reduction's radius-zero NO instance.

Corollary 4.4 is proved in [Search/Turing.lean](Search/Turing.lean) and exported by
[Main.lean](Main.lean). The exact statements below use namespace
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

The theorem concerns exact decision SVP in the coefficient maximum norm, with arbitrary
binary radius. Euclidean/canonical norms, fixed degree, rank-one ideals, and a fixed
relative approximation gap are outside this result.

## Proof route and layout

| File or folder | Contents |
| --- | --- |
| `Problem.lean` | Fixed encoding, validity predicate, arbitrary-radius language |
| `Algebra/` | Coefficient l1 bounds, negacyclic adjoint, signed monomial units |
| `Rigidity/` | Opposite-pair filter, skew orthogonality, base-five support rigidity |
| `Reduction/` | Total source normalization, executable gadget, determinant, exact norm, gaps |
| `Membership/` | Binary-radius verifier, Cramer witness bounds, native runtime, NP membership |
| `Runtime/` | Native multitape-TM certificates for primitives and the total reduction |
| `Search/` | Witness bijection/recovery and one-query exact search hardness |
| `Main.lean` | Decision NP-completeness and exact search hardness |
| `paper/`, `specs/` | Paper, retained audit, plan, and verification status |

The filter forces each short multiplier to be zero or a signed monomial. Boolean encoding
then reduces shortness to the exact weighted-sum equality; the constructed vector has norm
`M + 2 * |A - B|`. The determinant proof supplies full rank. Native machine certificates
track unary loop bounds and binary coefficient sizes, and NP membership uses bounded
integer-list multiplier witnesses. Algebra and membership APIs are also reused by
`Power2IdealSVP`; existing lattice infrastructure comes from `IdealCVP` and `Power2ModuleSVP`.

[NOTES.md](NOTES.md) maps paper results to declarations and retains detailed API signatures.
[specs/STATUS.md](specs/STATUS.md) records verification and the completed search reduction;
[specs/AUDIT.md](specs/AUDIT.md) is the historical mathematical audit.

## Build

From the repository root, run:

```sh
lake build Power2ModuleSVPSubsetSum
```

Axiom checks use `lake env lean Check.lean`.
The checked decision, rigidity, gap, and search endpoints use only `propext`,
`Classical.choice`, and `Quot.sound`; see STATUS for the verification record.
