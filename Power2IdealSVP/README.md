# Power2IdealSVP — CLIQUE to principal ideal SVP

Lean formalisation of [paper B](paper/power2-ideal-svp.pdf),
*Coefficient infinity-norm SVP on principal cyclotomic ideals* (27 October 2026).

For `R_n = ℤ[X]/(X^n + 1)`, with `n` ranging over powers of two, deciding whether
`f R_n` contains a nonzero vector of coefficient maximum norm at most a binary
radius is **unconditionally NP-complete** under deterministic polynomial-time
many-one reductions. The degree varies with the input. The proof includes the
source-label construction, sparse-spin geometry and interaction table, exact
minimum identities, a total executable CLIQUE reduction, native multitape Turing
machine runtime certificates, and NP membership.

## Exact headline statements

Import `Power2IdealSVP`. These signatures are inside namespace `Power2IdealSVP`,
with `Turing.MultiTapeTM` and `Cslib.Complexity` open:

```lean
theorem reduceList_correct (x : Cslib.Complexity.Graph × ℕ) :
    x ∈ Cslib.Complexity.Clique ↔ Runtime.reduceList x ∈ IdealSVPLang

theorem clique_polyTimeReducible_idealSVP :
    PolyTimeReducible (encPair encGraph encNat) encIdeal
      Cslib.Complexity.Clique IdealSVPLang

theorem idealSVP_npHard : NPHard encIdeal IdealSVPLang

theorem idealSVP_npComplete : NPComplete encIdeal IdealSVPLang

theorem idealSVP_mem_NP : IdealSVPLang ∈ Cslib.Complexity.NP encIdeal
```

Correctness is in [Glue/Correctness.lean](Glue/Correctness.lean), the native
certificate `Runtime.reduceList_polytime` in [Runtime/PolyTime.lean](Runtime/PolyTime.lean),
NP membership in [Membership/NP.lean](Membership/NP.lean), and the hardness and
completeness assembly in [Main.lean](Main.lean). Hardness composes complexitylib's
`Clique_npHard` with this certified total reduction; there are no paper-claim hypotheses.

## Encodings and conventions

[Problem.lean](Problem.lean) fixes `IdealInput = ℕ × (List ℤ × ℕ)` and `encIdeal`:
unary degree, signed-binary generator coefficients, and binary natural radius.
Well-formedness requires a dyadic degree, exactly that many coefficients, and a
nonzero generator. Malformed inputs are rejected. Degree one is allowed; radius
zero is allowed and always a NO instance. The paper states positive radii; every
main gadget radius is positive. `IdealYes` asks for an actual nonzero negacyclic
product, bounded using `Power2ModuleSVP.coeffSup`.

The source is complexitylib's `Graph = List ℕ × List (ℕ × ℕ)` with encoding
`encPair encGraph encNat`. Labels and target are binary. Vertices are the distinct
declared labels, in first-occurrence order. Adjacency is symmetric, loops are
ignored, and edges with undeclared endpoints cannot enter the normalized graph.
Repeated labels and edges do not change the answer. CLIQUE asks for exactly the
target number of distinct vertices, equivalently at least that many.

`Runtime.reduceList` uses the gadget only when `3 ≤ h ≤ v`, where
`v = Runtime.vertexCount G`. Otherwise it decides directly: target zero is YES;
target one is YES iff a vertex exists; target two is YES iff a normalized edge
exists; targets above `v` are NO. It returns `(1, [1], 1)` for YES and
`(1, [1], 0)` for NO. Empty graphs and all small vertex counts are covered.
Normalization enumerates vertex positions, never the numerical range of binary
labels or an unchecked binary target.

Coefficients are `Fin n → ℤ`; multiplication is `IdealCVP.Cyclotomic.mul`, not
pointwise multiplication. Integer-index lifts are antiperiodic, including at
negative indices. Sparse spins retain both initial signs. `Spin.Theta` uses rank
alternation; `Ideal.thetaOf` uses prefix sums. [Glue/Theta.lean](Glue/Theta.lean)
proves these definitions equivalent.

## Paper correction and literal size bound

At the antipode `d = n/2`, negacyclicity gives `X^(-d) = -X^d`. Thus the term
`5^j (X^d - X^(-d))` has coefficient **`2 · 5^j`**, as proved by
`Spin.antipodal_guard_coefficient` in [Algebra/SpinBasic.lean](Algebra/SpinBasic.lean).
For `s` forbidden distances the guard magnitude is bounded by `2 · 5^(s−1)`,
rather than the paper's `5^(s−1)`. This adds at most one bit and leaves the
polynomial bit bound unaffected. Both Lean guard constructions already add both
contributions; the mathematical guard and runtime proofs use the corrected term.

The literal dimension estimate in [Runtime/Structure.lean](Runtime/Structure.lean) is:

```lean
-- In namespace Power2IdealSVP.Runtime, with Cslib.Complexity open:
theorem degree_le_vertexCount (x : Graph × ℕ) :
    degree x ≤ 5376 * vertexCount x.1 ^ 9 + 66
```

Here `degree` is the main construction degree, also defined outside the main case;
the dispatched constant outputs instead have degree one. This is a polynomial
bound, not a practical dimension estimate for dense experiments.

The main gadget proves the exact identities (1)–(3), a positive output radius,
and the additive NO gap `r + 2`. The constant NO output has minimum one at radius
zero, so that stronger gap is a main-gadget statement. The result concerns exact
coefficient infinity norm in varying degree. It makes no claim about fixed degree,
canonical or Euclidean norms, or constant-factor approximation. The finite-`p`
obstruction discussed in paper §1.6 is not formalised here.

## Layout and proof route

| File or folder | Contents |
| --- | --- |
| `Problem.lean` | Fixed encoding, validity, arbitrary natural-radius language |
| `Algebra/` | Integral norm estimates, antiperiodic shifts, guard arithmetic |
| `Source/` | Three-term label uniqueness and difference-clique extraction |
| `Spin/` | Guard, signed shifts, short arc, dimers/trimer, endpoint table, equation (1) |
| `Ideal/` | Parity ideal, full signs, domain walls, equations (2)–(3), minimum and gap |
| `Runtime/` | Total graph adapter, executable coefficient lists, size and TM certificates |
| `Glue/` | Source/spin/ideal/list bridges and unconditional total correctness |
| `Membership/` | Multiplier verifier, bounded certificates, native runtime, NP membership |
| `Main.lean` | CLIQUE reduction, NP-hardness, NP-completeness |
| `paper/`, `specs/` | Paper, retained historical audit, plan and final status |

The forbidden-distance guard forces a short odd alternating support to consist
of dimers and one trimer. The endpoint table counts its components; label
extraction recovers a clique. Domain walls turn sparse spins into full signs.
The parity ideal and scalar domination then identify the actual first minimum.
NP verification uses bounded integral multiplier lists and reused Cramer bounds.

[NOTES.md](NOTES.md) maps the paper to declarations and records reuse decisions.
[specs/STATUS.md](specs/STATUS.md) records the final verification;
[specs/AUDIT.md](specs/AUDIT.md) retains the original mathematical audit.

## Build

From the repository root:

```sh
lake build Power2IdealSVP
```

For an axiom check, put `import Power2IdealSVP` followed by
`#print axioms Power2IdealSVP.idealSVP_npComplete` in a temporary Lean file and run
`lake env lean Check.lean`.
The checked theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
