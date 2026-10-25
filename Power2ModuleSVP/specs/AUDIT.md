> Historical document: Lean file names and line numbers below refer to the pre-restructure
> layout. See [RENAMES.md](RENAMES.md) for the complete path map. For example,
> `MainFinal.lean` → `Main.lean`, `AnchorRepairPoly2.lean` → `Anchor/FromSeed.lean`,
> `FlatFrontend3Main.lean` → `FlatFrontend/Geometry/Certificate.lean`, and
> `ColoringNative3.lean` → `Runtime/Coloring/Certificate.lean`. Intermediate
> “remaining/open” findings describe the reviewed revision; current results and removed
> interfaces are recorded in [STATUS.md](STATUS.md) and [RENAMES.md](RENAMES.md).

# Independent adversarial audit — p2s-audit

Audited revision: `182db7585418570e205985578afa79a5c708cbf1` (`182db75`),
2026-10-25. Scope: the 36 committed `Power2ModuleSVP/*.lean` files, the
committed root import, and the relevant imported arithmetic and complexity
definitions. The private manuscript was consulted only for comparison;
this report contains independently written summaries. Concurrent uncommitted
anchor/analytic work and concurrent STATUS additions were excluded. All
Lean files present in the audited revision and the Lake configuration
remained unchanged from that revision during validation. Near completion,
concurrent commit `ebdab28` advanced HEAD by adding excluded analytic files;
it did not change those audited Lean files. This job changes only this report.

## Verdict and findings

No critical or high-severity soundness defect was found in the requested
checks. The language definitions describe the stated coefficient-norm
problems, the complexity predicates and source problem are genuine, and
coset completeness has no hidden hypothesis. Module completeness remains
explicitly conditional, as its name and statement indicate.

| Severity | Finding | Suggested action |
| --- | --- | --- |
| Medium — expected incompleteness | The committed library does not prove `RigidAnchorFamilyHypothesis`. Consequently it does not yet prove the unconditional module part of `thm:main`. This is an exposed premise, not a concealed axiom or a defect in the conditional theorem. | Construct one uniform family with its native polynomial-time certificate, then specialize `moduleSVP_npComplete_of`. Preserve the conditional wording until then. |
| Low — build coverage | `lakefile.toml` declares the new library, but `defaultTargets` still lists only `IdealCVP` and `Rank2ModuleSVP`. A plain default build does not select this library. | Add `Power2ModuleSVP` to `defaultTargets`, preserving existing entries, or explicitly include its target in CI. |
| Low — stale documentation | Earlier STATUS sections and `SidonAudit.lean` describe obligations already discharged by the final source/runtime and separation modules. `NormSeparation.lean` still calls its hypothesis interfaces unproved even though `NormFinal.lean` constructs them. Later STATUS entries are more current. | Label these sections as historical and point to the final theorem names; distinguish the remaining anchor obligation from discharged separation/source obligations. |
| Informational — cutoff contract | The anchor hypothesis existentially quantifies a fixed cutoff `2^k0`; it does not assert the manuscript's specific exponent 3600. This is intentionally weaker and sufficient for hardness. | If exact quantitative coverage is desired, additionally export the family with `k0 = 3600`. No change to the current conditional reduction is required. |

No new mathematical error in the compared manuscript claims was identified.
This audit does not prove the missing infinite anchor-family construction
and does not claim a separate line-by-line audit of every analytic lemma in
the manuscript.

## Language and ring fidelity

* `Coeff d` is `Fin d → ℤ`. `Rd d` is the imported
  `AdjoinRoot (X^d + 1)` over integer polynomials, hence the actual quotient
  by that polynomial. `IdealCVP.Cyclotomic.mul` is negacyclic convolution.
  `toQuot_bijective` and `toQuot_mul` establish its coefficient-model
  interpretation for positive degree; this is not an arbitrary replacement
  multiplication. A degree-two computation verifies `X * X = -1`.
* `Dyadic d := ∃ k : ℕ, d = 2^k` includes degree one and excludes degree
  zero. `Dyadic.pos` supplies positivity. Vacuous predicates on `Fin 0`
  cannot make a malformed degree-zero input enter either language.
* `Cube a` requires every integer coefficient to have absolute value at
  most one. `coeffSup` takes the maximum of the coefficients' `natAbs`,
  and `pairSup` takes the maximum over both coordinates.
  `cube_iff_coeffSup_le` and `pairSup_le_one_iff` identify the acceptance
  bounds with these actual norms. Squared norms occur in witness estimates,
  not in the acceptance condition.
* `Signs` requires every coefficient to equal either -1 or 1. `Bits` uses
  0 or 1. `EvenCoeffs` tests integral parity at every coefficient.
  `SignedMonomial` is exactly one of `±X^j`, for `j < d`.
* `CosetInput.WellFormed` requires dyadic degree, both exact list lengths,
  a nonzero generator, and even coefficients of the generator. The
  translation is unrestricted. `CosetYes` is `∃ u, Cube (h + g*u)`,
  equivalent to a cube point whose difference from `h` lies in `gR_d`.
  A zero coset point is correctly allowed.
* `SVPInput.WellFormed` requires dyadic degree, four exact list lengths,
  and `listIndependent = true`. The latter computes the nonzero
  determinant `a₁b₂ - a₂b₁` in the negacyclic ring. The imported
  `listIndependent_iff`, quotient domain theorem, and `independent_iff`
  identify it with independence over the fraction field. Thus singular
  matrices are rejected, rather than treated as arbitrary generating sets.
* `moduleVector a b u v = (a₁u + b₁v, a₂u + b₂v)`: stored pairs are
  columns. This is the image of the imported integral `basisMap`, whose
  range is `basisSpan`. `generalBasis` supplies a free rank-two basis
  when those columns are independent. `ModuleYes` quantifies all integral
  ring multipliers, requires the resulting vector to be nonzero, and tests
  both coefficient cubes. It is exactly the required unit-threshold SVP
  condition in the actual column span.
* Both languages conjoin well-formedness with their semantic YES condition.
  Although `ofList` can pad or truncate lists, malformed lengths are
  rejected before they can exploit that interpretation. The executable
  check specifications and verifier equivalences are proved for all raw
  inputs, not merely promised inputs.
* `encCoset` and `encSVP` reuse the existing injective pair/list encodings:
  unary degree, signed binary integers, and explicit array framing. Unary
  degree charges the explicit output dimension; with the required arrays
  it does not hide a succinct high-dimensional representation. No norms,
  witnesses, or hypotheses are inserted into the encoded instances.
  `CosetBits` and `ModuleSVPBits` are the corresponding image languages;
  strings outside those images are excluded by definition. The exported
  complexity statements use complexitylib's standard encoded-type API.

The committed packing uses the documented zero-padded specialization, rather
than literally repeating the manuscript's geometric factor. Zeros are
permitted in the target cube. `packCoset_correct` proves the equivalence for
this actual construction, and the final reductions instantiate separation;
this specialization does not weaken the target language.

`cosetReduction_alphabet` proves the restricted generator/translation
alphabets from `thm:main`; `moduleReduction_alphabet` adds the zero lower
left column and the sign anchor under the displayed family premise.
`moduleReduction_gap` states attained first minimum one on YES inputs and
a universal coefficient-norm lower bound of two on NO inputs for those
actual stored columns. The alphabet and gap claims therefore refer to the
same reductions used in the completeness proofs.

## Complexity provenance and hidden-premise check

Inspection of the imported definitions confirms:

* `Cslib.Complexity.NP` is existence of a native multitape polynomial-time
  verifier with polynomial-length binary certificates.
* `PolyTimeReducible` requires one total function, a
  `Turing.MultiTapeTM.ComputableTidilyInPolyTime` certificate for the stated
  input/output encodings, and a membership equivalence on every source
  input. `NPComplete` is NP membership together with hardness under that
  reducibility. These are the production definitions in complexitylib,
  not the similarly named abstract test definitions.
* The source is `Cslib.Complexity.ThreeSAT` on `CNF ℕ`: satisfiable formulas
  whose clauses have length at most three, with binary variable labels.
  `ThreeSAT_npHard` comes from the imported Cook–Levin SAT hardness and
  the proved SAT-to-3SAT reduction. The library reuses its proved
  exact-three conversion and then the Boolean source construction.
* `coset_mem_NP` and `moduleSVP_mem_NP` use
  `mem_NP_of_witness`, the actual certified list verifiers, and polynomial
  encoded-multiplier bounds. They impose no anchor or separation premise.
* `threeSAT_polyTimeReducible_coset` packages `cosetReduction`, its native
  time certificate, and its total correctness theorem. The module version
  extracts one fixed family and time certificate from `hJ` and runs it on
  the final unary ring degree.

Explicit `#check @...` checks produced these complete types, with no
additional implicit parameters or typeclass premises:

```lean
Power2ModuleSVP.coset_npComplete :
  Cslib.Complexity.NPComplete encCoset CosetLang
Power2ModuleSVP.moduleSVP_npComplete_of :
  RigidAnchorFamilyHypothesis →
    Cslib.Complexity.NPComplete encSVP ModuleSVPLang
Power2ModuleSVP.coset_mem_NP :
  CosetLang ∈ Cslib.Complexity.NP encCoset
Power2ModuleSVP.moduleSVP_mem_NP :
  ModuleSVPLang ∈ Cslib.Complexity.NP encSVP
```

In particular, `Fact` instances needed by imported quotient/domain lemmas
are constructed locally from well-formedness. They do not occur as
unquantified assumptions on these exports. `normSeparationHypothesis_holds`
is a theorem with no parameters, supplying all three earlier separation
interfaces. There is no remaining norm/source/anchor premise on coset
completeness.

`#print axioms` reported exactly `[propext, Classical.choice, Quot.sound]`
for all four displayed results, `threeSAT_polyTimeReducible_coset`,
`normSeparationHypothesis_holds`, and the imported `ThreeSAT_npHard`.
The Main build also displayed the same list for both hardness results and
`moduleReduction_gap`. This dependency report does not discharge the
explicit `hJ` argument of the conditional module theorem.

The following scan of the committed root and all committed library Lean
files returned no matches (exit status 1, as expected for no matches):

```sh
git grep -n -E '\b(sorry|admit|axiom|opaque|implemented_by|unsafe|native_decide)\b|@\[extern\]' \
  182db75 -- Power2ModuleSVP.lean 'Power2ModuleSVP/*.lean'
```

## Anchor contract and adversarial examples

`Rigid J` says that *every* multiplier whose product with `J` is in the
unit cube is zero or a signed monomial. The implication has the correct
direction and the inclusive bound is one. It does not confuse a bounded
multiplier with a bounded product. For sign `J`, the converse follows
from signed-monomial cube preservation and commutativity; this complete
iff was also checked in scratch Lean. Sign anchors in positive dyadic
degree are nonzero in a domain, so nonzero kernel multipliers cannot hide
in the zero branch.

`RigidAnchorFamilyHypothesis` requires a single total function
`J : ℕ → List ℤ` and one native polynomial-time certificate from unary
degree to binary integer lists. Above a fixed dyadic cutoff it requires
exact length, signs at every coefficient, and precisely this rigidity
property. It asserts neither only pointwise existence nor a different
machine for each degree. The cutoff is not an input-dependent parameter:
it is chosen before the reduction. Every finite cutoff leaves infinitely
many required dyadic degrees, so the condition cannot become vacuous by
choosing a large natural number.

This is the qualitative, uniform content of `thm:rigid-anchor`; allowing
an existential cutoff is weaker than retaining its specific numerical
cutoff. Requiring a total machine on other degrees adds no substantive
anchor obligation: it can return a fixed default outside the specified
regime. No contradictory small-degree demand or accidental stronger
rigidity requirement was found. Finite checks alone cannot prove the full
hypothesis true; its construction remains the explicit open obligation.

Additional kernel-checked scratch proofs established:

* `Rigid [1]` in degree one and `Rigid [1,1]` in degree two. Both vectors
  are sign polynomials.
* The degree-four all-ones polynomial is **not** rigid:
  multiplying by `[1,-1,1,0]` gives `[1,-1,1,1]`, a cube point, while the
  multiplier is nonzero and is not a signed monomial. Thus signs alone
  do not make the rigidity predicate automatically true.
* Both languages are nonempty and have valid NO instances. In degree one,
  `(g,h) = ([2],[0])` is a coset YES instance, while `([4],[2])` is a
  well-formed NO instance: `2+4u` never lies in `[-1,1]`. The identity
  matrix is a module YES instance, while `2I₂` is a well-formed NO
  instance because a nonzero vector in its integral span has a coefficient
  of absolute value at least two. These are proofs of semantic membership
  and nonmembership, not just failures of selected certificates.

## Validation performed

All Lean invocations were sequential. No source file was edited for a test.

1. `lake build Power2ModuleSVP.Main` succeeded. It replayed existing
   style/deprecation warnings; there were no build errors.
2. `lake env lean /tmp/p2s-scratch-audit/Audit.lean` succeeded after scratch
   development. It imported `Power2ModuleSVP.Main`, checked the types and
   axioms above, proved the semantic/rigidity examples, and kernel-checked
   30 finite Boolean tests using ordinary `decide`. Matching `#eval`
   output contained 30 `true` values. No native decision procedure was
   used to prove these examples.
3. `lake env lean Power2ModuleSVP.lean` succeeded, checking the committed
   root import as well as the Main target.

The 14 coset tests covered accepted zero/negative-generator cube points,
valid excessive residue rejection for a selected certificate, zero/odd
generator rejection, zero/nondyadic degree rejection, short/long generator
arrays, a short translation array, short/long certificate arrays, and an
unrestricted large translation in a well-formed input. The 16 module tests
covered identity acceptance, zero vector rejection, an excessive product,
singularity, zero/nondyadic degree, each malformed column coordinate,
short/long multiplier arrays, nonsymmetric column orientation, negacyclic
wraparound, and a nonsingular nonconstant determinant.

Scratch files were removed after validation. The only delivered change is
`Power2ModuleSVP/specs/AUDIT.md`; there are no new library declarations or
changes to the audited definitions/theorems.
