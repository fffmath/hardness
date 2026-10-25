> Historical document: Lean file names and line numbers below refer to the pre-restructure
> layout. See [RENAMES.md](RENAMES.md) for the complete path map. For example,
> `MainFinal.lean` → `Main.lean`, `AnchorRepairPoly2.lean` → `Anchor/FromSeed.lean`,
> `FlatFrontend3Main.lean` → `FlatFrontend/Geometry/Certificate.lean`, and
> `ColoringNative3.lean` → `Runtime/Coloring/Certificate.lean`. Intermediate
> “remaining/open” findings describe the reviewed revision; current results and removed
> interfaces are recorded in [STATUS.md](STATUS.md) and [RENAMES.md](RENAMES.md).

# Frontend and final assembly audit — p2s-audit4

Date: 2026-10-25. Reviewed HEAD: `32fcfe5c786261363d988376f42862c2b43b17de`.
Scope: all 17 committed `FlatFrontend3*.lean` modules, their preparation
interfaces and downstream seed/anchor assembly, and
`MainAssembly.moduleSVP_npComplete_of_fullColoringNative` (the declaration
itself is in namespace `Power2ModuleSVP`). STATUS, AUDIT2 and AUDIT3 were
read first. The private manuscript's `thm:main` and relevant construction
were consulted locally. This report paraphrases the mathematics; no private
source text is reproduced. Concurrent `ColoringNative3*.lean` files were
excluded from certification and left untouched.

## Verdict and severity

No critical/high-severity semantic defect, weakened target, or vacuity was
identified. The new geometry theorem discharges the actual six-field
contract for the original scan. The final theorem is still conditional,
with exactly one explicit premise: native polynomial time of the particular
program `fullColor PartialColoringAlg.partialColor`. That premise is
TRUE-plausible; this review neither proves it nor proves its consistency
from kernel axiom inspection alone.

| Severity | Finding | Action |
| --- | --- | --- |
| Medium — outstanding proof | The final result still assumes `FullColoringNativeHypothesis partialColor`, including runtime on arbitrary raw inputs. | Finish the native certificate, with polynomial projector evaluation and additive coordinate-denominator bounds across all recursion levels. Do not describe the module result as unconditional yet. |
| Low — documentation | MainAssembly's opening comment still calls geometry one of two remaining inputs. Several earlier frontend/seed comments also describe now-discharged obligations as open. | Update comments to distinguish intermediate conditional interfaces from the final one-premise wrapper. |
| Low — optional audit lemma | There is no exported positivity-of-interval-count theorem in the reviewed new frontend. This can initially make the count estimate look vacuous. | Optionally export nonemptiness at admissible degrees using the zero-mean cosine argument below. This is not needed for correctness of the existing assembly. |

AUDIT2 H1's false universal-program premise is **not** used by this
assembly. The old `FullColoringRuntimeHypothesis` declaration remains in
FlatSeedMain as an alternative conditional interface; its presence must
not be confused with a discharged theorem or the selected route.

## Definitions and nondegeneracy

`seedN d` is the natural number `d / 4 - 1`. For dyadic `d ≥ 2^512`,
`dyadic_shape` proves `d = 4*N+4`, and `cutoff_seedN` proves
`N ≥ 2^509`. Thus truncating subtraction and division cannot collapse the
relevant dimension. There are arbitrarily large admissible dyadic degrees;
the cutoff premise is not empty. `seedCosineMargin` is the real number
`1/2^250`, and `seedConstant` is the rational number `1/2^252`, subsequently
cast to the reals. Both are strictly positive, not natural-number divisions.

`intervalCount d` is exactly the length of `intervals (seedN d)`.
`intervals N` scans the list of `N/2` actual `markedCell` results and merges
maximal runs. The marker evaluates the implemented integer Chebyshev
polynomial at the implemented rational samples, using a positive height
and an inclusive threshold. Neither the list nor its count is redefined
in FlatFrontend3. `gridRatio` and `gridSize` are positive for `N>0`.

The fields of `MarkedRunEstimates` have their intended dimensions and
quantifiers: every run has width at most six coarse cells, both axis
clearances hold, `J*2^66 ≤ N`, the actual cosine has a positive lower bound
outside the folded runs, and the actual even sine part is bounded by
`6*sqrt N`. Positive run width and separation are deliberately supplied
by earlier scan lemmas rather than repeated as fields. In particular,
`markedKernelIntervals.width_pos` comes from `intervals_bounds`, not from
a default or assumed empty family. Finite indexing keeps `(0,0)` lookup
defaults unreachable for stored runs.

`SeedKernelIntervals` requires strictly positive widths, widths at most six,
100-cell clearances, and at least one separating cell. Its real intervals
include their endpoints. `GeometryCertificate.left_eq/right_eq` identify
these endpoints with the scan outputs; the concrete constructor uses
exactly `runLeft/runRight`. `FlatSeedGeometryHypothesis` also retains the
actual input equality, cube/nonnegative/entropy conditions, count, folded
angle range, complementary cosine estimate and even bound. Later
coefficient and rounding contracts tie these analytic functions to the
actual assembled word. The generic ability to name analytic functions
does not free this concrete instantiation to choose unrelated ones.

### Can the interval count vanish?

Empty families are legitimately supported by the generic interfaces and
occur for some small degrees outside the cutoff. They do not trivialize
`cosine_good`: for `J=0`, membership in the interval union is false at
every angle, so that field asserts a global strictly positive cosine
lower bound. It does not become a vacuous implication.

In fact `intervalCount d` cannot vanish at any admissible dyadic degree.
Here is an ordinary analytic argument, distinguished from the checked
probe below. `cosine_eq_sum` identifies the cosine as a finite sum of
terms `a_j*cos((2j+2)*θ)`. Each term has integral zero on `[0,π/2]`.
The function is continuous, and `cosine_axes` gives a positive value at
zero. Its integral being zero forces a zero somewhere in that interval
(equivalently, apply Rolle to its finite sine antiderivative). At that
zero, the proved `cosine_good` and the positive margin imply that the
folded angle belongs to a run. Hence a run exists. No numerical scan at
astronomical degree is needed for this argument.

A scratch Lean example kernel-checked the last implication explicitly:
for dyadic `d ≥ 2^512`, the existence of any zero of the actual cosine
implies `intervalCount d ≠ 0`. The analytic existence-of-zero argument
above was not added as a formal lemma during this read-only audit.
Therefore the bound is not explained by an identically empty scan; the
proof really bounds the number of runs.

Even in a hypothetical valid preparation with `J=0`, the downstream
spectral theorem would remain legitimate: the interval union and target
transform are empty/zero, while the complementary cosine estimate protects
the whole circle. `seedIntervalRows N 0 = 0` makes the first coloring
problem empty too, correctly avoiding an impossible positive entropy bound
with zero variables. This branch changes no spectral target. In the
concrete admissible construction the zero-mean argument excludes it.

## Review of the 17-module bridge

* Words/Blocks identify both stored coefficients of each even-frequency
  pair and both finite block evaluations with the Rudin–Shapiro words.
  The selected cosine block uses P then Q; the removed stable-prefix
  blocks both use P. Even/Cosine transfer these identities to the actual
  cosine, even sine part, reduced polynomial and normalized wave.
* Grid/Sampling prove error bounds for the actual Taylor samples,
  including clamping, reflection and endpoint branches. The exact marker
  is equivalent to an inclusive sample comparison, not an abstract root
  predicate. Budget/Parameters transfer marked samples to the small-wave
  witnesses and then to seven-cell exclusion and axis clearances.
* Scan proves actual run coverage, bounds, widths and clearances. The
  proofs use marked cells within stored runs and the first unmarked cell
  after a run, not arbitrary interval data.
* Ordering proves first-half sample ordering despite rational error.
  Count maps each run witness into a closed sublevel component of the
  polynomial in `cos(2θ)`. Two runs in one component would force the
  intervening unmarked cell to be marked. This gives an injection into
  at most `natDegree` components. The reduced degree is bounded by
  `stageWidth`, and stage admissibility gives exactly `J*2^66 ≤ N`.
  No spurious factor two or squarefreeness assumption was found.
* Margin/Coverage/Complement prove the lower bound outside the computed
  runs using a nearby unmarked sample, and handle the terminal unscanned
  half-cell separately via `cosine_right_tail`. This matters because
  admissible `N` is odd. Folding preserves the absolute cosine value.
  The small constant margin is obtained from a positive height estimate;
  it is not set to zero.
* Main assembles all six estimates and uses the existing enclosure and
  preparation bridges. No field is omitted, assumed under an impossible
  premise, or replaced with the final spectral conclusion.

## Spectral seed, anchor and remaining runtime premise

`seed_circle_lower` uses actual full-coloring correctness to obtain both
colorings, then the coefficient evaluation identity and rounding bounds.
Its split is exhaustive: inside a folded interval the sine-kernel target
is large; outside it the actual cosine is large. It concludes a positive
lower bound for the norm of the actual assembled sign polynomial on the
whole circle. `seed_spectral` restricts this to every root of `X^d+1`.
The spectral predicate includes `Signs`, and its positive constant and
positive degree exclude a zero polynomial masquerading as a seed.

`rigidAnchorFamily_of_seed` applies the proved repair runtime and semantic
repair specification. The resulting `Rigid` predicate controls **every**
integral ring multiplier whose product lies in the unit cube, concluding
zero or a signed monomial. Increasing the fixed degree cutoff to include
3600 leaves infinitely many dyadic degrees. Thus the frontend is connected
to a genuine rigid sign anchor, not merely to an unrelated bound or an
empty family of degrees.

The remaining native hypothesis has one field: a native multitape
polynomial-time certificate for the fixed list function
`fullColor partialColor`, with the established rational/list encoding.
It does not quantify over arbitrary partial algorithms. On raw inputs,
the recursive dimension strictly decreases or the program returns nearest
signs; there are at most the initial number of coordinates many levels.
The partial wrapper rejects non-cube starts and negative thresholds.
Retained rows have bounded normalized norm and threshold square at most
`4r`; row counts and fuel are polynomial in explicit dimensions. Rounded
weights and additive common-denominator lemmas provide a credible path to
uniform rational bit bounds. Matrix rows are restricted across recursion
and thresholds only increase by four, so projector bounds can be kept
independent of the growing point denominator. Polynomial evaluation of an
equal projector program, rather than naive repeated recursive expansion,
is still necessary.

These facts support TRUE-plausibility on all raw inputs and block AUDIT2's
malformed-start payload argument for this particular program. They are not
a runtime certificate. Neither termination alone, correctness on entropy
promises, nor a polynomial bound for one call would establish this premise.
No false universal closure assumption is used to fill that gap.

## Fidelity to the end-to-end target

The language uses the imported integral negacyclic coefficient model of
`Z[X]/(X^d+1)`, positive power-of-two degree, and exactly two stored basis
columns. Well-formedness checks exact array lengths and nonsingularity.
`ModuleYes` quantifies both arbitrary integral ring multipliers, requires
the resulting vector to be nonzero, and bounds every coefficient in both
coordinates by one inclusively. This is the specified coefficient maximum
norm decision problem, not a Euclidean or multiplier-bounded substitute.

The coset language separately requires a nonzero even generator and tests
intersection of its translated principal ideal with the unit coefficient
cube, permitting a zero intersection point. Its NP-completeness is already
unconditional. The existing reduction alphabet lemmas give the triangular
basis with the requested generator/translation alphabets and sign anchor;
`moduleReduction_gap` gives attained first minimum one on YES and norm at
least two for every nonzero vector on NO. These auxiliary statements are
available for the same family, although the final NP-completeness wrapper
does not itself restate them.

Encodings are framed explicit arrays with signed binary coefficients and
unary degree. On well-formed arrays the latter has only linear overhead.
Complexity predicates are the imported native deterministic polynomial-time
many-one reductions and NP membership. The zero-padded packing variation
recorded in STATUS, instead of the manuscript's repeated geometric factor,
preserves the target and alphabets. Therefore the checked conclusion
faithfully matches the module decision part of `thm:main`, conditional on
the single remaining runtime premise; the full theorem's alphabet/gap and
coset assertions are supplied by the cited companion results. It is not
yet an unconditional formalization of the entire main theorem.

## Validation and limits

Sequential `lake env lean` checks passed for all 17 `FlatFrontend3*.lean`
source files and `Power2ModuleSVP/MainAssembly.lean`. A separate scratch
probe importing MainAssembly checked the exact function type

```lean
FullColoringNativeHypothesis PartialColoringAlg.partialColor →
  Cslib.Complexity.NPComplete encSVP ModuleSVPLang
```

`#print` confirmed that the native hypothesis has only the selected
program's runtime field. `#print axioms` reported exactly `propext`,
`Classical.choice`, and `Quot.sound` for the final wrapper,
`markedRunGeometryHypothesis_holds`, `flatFrontend_preparation`,
`seed_circle_lower`, and `coset_npComplete`. The probe also checked
positivity of both spectral constants, the dimension lower bound,
nonemptiness of the admissible degree domain, and the implication from a
cosine zero to nonzero interval count. An initial scratch-only dependent
rewrite failed; replacing it with arithmetic elimination made the complete
probe pass. No library change was needed.

A token scan of the 17 new sources and MainAssembly found no `sorry`,
`admit`, new axiom, `unsafe` or `native_decide`. This is a semantic/code
review and kernel-checking audit, not a proof of the remaining runtime
premise or a recheck from source of every transitive imported theorem.
Only this report was written in the repository. Scratch was removed;
no Lean source, dependency, concurrent native3 file or git commit was changed.
