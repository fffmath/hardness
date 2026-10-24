# Concrete assembly audit — p2s-audit3

Date: 2026-10-25. Audited HEAD: `77d12a36c267c82774294ff96ddb114caa6ea621`.
Scope: `MainAssembly.lean`, its two explicit premises, the concrete frontend,
and the target languages and complexity predicates. PLAN, STATUS and both
previous audits supplied context. The private manuscript was consulted for
mathematical comparison; all explanations here are independently written.
Concurrent `FlatFrontend3*` and `ColoringNative3*` work was visible during
review, but is not part of the checked MainAssembly dependency chain and is
not certified by this report. No Lean file was edited, and no commit made.

## Verdict and findings

No critical or high-severity defect was identified. The revised assembly
removes AUDIT2's false universal runtime premise: it selects exactly
`fullColor PartialColoringAlg.partialColor`. The six geometry requirements
are consistent with the manuscript's construction and the actual scan,
including its sampling scale. The concrete full-coloring runtime is
plausibly polynomial on all raw inputs. Neither premise is proved true by
this audit; in particular, kernel checking a conditional implication is
not a consistency proof for its premises. No counterexample or
vacuous-making condition was found.

| Severity | Finding | Concrete action |
| --- | --- | --- |
| Medium — outstanding proof | `MarkedRunGeometryHypothesis` remains an infinite family of substantial analytic assertions about the computed runs. The manuscript's abstract interval lemma alone does not discharge it. | Prove ordered sampling and its error bound for `gridSample`, then transfer seven-cell exclusion, axis avoidance, component counting and coverage to `scanCells`. Keep the theorem conditional until this bridge is checked. |
| Medium — outstanding proof | `FullColoringNativeHypothesis partialColor` concerns every raw input. Logarithmic recursion follows on semantic promised inputs; the program itself only checks strict dimension decrease. | Bound recursion by the original dimension on raw inputs and prove an additive common-denominator invariant independent of the current point's bit size. Combine this with polynomial fixed-row/projector and weight bounds. |
| Low — coverage trap | Relevant `N = seedN d` is odd, while `intervals N` scans only `N / 2` cells. The final half-cell before the right axis is absent from the list. This is compatible with axis avoidance, but must be handled explicitly in `cosine_good`. | Prove a cosine lower bound on the whole axis neighborhood, including the missing half-cell and the axis itself. Do not apply a scanned-cell coverage lemma there. |
| Low — counting trap | Counting components using the unreduced even Chebyshev polynomial without its symmetry gives an avoidable factor two. | Use the polynomial in `cos(2θ)` of degree `stageWidth (stage N)`, or prove the symmetry pairing and axis exclusion explicitly. |

These are exposed proof obligations and proof hazards, not demonstrated
false hypotheses. No definition or program change is presently indicated.

## The six marked-run fields

`FlatFrontend2Runs.lean:110–117` fixes endpoints to the output of
`intervals (seedN d)`. There is no existential freedom to choose favorable
intervals. `markedCell` tests every fine-grid endpoint in a closed coarse
cell; `scanCells` merges consecutive true cells. A pair `(a,b)` represents
the marked cells with indices `a ≤ j < b`, and the associated angular
interval includes both `aπ/N` and `bπ/N`. The existing structural proofs
give positive width, endpoint range and at least one intervening good cell.
The inclusive test at a shared endpoint can mark both neighboring cells;
they merge, rather than create overlapping separate runs.

1. **Width.** `b ≤ a+6` is precisely the six-cell bound in
   `lem:seed-intervals`, not six fine-grid samples. With
   `T = blockShift N`, rescaled cell width is `2Tπ/N`. The selected stage
   makes this very small. Seven consecutive marked cells would supply
   seven small-value witnesses, and alternating witnesses have the
   spacing needed for the manuscript's interpolation/derivative argument.
   Rational sample error must first put each witness below the analytic
   small-value threshold. Shared endpoints do not spoil the spacing of
   witnesses chosen two cells apart. No off-by-one contradiction was found.

2. **Left clearance.** `100 ≤ a` measures distance from zero in coarse
   cells. Odd stage selection gives the nonvanishing normalized wave at
   the axis. Its derivative bound protects all potentially offending
   cells, with the extra cell allowance used in the manuscript's argument.
   This is the intended `100π/N` clearance, not an assertion that samples
   near a typical zero have that separation.

3. **Right clearance.** `2*(b+100) ≤ N` says exactly
   `bπ/N + 100π/N ≤ π/2`. For odd `N` it correctly retains the half-cell
   offset from the axis; replacing the right axis by `floor(N/2)π/N`
   would be a different requirement. Odd stage also protects this axis.
   A sufficient cellwise statement for a marked cell `j` is
   `2*(j+101) ≤ N`. Apply it to the last cell `b-1` of a run.

4. **Count.** `J*2^66 ≤ N` is plausible with precisely this constant.
   Put `w = 2T+2^t-1 = stageWidth t`. Stage admissibility gives
   `w*2^66 ≤ N`. On the quarter circle, write the cosine sum as a
   polynomial in `cos(2θ)` of degree at most `w`. A polynomial sublevel
   set at a positive threshold has at most that many components:
   its two level polynomials have total degree at most `2w`, counting
   boundary zeros with multiplicity, and the endpoints are excluded.
   Ordered samples of each component occupy consecutive fine-grid
   indices, hence consecutive coarse cells; merging can only reduce
   the number. Thus `J ≤ w` gives the field. Equivalently the manuscript
   counts four symmetry copies on the full circle. One must not count
   all copies as the frontend's `J`.

5. **Cosine outside runs.** The requested margin is
   `2⁻²⁵⁰ sqrt N`. The manuscript's stronger unmarked-cell lower bound
   exceeds this through the height/gamma estimates. Folding is legitimate
   for the absolute value of this even-frequency cosine sum, but its
   periodicity and reflection must be linked to the implemented background.
   For angles in the scanned region, an unmarked cell's preceding fine
   sample and derivative/error bounds supply the estimate. For angles
   in the unscanned half-cell and at `π/2`, use axis protection instead.
   Closed run endpoints are inside `runContains`, so the complement
   assertion introduces no impossible strict boundary demand. Even `J=0`
   does not erase this obligation: it then requires a global cosine bound.

6. **Even part.** `6 sqrt N` matches the stable-prefix bound plus the
   removed-block bounds in `lem:seed-intervals`. In the actual program,
   selected frequencies have equal paired coefficients and contribute
   only cosine. Other even frequencies have opposite paired stable-prefix
   signs and contribute the even sine part. Both removed stable blocks
   use the first RS word; the second cosine block uses the second RS
   word. These roles are distinct and agree with the manuscript's
   construction. The actual `background` does not substitute the second
   RS word into the removed stable-prefix block. No incompatible sign,
   normalization or frequency range was found.

## Sampling precision and admissible degrees

`MarkedRunGeometryHypothesis` in `FlatFrontend2Main.lean` quantifies over
every dyadic `d ≥ 2^512`. This is nonempty and unbounded. It excludes
small degrees at which the stage search's default need not be admissible.
Here `d=4N+4`, `N=2^(k-2)-1`, and the selected stage is positive and odd.
The stage and block-fit lemmas apply throughout this range. The later
repair cutoff of at least 3600 is compatible with the earlier cutoff 512;
it does not empty either required family.

The rational grid uses the manuscript's height, fine-grid ratio and exact
threshold comparison. Its hard-coded precision is ample, not an apparent
obstruction to ordered sampling. A useful independent conservative bound
is as follows, using existing scalar-error and raw-parameter bounds:

* `fineError N = 1/(2^80*(N+1)^10)` bounds the reciprocal precision;
  the Machin error is at most four times this, and the Taylor error is
  at most twice this for arguments of magnitude at most `4N`.
* First-half grid arguments have magnitude at most two. The cosine
  approximation error is consequently at most `6*fineError N`.
  Clamping to `[0,1]` cannot increase that error. The exact midpoint,
  endpoint branches and reflection preserve the desired error and symmetry.
* For `N≥1`, the existing coarse bounds imply
  `h≥2⁻²¹²`, `R≤2^220*N`, and `M≤2^220*N²`.
  Hence the target tolerance `gridError N` is at least
  `2⁻⁴⁴²*N⁻⁴`. Throughout the relevant degree range,
  `6*fineError N` is smaller. These inequalities are audit calculations,
  not new Lean lemmas delivered by this job.
* With error at most `1/(4M²)`, adjacent exact cosine samples have
  separation greater than twice the error; their rational approximations
  are strictly ordered. Clamping does not invalidate this reasoning once
  the uniform error and exact endpoint values have been established.

Exact Python fraction calculations at `d=2^k`, for
`k=512,513,514,516,1024`, checked the chosen stage, height, grid size and
the inequality `6*fineError < gridError`. At `k=512`, the selected stage
is 431, `N` has 510 bits, and `R` has 508 bits; the error/tolerance ratio
is less than `2^-3141`. These huge constants explain why actual full scans
at admissible degrees cannot be practical audit experiments. They do not
contradict asymptotic polynomial time. No floating-point sampling of those
degrees was used as evidence for the analytic fields.

A separate Python bookkeeping test exhaustively checked all 8191 Boolean
words of lengths zero through twelve: maximal-run endpoints, coverage and
one-cell separation agreed with the scan convention. This tests indexing
only; it proves none of the six analytic estimates. No scaled numerical
analogue was needed to decide the constant/unit comparisons above.

## Concrete full-coloring runtime

`FullColoringNativeHypothesis partialColor` (`Coloring.lean:204`) requires
one native multitape polynomial-time certificate for the actual full list
function, on every encoded input. It contains neither a universal partial
program quantifier nor an existential choice of an unrelated fast program.
AUDIT2's time-hierarchy construction therefore does not apply.

On entropy-promised inputs, `partialColor_correct` fixes at least half the
coordinates and full recursion has logarithmic depth. On arbitrary inputs,
`fullColorCore` only recurses if the active dimension strictly decreases;
there are at most the original `r` recursive calls. Otherwise it returns
nearest signs. Dimension is bounded by explicit input-list length, so this
linear bound suffices. The naive recursive expression may recompute partial
outputs during assembly, but polynomially many evaluations of a uniformly
bounded partial call still suffice; a stack evaluator can share them.

The significant size facts supporting satisfiability are concrete:

* Canonicalization pads/truncates rows to the explicit dimension. Partial
  input checks reject points outside the cube and negative thresholds,
  returning nearest signs. Thus the old malformed-input payload route is
  blocked. Bad row shapes and threshold lengths are handled by the actual
  wrapper, rather than by a semantic promise on the runtime theorem.
* Prepared rows remove zero rows and thresholds with square above `4r`,
  normalize retained vectors, and keep both signs. There are at most twice
  the original number of rows. Fuel is `2048*r^3`; no loop count depends
  on a rational value's numerical magnitude.
* Weights are rounded to a fixed dyadic mesh. Their denominator precision
  depends on dimensions/fuel; normalized rows and retained thresholds
  bound their per-step growth even without the entropy premise. Polynomial
  magnitude-bit bounds and projector bit bounds still need to be assembled.
* The point affects projection constraints only through its frozen
  coordinate set. It affects a direction's orientation but not the
  direction denominator. `ColoringNativeDenominators` proves the relevant
  invariance and the additive common-denominator recurrence for cube steps,
  including cancellation of direction denominators at boundary steps.
* Across levels the raw matrix entries are merely restricted, and each
  threshold increases by four. Normalization is recomputed from these
  entries, not from increasingly large point coordinates. Consequently
  a direction-factor bit bound can depend polynomially on the original
  matrix/threshold data and dimensions independently of the point's shared
  denominator. Sum the per-step contributions over at most `r` levels;
  do not repeatedly substitute an arbitrary polynomial output-size bound.

An exact rational orthogonal projector has polynomial bit complexity via
rank/Gram determinant bounds; the recursive projection definition alone
does not provide a polynomial evaluation strategy. Cached elimination or
an equal matrix evaluator and a bit bound are required. The existing
denominator lemmas provide a credible route rather than an automatic
runtime theorem. Concurrent native3 helper contracts remain proof work,
not assumptions secretly supplied by MainAssembly.

## Target fidelity and absence of trivialization

`Problem.lean` and `Coefficient.lean` express the intended decision
problems. The imported ring is the coefficient model of
`Z[X]/(X^d+1)` with negacyclic multiplication. Dyadic degree includes one
and excludes zero. `Cube` is the inclusive coefficient bound one.
`ModuleYes` quantifies both integral ring multipliers, requires the
resulting vector to be nonzero, and bounds both coordinates; it does not
merely require nonzero multipliers or use a squared Euclidean threshold.
Stored generator pairs are columns. Exact list lengths and the imported
nonzero determinant test reject malformed and singular module inputs.

`CosetLang` requires a nonzero even generator and exact arrays, then
quantifies `Cube (h+g*u)` with arbitrary integral `u`. Zero coset points
are allowed, as required. Neither language adds an anchor promise or
restricts general accepted inputs to the reduction's coefficient alphabet.

Both encodings reuse the existing framed arrays and signed binary integers;
degree is unary. On explicit well-formed arrays, unary degree costs only
linear additional size. For polynomial equivalence to binary degree on
all inputs, first compare binary degree with actual array lengths and
reject invalid shapes before expanding unary degree. This is a standard
encoding argument, not a separately checked conversion theorem here.

The imported complexitylib definitions use actual native multitape
polynomial time, polynomial binary certificate lengths, and total
deterministic many-one reductions. `NPComplete` is NP membership and
hardness for that reducibility. `Main.lean` obtains coset completeness
unconditionally and module completeness by composing the actual reduction
with a uniform anchor family. The exported alphabet theorem and integral
gap theorem describe those same stored module outputs. MainAssembly's
single completeness conclusion does not itself restate these additional
claims, but they remain available for the selected family.

`FlatFrontendRuntime` certifies the original list programs. Alternate
integer/common-denominator recurrences and capped scans have equality
proofs; they do not redefine `intervals` or assume the desired geometry.
`FlatFrontend2Main.enclosure_of_geometry` discharges the rational enclosure
fields from the geometric certificate and proved precision bounds.
Clamping the second starting point is charged by its approximation
transfer; it does not replace the analytic target by an unrelated function.
Finally, MainAssembly supplies concrete frontend runtime, concrete partial
correctness and proved sine-kernel decomposition, using exactly `hG` and
`hN` for the two remaining steps. No weakened target, contradictory
small-degree condition or extra hidden mathematical premise was found.

## Validation and limits

Sequential checks passed:

* `lake env lean Power2ModuleSVP/MainAssembly.lean`.
* A stdin Lean check importing MainAssembly printed the full theorem type:
  exactly `MarkedRunGeometryHypothesis → FullColoringNativeHypothesis
  partialColor → NPComplete encSVP ModuleSVPLang`.
* `#print axioms` for that theorem, `flatFrontend_runtime`, and
  `coset_npComplete` reported only `propext`, `Classical.choice`,
  and `Quot.sound`. The alphabet and gap theorem types were also checked.
* A source-token scan found only comments and `#print axioms` uses of the
  inspected escape-hatch words; no admitted theorem, new axiom, unsafe
  implementation or native decision proof was found.

Only this Markdown report was written. Temporary scratch was removed.
No dependencies were updated, no shared package files were modified, and
no Lean source or concurrent job's artifact was changed. This is a
read-only mathematical/code review with a checked conditional assembly,
not a formal proof of either remaining premise or an unconditional
module NP-completeness result.
