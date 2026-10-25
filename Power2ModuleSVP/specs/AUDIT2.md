> Historical document: Lean file names and line numbers below refer to the pre-restructure
> layout. See [RENAMES.md](RENAMES.md) for the complete path map. For example,
> `MainFinal.lean` → `Main.lean`, `AnchorRepairPoly2.lean` → `Anchor/FromSeed.lean`,
> `FlatFrontend3Main.lean` → `FlatFrontend/Geometry/Certificate.lean`, and
> `ColoringNative3.lean` → `Runtime/Coloring/Certificate.lean`. Intermediate
> “remaining/open” findings describe the reviewed revision; current results and removed
> interfaces are recorded in [STATUS.md](STATUS.md) and [RENAMES.md](RENAMES.md).

# Anchor and flat-seed adversarial audit — p2s-audit2

Audited revision: `aae03f3dde5e43a08ecfc6ead6280af9a8b5464b`, 2026-10-25.
Scope: the committed anchor chain, seed assembly and coloring interfaces;
the token scan covers all 97 committed library Lean files and the root file.
Concurrent `ColoringNative*.lean` and `FlatFrontend*.lean` work was excluded.
The private manuscript was read locally for comparison. All descriptions
below are independently written; manuscript references use lemma labels.

## Verdict and severity-ranked findings

The anchor correctness and runtime chain has no identified semantic defect.
The preparation interfaces have no identified incompatible precision,
irrational-equality, entropy, or cutoff requirement. There is, however, a
high-severity quantifier defect in the generic full-coloring runtime
interface. The existing conditional assembly theorem remains a valid Lean
implication, but its premises should be corrected before pursuing an
unconditional seed theorem.

| Severity | Finding | Concrete fix |
| --- | --- | --- |
| High | `FlatSeedMain.lean:245–249`, `FullColoringRuntimeHypothesis`, requires runtime closure for **every** polynomial-time semantically correct partial-coloring program. This exceeds the paper's particular-algorithm claim and admits a time-hierarchy counterargument. | Select the actual program `P` and require the existing `FullColoringNativeHypothesis P` (`Coloring.lean:204–206`). Alternatively, add a suitable intermediate-size invariant and prove it for the selected algorithm. |
| Low | `RepairRuntimeProbability.lean:4–6` describes arbitrary multipliers as capped, which can suggest a change to the repair probabilities. | Describe fixed-depth local evaluation and its exactness on bounded-support candidates explicitly. No repair probability is clipped. |
| Low | `AnchorRepairPoly.lean:5–7` describes full runtime assembly as outstanding without pointing to its completed downstream proof. | Identify this file as an intermediate layer and reference `RepairRuntimeLoop.repair_polytime` and `AnchorRepairPoly2.lean`. |

### H1: the universal runtime contract cannot be the remaining obligation

`PartialColoringCorrect P` (`Coloring.lean:18–23`) restricts outputs only
on well-shaped inputs with a cube starting point, nonnegative thresholds,
dimension at least 64 and the entropy premise. It does not impose a bound
on denominators or on intermediate recursive input lengths.
`FullColoringRuntimeHypothesis.polytime` nevertheless promises a native
polynomial-time certificate for `fullColor P` on **all raw inputs**, for
every `P` satisfying correctness and a polynomial-time certificate.

The paper's `thm:full-color` uses additive denominator bounds for its
specific partial-coloring walk. A polynomial output-size bound for one
arbitrary call is insufficient: iterating a size bound `L ↦ L²` for
logarithmically many levels gives no fixed polynomial in the original
input length. `Coloring.lean:201–206` already acknowledges this issue in
the comment introducing the program-specific runtime interface.

Large intermediate values alone would not refute an **extensional**
runtime certificate: another machine might compute the same final signs
quickly. There is a stronger obstruction to the universal quantifier:

1. Suppose a correct polynomial-time partial program `P₀` exists, as
   `DeterministicPartialColoringHypothesis` requires. Modify it only on
   inputs with a starting coordinate outside the cube. Testing that
   condition uses rational comparisons, and correctness is unchanged.
2. On those inputs with dimension greater than 128, the modified program
   returns signs in the first `ceil(r/2)` coordinates and an integer
   payload greater than one in the others. The payload stores an original
   binary word and padding; each call squares its bit length. Constructing
   the output remains polynomial in the current input length.
3. `fixedSet` selects the first sign coordinates, so `fullColorCore`
   (`Coloring.lean:36–46`) recurses on the payload coordinates. Start with
   dimension `128 * 2^ceil(log₂(max(2,n)))` for a word of length `n`.
   The initial encoded input has polynomial size. By the last partial
   call, in dimension 128, the padding is long enough for exponentially
   many simulation steps.
4. At that call, run a fixed exponential-time decider for a language
   outside polynomial time, capping the simulation by the available
   payload length on every raw input. Emit its answer as the first sign
   and make the other outputs signs. Each partial call is still
   polynomial-time in its own input size. The answer sign survives full
   recursion at a known output position.

A polynomial machine for this `fullColor P` would decide the chosen
non-polynomial-time language in polynomial time, contradicting deterministic
time hierarchy. Thus, once a correct polynomial-time partial program
exists, the universal runtime contract is not satisfiable as stated.
This counterargument is an ordinary complexity argument, **not a
Lean-formalized time-hierarchy proof**. The kernel-checked conditional
theorem does not establish the consistency or truth of its explicit premises.

The minimal repair is already supported by the API:
`spectralSeedFamily_of_fullColor` accepts one full program and its runtime
certificate. For a selected `P`, use `F := fullColor P`,
`fullColoringCorrect_of_partial P hP`, and
`(hN : FullColoringNativeHypothesis P).polytime`. This composition was
checked in scratch Lean. Change the final generic wrapper to select that
same `P` together with its program-specific full-runtime certificate.
No analytic estimate or anchor interface needs to change. Establishing
that certificate still requires the actual denominator-growth proof.

## Anchor semantics and runtime

* `Rigid J` (`Coefficient.lean:17–19`) quantifies all integral ring
  multipliers `v` for which `J*v` lies in the inclusive unit coefficient
  cube, and concludes `v = 0` or `v` is a signed monomial. This is the
  needed implication for homogenization. The family separately requires
  `Signs J`; signed monomials then do give cube products. It does not
  assume that the multiplier itself is bounded. Dyadic degrees are
  positive, and a sign word in positive degree is nonzero.
* `SpectralSeed` (`AnchorSeedSpec.lean:19–21`) uses the actual coefficient
  evaluation and constant `2⁻²⁵²`, at every root of `X^d+1`. The paper's
  `thm:spectral-seed` gives an all-circle bound, so this root-only
  interface is a faithful weakening, sufficient for screening.
* `SpectralSeedFamilyHypothesis` (`AnchorSeedSpec.lean:26–35`) selects a
  single total list function, a single native polynomial-time certificate
  from unary degree, and a fixed cutoff before quantifying degrees.
  Exact length and signs are required. No finite cutoff removes all
  required dyadic degrees. Allowing an existential cutoff instead of
  fixing 512 weakens the interface without affecting the reduction.
* `repair_rigid_of_cutoff` (`AnchorRepair.lean:677–680`) assumes only
  dyadic degree, `2^3600 ≤ d`, and the spectral seed of the actual input
  representative. Its dimension inequalities, initial potential bound,
  retained spectral bound and candidate exclusion are proved downstream
  of screening; none remains an extra hypothesis. The constants agree
  with `thm:repair` and `thm:rigid-anchor`. Candidate list repetitions are
  counted in the potential and in `candidates_length_le_pow` (`:217`),
  so the list bound is not silently replaced by a distinct-element count.
* The runtime proof evaluates the same potential exactly. The fixed-depth
  `localFraction` is only specified when the variable list fits the depth
  (`RepairRuntimeProbability.lean:203–208`). `eventFraction_spec`
  (`:288–305`) obtains that condition from multiplier support.
  `potentialFraction_spec` (`RepairRuntimePotential.lean:105–119`)
  supplies the proved support bound for every actual candidate. Its
  resulting equality has no raw-input side condition.
* `probabilityParameter_spec` (`RepairRuntimePotential.lean:24–31`)
  preserves the original rational flip parameter. `max 1 d` changes only
  the stored denominator at degree zero, where both rational values are
  zero. Values outside `[0,1]` on inadmissible small degrees are not
  clipped; raw-input equalities remain algebraic. The semantic probability
  argument uses the admissible-degree inequalities separately.
* The unconditional equality chain is `potentialFraction_spec` →
  `nextFlagFast_eq` → `flagsFast_eq` → `repairFast_eq`
  (`RepairRuntimeLoop.lean:35,72,92`). It preserves the comparison tie
  rule. `repair_polytime` (`:99–102`) rewrites by the last equality, so
  its certificate concerns the original `repair`, including malformed
  seeds and degree zero. Fixed support-depth constants can give enormous
  polynomial exponents, but are not runtime input parameters.
* `rigidAnchorFamily_of_seed_of_repair_polytime`
  (`AnchorRepairPoly.lean:112–125`) uses cutoff `max k0 3600`, composes
  the same seed function with repair and preserves uniformity.
  `AnchorRepairPoly2.lean:8–19` discharges the repair runtime premise and
  exports the conditional anchor-family and NP-completeness results.

## Remaining flat-seed and coloring contracts

The following assessment concerns satisfiability by the paper's construction,
not an assertion that the missing frontend or certificates have been proved.

| Contract | Adversarial assessment |
| --- | --- |
| `FlatSeedGeometryHypothesis` (`FlatSeedMain.lean:58–68`) | The interval count is `J ≤ N/2^66`, matching `lem:seed-intervals`. The cosine margin is `2⁻²⁵⁰ sqrt N`, and the even-part allowance is `6 sqrt N`. Rational first input, nonnegative thresholds and entropy are separate requirements. With `J=0`, `seedIntervalRows` removes the rows as well as columns; there is no impossible positive entropy in dimension zero. |
| `FlatSeedIntervalRoundingHypothesis` (`:73–84`) | The exact kernel identity concerns real analytic witnesses, not rational machine approximations. It is an absolute-value identity after folding, consistent with odd-frequency reflection. The second input is required for every first output satisfying the full-coloring specification; the first discrepancy bound controls every such sign output, as the paper needs. |
| `FlatSeedDerivativeRoundingHypothesis` (`:90–110`) | Each exact derivative identity uses a **real** row `v`, with rational matrix entries only required to approximate `v`. The real fractional coefficients are likewise approximated by the rational starting vector. There is no requirement that an irrational sine, integral or square root equal a rational. The degree `2N`, global bound `2N` and reflection identity hold for the intended odd-frequency error; the paper's strict coefficient bound below `3/4` leaves room for the global bound. |
| `FlatSeedCoefficientHypothesis` (`:115–123`) | The identity is required for every sign word, which is correct for Laurent assembly, not only for one computed coloring. The phase has norm one and the three appended monomials cost at most three. `seedAssemble` places opposite signs at paired odd frequencies; the background controls the even positions. No spectral or rigidity conclusion is a field. |
| `FlatSeedPreparationHypothesis` (`:129–133`) | Its real witnesses are existential only in proofs. The executable routines are the already selected `A`, so this does not select a noncomputable algorithm from those witnesses. It remains a substantial geometric/algebraic bridge, including the first-round coefficient estimate, rather than a completed frontend. |
| `FlatSeedFrontendRuntimeHypothesis` (`SeedAlgorithmRuntime.lean:21–25`) | Separate certificates concern the three actual preprocessing functions on every raw input; they do not assume runtime of the composed seed. The paper describes promised inputs, so total implementations must also handle malformed degrees and arbitrary second-input lists with polynomial-time defaults or normalization. No incompatible requirement was found. |
| `DeterministicPartialColoringHypothesis` (`PartialColoring.lean:76–85`) | Faithful to `lem:partial-color`: rational inputs, `r≥64`, entropy `r/64`, at least `ceil(r/2)` sign coordinates and discrepancy `68 λ ||V_i||₂`, with one uniform machine. It is an explicit algorithmic lemma obligation, not the seed or module conclusion. |
| `PartialColoringNativeHypothesis` (`PartialColoringAlgCorrect.lean:221–223`) | Requires runtime of the concrete `partialColor`. Rational norm enclosures retain the factor-two guarantee, weights use a fixed dyadic mesh, and cached projector tables avoid recursive recomputation. An all-raw-input bit bound still needs proof; absence of the entropy promise does not by itself falsify it. Retained thresholds, normalized directions, polynomial step budget and grid weights provide plausible bounds even on that branch. |
| `FullColoringRuntimeHypothesis` | Fails the universal-program audit; see H1. Replace it with the selected-program contract already available. |

Additional numerical checks:

* The second thresholds are rational integers `12+ell`, rather than exact
  irrational expressions. `seed_derivative_threshold` and
  `seed_derivative_entropy` (`FlatSeedRounding.lean:142,157`) prove the
  budget for **all** `16N(N+1)` rows. There is no omitted factor of `N`
  or factor of 16.
* The first thresholds can be rational upper enclosures of the paper's
  real thresholds; upper rounding reduces the entropy sum. The small
  positive enclosure error belongs in the coefficient-bound proof, not
  in an exact equality with the real threshold. Exact rational arithmetic
  also checks the coarse endpoint estimate: using threshold bound 29,
  `π < 22/7` and an added error `1/1000` gives less than `0.741 < 3/4`.
* `seedRoundingError N = 1/(2^20*(N+1)^2)` is less demanding than the
  paper's `N⁻²⁰` precision throughout the required range. The larger
  allowed error is charged explicitly by `seed_rational_row_transfer`
  and `seed_rounding_allowance`; it is not discarded. Derivatives through
  order `N` are normalized before approximation, avoiding exponential
  absolute precision requirements.
* `seedN d = d/4-1`; every relevant dyadic degree is divisible by four,
  so assembly has exactly `d=4N+4` coefficients. The cutoff 512 gives
  ample room for `N≥2^20`, the final center/tail losses and the
  `2⁻²⁵² sqrt d` margin. Repair raises the fixed family cutoff to at
  least 3600. No conflicting small-degree requirement was found.

No additional mathematical error in the inspected manuscript arguments was
identified. H1 is a stronger Lean-interface claim than the manuscript's
specific-algorithm runtime argument. This audit does not certify every
analytic lemma of the private construction.

## Token scan and validation

The following scan was run against the named revision, excluding concurrent
untracked files:

```sh
git grep -n -E '\b(sorry|admit|axiom|opaque|implemented_by|extern|unsafe|native_decide)\b' \
  aae03f3dde5e43a08ecfc6ead6280af9a8b5464b -- 'Power2ModuleSVP/*.lean' Power2ModuleSVP.lean
```

Its only match is the word `axiom` in a comment at
`PartialColoringAlgCorrect.lean:94`. No forbidden declaration, tactic,
implementation override or foreign-code attribute was found.

Lean checks were sequential, using `lake env lean` without creating a Lake
project or modifying dependencies:

* `Power2ModuleSVP/AnchorRepairPoly2.lean`: passed.
* `Power2ModuleSVP/FlatSeedMain.lean`: passed.
* `Power2ModuleSVP/AnchorRepair.lean`: passed.
* `/tmp/p2s-scratch-audit2/Audit.lean`: passed, including the corrected
  program-specific assembly. It checks the exact
  exported types and proves unrestricted `repairFast` equality and that
  unconstrained coloring rows permit arbitrary precision in the fractional
  half. The hierarchy counterargument itself is not formalized there.

`#print axioms` for `repair_rigid_of_cutoff`, `repair_polytime`,
`rigidAnchorFamily_of_seed`, `potentialFraction_spec`, `repairFast_eq`
and `spectralSeedFamily_of` reported only
`[propext, Classical.choice, Quot.sound]`. This does not discharge explicit
hypothesis arguments, particularly H1. This job changes only this report;
no library theorem or implementation was edited. All audited Lean sources
were unchanged during validation. Audit scratch was removed after checking.
