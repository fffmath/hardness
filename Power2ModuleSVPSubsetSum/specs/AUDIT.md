# Mathematical audit of paper A

**Paper:** *ModuleSVP^(2)_∞(Z[ζ_(2^k)]) Is NP-Hard*, supplied as `papers/A.pdf` (15 pages), with extracted text `papers/A.txt`.  
**Purpose:** check the mathematical reduction and identify the exact obligations for a later Lean 4 formalisation. No Lean implementation is included.  
**Audit date:** 2026-10-28. All paths below are relative to `/workspace/shared/jobs/hardness-power2-new` unless specified otherwise.

## Verdict and how to read this report

The reduction is mathematically sound on its stated domain: **a nonempty list of strictly positive integer weights, a nonnegative binary target, and a degree chosen by the reduction that is always at least four**. No blocking mathematical gap was found in the multiplier filter, Boolean encoding, equality test, determinant argument, size estimate, NP membership argument, or one-call exact-search reduction. This is an audit conclusion, not a machine-checked theorem. The finite computations below are additional checks, not a replacement for the general proofs.

The main theorem concerns explicitly represented coefficient arrays and the **coefficient maximum norm**. It does not establish Euclidean hardness, canonical-embedding norm hardness, rank-one ideal hardness, hardness for a fixed degree, or a fixed relative approximation gap. The power-of-two degree varies with the input. These distinctions matter when stating the formal theorem.

Findings use the requested classification:

| Class | Finding | Consequence |
|---|---|---|
| **(a) Blocking mathematical errors/gaps** | None found in the claimed theorem on the stated domain. | The algebraic correctness theorem is a reasonable formalisation target. |
| **(b) Fixable edge cases / transcription issues** | Extracted text loses the parentheses and absolute values in the introductory lattice encoding and obscures the ceiling/exponent in the degree formula. | Use the PDF formulas reproduced below. The PDF itself has the correct formulas. |
| **(b) Domain boundaries** | Zero weights and an empty list are not source instances as defined. The filter is stated for `n ≥ 4`, although the target language permits `n = 1, 2`. | Zero weights may be removed; handle an empty list by a fixed YES/NO output. Do not instantiate the filter at `n = 1, 2`. Positive weights with `B = 0`, `B > W`, repeated weights, and `s = 1, 2` need no repair. |
| **(c) Lean obligations** | Signed wraparound, integer digit separation, finite-sum sign arguments, coefficient-basis equivalence, minimum existence, explicit encodings, bit bounds, and polynomial-time verification/recovery. | Make these separate lemmas and complexity theorems; do not silently replace them with computation on examples. |
| **(c) External complexity dependency** | Binary Subset Sum NP-hardness is cited rather than reproved in A. | Import a proved theorem with the exact source encoding, or formalise a reduction from an established NP-complete problem such as 3SAT. This is a normal dependency, not a gap in the paper's mathematical proof. |

The report is organised as a proof-step audit. It restates the definitions, equations, hypotheses and conclusions before checking their uses; references such as “(3.2)” are the paper's equation numbers. Part III gives executable checks, finite search bounds, and actual results. The formalisation plan distinguishes pure integer-array mathematics from bit-complexity and Turing-machine claims.

### Scope and source checks

The supplied PDF and text were read throughout. PDF pages 2, 10 and 11 were rendered to resolve the ordinary-lattice formula, the ceiling in (4.1), and the signs in the equality test and the expansion of `H`; the images and a layout-preserving extraction are retained under `out/auditA/`. The introductory survey and bibliography do not enter the proof. This audit does not independently certify the novelty or correctness of every cited recent preprint.

For the upstream complexity dependency, [Karp's original paper, reprinted with an introduction by its author](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/Karp.pdf) supplies the classical NP-completeness framework and the equality version called KNAPSACK. The exact positive-weight, nonnegative-target source used here must still be matched to the chosen formal library; a normalization and an optional direct 3SAT route are given below. No claim about the reduction in A depends on the recent lattice-hardness references in its introduction.

---


## Coverage index

| Paper location | Definition or claim audited | Detailed location below |
|---|---|---|
| pp. 1–2 | Norm, module, first minimum; Theorem 1.1; classical lattice (1.1) | Parts I–II |
| pp. 3–5, (2.1)–(2.7), Definition 2.1 | Quotient ring, antiperiodic extension, monomial units, adjoints, coefficient matrix, input language | Part I §§1–2 |
| p. 5, Proposition 2.2 | NP membership and certificate length | Parts I–II |
| p. 6, Lemma 2.3 | Membership and multiplier recovery | Parts I–II |
| p. 6, §2.4 | Exact source language and binary size measure | Parts I–II; Part IV |
| pp. 6–7, Lemma 3.1 | Filter polynomials, pair norm, adjoints, vanishing coefficients, norm bound | Part I §3 |
| p. 8, Lemma 3.2 | Support rigidity | Part I §4 |
| pp. 8–9, Proposition 3.3 | Multiplier rigidity and computability | Part I §5 |
| pp. 10–11, (4.1)–(4.6), Lemma 4.1 | Degree, all polynomials/constants, Boolean equivalence, exact norm identity | Part II |
| pp. 11–13, Proposition 4.2; decision proof | Validity, exact gap, output size, deterministic reduction | Part II |
| p. 13, Corollary 4.3 | Witness bijection and inverse | Part II |
| p. 14, Corollary 4.4 | One-call search hardness and bounded oracle answer | Part II |
| p. 14, §5 | Scope: coefficient max norm, rank two, no relative gap claim | Verdict and Part IV |
| pp. 14–15, references | Source hardness is a dependency; other references are contextual | Verdict and Part IV |


## Part I. Definitions, algebra, and multiplier filter

### 1. Exact definitions and assumptions

1. A power of two means `n=2^r` for some natural number `r`; in particular `n≥1`. In the title's notation `k=r+1≥1`, so `n=2^(k−1)` and `2n=2^k`. An algebraic number field is a finite extension of `Q`; its ring of integers consists of elements satisfying monic polynomials over `Z`. Put `ζ_(2n)=exp(πi/n)`, `K_n=Q(ζ_(2n))`, and `R_n=Z[X]/(X^n+1)`, identified with `Z[ζ_(2n)]`. The latter is the full ring of integers of `K_n`. Each element has unique representative `f=Σ_(0≤i<n) f_i X^i`, `f_i∈Z`. The ring has characteristic zero, is an integral domain, and is free over `Z` with basis `1,X,…,X^(n−1)`. Write `coeff_n(f)=(f_0,…,f_(n−1))^T`; `coeff_(2n)(f,g)` concatenates `coeff_n(f)` followed by `coeff_n(g)`.
2. For such an array define `||f||_1=Σ_i |f_i|`, `||f||_∞=max_i |f_i|`, and `⟨f,g⟩=Σ_i f_i g_i`. The same array formulas make sense over the real numbers. On a pair use `||(f,g)||_∞=max(||f||_∞,||g||_∞)`. For a real linear operator `A` on the coefficient space, its adjoint `A†` is defined by `⟨Ax,y⟩=⟨x,A†y⟩` for all arrays `x,y`; it is skew-adjoint when `A†=−A`.
3. For integer `i`, write its Euclidean division by the positive integer `n` as `i=qn+r`, `0≤r<n`, and set `f̃_i=(-1)^q f_r`. Thus `f̃_(i+n)=-f̃_i`. This is not the periodic extension. In a mechanisation, define the sign from the parity of `q`, avoiding negative powers in the integers.
4. Explicit negacyclic convolution is `(fg)_i=Σ_(0≤j≤i) f_j g_(i−j) − Σ_(i<j<n) f_j g_(n+i−j)` for `0≤i<n`. The Euclidean quotient in the extension is integer floor division, including for negative indices (for example `−1=(−1)n+(n−1)`, so `f̃_(−1)=−f_(n−1)`). Multiplication by `X^d`, for any integer `d`, obeys `(X^d f)_i=f̃_(i−d)`. Negative powers are legitimate because `X^n=-1`, so `X` is a unit. For `1≤j<n`, `X^(−j)=-X^(n−j)`; `X^0=1` has inverse itself.
5. `U_n={εX^j : ε∈{−1,1}, 0≤j<n}` consists of signed monomial units. Multiplication by each is a signed permutation of the coefficient positions, preserving both coefficient norms and nonzeroness.
6. The involution is `f*=f(X^(−1))`. It is additive and multiplicative, fixes integers, and squares to the identity. The multiplication operator by `f` has transpose/adjoint multiplication by `f*`, for the coefficient inner product.
7. A lattice with integer column basis `B∈Z^(N×d)` and linearly independent columns is `{Bz:z∈Z^d}⊆R^N`, of rank `d`. It is full rank when `N=d`. For positive rank its maximum-norm first minimum is `lambda_(1,∞)=min_(0≠v∈Λ(B)) max_(1≤i≤N)|v_i|`. Existence follows from the nonempty set of positive integer norms and well-ordering; no compactness argument is needed here. The target lattices always have rank `2n>0`; a rank-zero lattice would require a separate convention for the minimum.
8. Given `G∈R_n^(2×2)` with `det G≠0`, put `Λ(G)={G(a,b)^T:a,b∈R_n}`. It is free of rank two over `R_n`; its coefficient lattice has the `2n` integer basis vectors `X^j g_1, X^j g_2`, `0≤j<n`.
9. For `f∈R_n`, the multiplication matrix has entries `C_n(f)_(i,j)=f_(i−j)` when `i≥j`, and `−f_(n+i−j)` when `i<j`. Its `j`th column is the array for `X^j f`.
10. The integer coefficient basis is the block matrix `Ĝ=[[C_n(G_11),C_n(G_12)],[C_n(G_21),C_n(G_22)]]`. For all `a,b`, `coeff_(2n)(G(a,b)^T)=Ĝ·(coeff_n(a),coeff_n(b))^T`. `det G≠0` is equivalent to `Ĝ` being nonsingular over `Q`.
11. Definition 2.1 is an ordinary language, not a promise problem: valid inputs have `n` a positive power of two, four explicit arrays of length `n`, `det G≠0`, and a nonnegative binary integer `T`; malformed inputs are rejected. The answer is whether `∃v∈Λ(G), v≠0 ∧ ||v||_∞≤T`. Exact search takes valid `(n,G)` and returns such a vector of minimum norm.
12. Binary Subset Sum in §2.4 has `s≥1`, strictly positive integer weights `w_1,…,w_s`, nonnegative target `B`, and asks for `ξ∈{0,1}^s` with `Σ_j w_j ξ_j=B`. Empty subsets and repeated weights are permitted. Its size measure is `ℓ=s+bits(B)+Σ_j bits(w_j)`, `bits(t)=max(1,ceil(log_2(t+1)))`. The strict positivity assumption means weights zero are outside this source language, although many later algebraic formulas remain meaningful for zero weights.
13. Section 3 assumes `n=2m`, `m≥2`, and `n` a power of two; hence its smallest degree is `n=4`. Define
   - `D=1+X^m`;
   - `S^(d)=X^d−X^(−d)=X^d+X^(n−d)` for `1≤d<m`;
   - `K=Σ_(d=1)^(m−1) 5^(d−1) S^(d)`.
   The opposite pairs are `{j,j+m}`, `0≤j<m`. A pair is occupied by `b` exactly when `(b_j,b_(j+m))≠(0,0)`.
14. Proposition 3.3 takes arbitrary `H,V∈R_n` and defines the actual integer norms
   `F=||H||_1`, `ν=||V||_1`, `ρ=||DK||_1`,
   `L=F+ν+1`, `M=2(Lρ+ν)+F+1`, and `Q=MD+LDK`.
   Here `ρ` is the actual norm, not merely its upper bound `5^(m−1)−1`; confusing these two does not reproduce the paper's construction exactly. All these scalar parameters are nonnegative integers, and `L,M` are strictly positive.

### 2. Section 2, proof steps checked

#### §2.1: number field, coefficient identities, adjoints

* For `n=2^r`, `(X+1)^n+1` has constant coefficient `2`, leading coefficient `1`, and all intermediate coefficients divisible by `2`. Its constant coefficient is not divisible by `4`. Eisenstein at `2`, followed by invariance of irreducibility under translation, proves `X^n+1` irreducible over `Q`. The intermediate binomial divisibility is a lemma to supply rather than a consequence of an arbitrary `n` being even. For `n=1`, the translated polynomial is `X+2`; the criterion is valid, or linear irreducibility can be used directly. Identification with the full ring of integers is a cited cyclotomic theorem and is not required for the array/filter reduction itself.
* The antiperiodic rule follows from increasing the Euclidean quotient by one. For any integer shift, reducing the exponent modulo `n` gives exactly the sign in `f̃_(i−d)`. This accounts correctly for negative indices and multiple wraps.
* Each shift matrix is a signed permutation, and its transpose is the inverse shift. Expanding `f` linearly therefore gives `⟨fg,h⟩=⟨g,f*h⟩` (Eq. 2.4). All signs and multiplication order are correct.
* The product estimate in Eq. 2.4 is an inequality, although the following prose calls it the “second identity.” The triangle inequality gives `||fg||_∞≤Σ_i |f_i|·||X^i g||_∞=||f||_1||g||_∞`. Calling it an identity is harmless wording, not a mathematical error.
* If `K*=−K`, symmetry and adjointness imply `⟨b,Kb⟩=−⟨b,Kb⟩`. The conclusion is valid over `Z` as well as `R`, because these rings have no nonzero 2-torsion. It would not follow over characteristic two. The converse assertion that skew-adjoint multiplication implies `K*=−K` uses faithfulness of the regular representation: apply the equality of multiplication operators to `1`.

#### §2.2: module basis and Proposition 2.2 (NP membership)

**Statement.** The language in Definition 2.1 belongs to NP.

* `G` is invertible over the field `K_n`, because its determinant is nonzero. Thus `G(a,b)^T=0` forces `a=b=0`, proving freeness and uniqueness of multipliers.
* The coefficient basis spans by the integer basis `1,…,X^(n−1)`. An integer relation among its columns converts into a kernel vector for `G`, proving independence.
* The displayed formula for `C_n(f)` has exactly the correct negative sign for `i<j`: the contributing coefficient is `f_(n+i−j)` and the exponent has wrapped once.
* Conversely, if `G` is singular over `K_n`, choose a nonzero kernel vector in `K_n^2`. Every coordinate of a field element has rational coefficients in the power basis, so its concatenated array is a nonzero rational kernel vector for `Ĝ`. This justifies the nonsingularity equivalence. It uses the degree-`n` field basis, not an assertion that the original kernel vector already has integer coefficients.
* A certificate `(v,t)∈Z^N×Z^N`, `N=2n`, is checked by `0<||v||_∞≤T` and `Ĝt=v`. Completeness follows by choosing any desired short lattice vector and its unique integer multipliers.
* For `A≥1` bounding `|Ĝ_ij|`, put `U=max(A,T,1)`. Every entry of a Cramer replacement matrix has absolute value at most `U`, and every column has Euclidean norm at most `sqrt(N)U`. Hadamard gives `|det Ĝ_i(v)|≤N^(N/2)U^N`. Since `det Ĝ` is a nonzero integer, its absolute value is at least one. Hence `|t_i|≤N^(N/2)U^N` and each multiplier coordinate has `O(N(log(N+1)+log(U+1)))` bits. The total length of `t` is consequently `O(N^2(log(N+1)+log(U+1)))`, polynomial in explicit input length. The vector `v` contributes `O(N log(T+2))` bits. The paper does not accidentally claim the per-coordinate estimate as the total length.
* The bound also works when `T=0`; however no witness is then accepted, because no nonzero integer vector has zero maximum norm.
* Input validity is polynomial time, including array lengths, binary signed-integer parsing, power-of-two testing, and exact nonsingularity. Because all four arrays are explicit, `n` is at most a constant multiple of input length. It is legitimate to use algorithms polynomial in `n`; this would fail for a succinct polynomial representation.
* For Lean, a weaker bound `|det A|≤N! U^N≤(NU)^N`, obtained directly from the determinant permutation expansion, avoids real square roots and Hadamard while giving the same polynomial bit-length conclusion. Bounding a determinant is not by itself a formal proof that Gaussian elimination has polynomial bit complexity; the latter algorithmic fact is a separate dependency.

#### §2.3: Lemma 2.3 (membership and multiplier recovery)

**Statement.** For a valid `(n,G)` and an explicitly given `v∈R_n^2`, module membership and, on membership, the unique multiplier pair can be computed in polynomial bit time.

* Solve `Ĝt=coeff_(2n)(v)` over `Q`. Nonsingularity gives a unique rational solution. This vector is integral if and only if `v` is in the integer lattice; split it into two length-`n` blocks to get the ring multipliers.
* Exact or fraction-free elimination with divisibility tests has the claimed bit complexity. Cramer's rule bounds rational numerators and a common denominator by determinants with entries bounded by `max(A,||v||_∞,1)`; reduced representations can only shrink these bounds. This correctly accounts for the bit length of the supplied `v` as part of the input.
* All statements remain valid for `n=1` and `n=2`. These cases are not excluded by the problem definition and require no use of Section 3.

#### §2.4: source problem

The Boolean verification is polynomial time using binary multiplication by a bit and binary addition. NP-completeness is an external complexity theorem, not proved in this paper. A full end-to-end Lean hardness theorem needs either a formalised positive-weight binary Subset Sum hardness result or an additional reduction from a previously formalised NP-complete language (for example 3SAT). It is logically sufficient to import that exact source theorem; the new reduction need not itself begin at 3SAT.

### 3. Lemma 3.1: all identities and bounds

**Precise statement.** Under `n=2m`, `m≥2` and the definitions above, for every integer coefficient array `b`,

`||Db||_∞=max_(0≤j<m)(|b_j|+|b_(j+m)|)≥||b||_∞`,

`D*D=2`, `K*=−K`, `⟨Db,DKb⟩=0`,

`K_0=K_m=(DK)_0=(DK)_m=0`, and `||DK||_1≤5^(m−1)−1`.

**Audit.**

1. Since `X^(2m)=−1`, `(X^m b)_j=−b_(j+m)` and `(X^m b)_(j+m)=b_j`. Therefore the pair map for `D` is `(c,e)↦(c−e,c+e)`.
2. The scalar identity `max(|c−e|,|c+e|)=|c|+|e|` is correct over `R`. It can be proved by the paper's nonnegative-square argument, or more simply by a sign split on `c,e`. Combining all opposite pairs proves the norm identity, and each original coefficient is bounded by its pair sum.
3. `X^(−m)=−X^m`, hence `D*=1−X^m` and `D*D=1−X^(2m)=2`. This is scalar multiplication by the integer `2`, not the polynomial coefficient array having two entries equal to one.
4. `S^(d)*=−S^(d)`, so `K*=−K`. Then `⟨b,Kb⟩=0` and `⟨Db,DKb⟩=⟨b,D*DKb⟩=2⟨b,Kb⟩=0`.
5. For `1≤d<m`, the indices `d` and `2m−d` are distinct, belong to disjoint index intervals, and avoid `0,m`. No cancellation occurs in `K`; each of these entries is the positive integer `5^(d−1)`. This proves the vanishing entries. Applying the same pair map at `j=0` proves the vanishing entries of `DK`.
6. `||K||_1=2Σ_(d=1)^(m−1)5^(d−1)=(5^(m−1)−1)/2`, and `||DK||_1≤2||K||_1=5^(m−1)−1`. The division by two is exact because the numerator is even.
7. As a further check (not needed in the proof), for even `m` the exact norm is
   `ρ=||DK||_1=5^(m−1)−3·5^(m/2−1)`.
   Indeed at pair `j`, `1≤j<m`, the two positive `K` entries are `a=5^(j−1)` and `b=5^(m−j−1)`, so the contribution is `|a−b|+|a+b|=2max(a,b)`. The central `j=m/2` contributes `2·5^(m/2−1)` and the other terms occur in symmetric pairs. This gives `ρ=2` for `n=4` and `ρ=110` for `n=8`, within the asserted bounds `4` and `124`.

### 4. Lemma 3.2: support rigidity

**Precise statement.** If `b∈R_n`, `||Db||_∞≤1`, and for every `0≤j<m` with `(b_j,b_(j+m))≠(0,0)` both `(Kb)_j=0` and `(Kb)_(j+m)=0`, then either `b=0` or there are `ε∈{−1,1}` and `0≤t<n` with `b=εX^t`.

**Audit.**

1. Lemma 3.1 yields `|b_j|+|b_(j+m)|≤1`. Integrality implies an occupied pair is exactly one of `(1,0),(-1,0),(0,1),(0,-1)`; unoccupied pairs are `(0,0)`. Thus all coefficients and all antiperiodic coefficients lie in `{-1,0,1}`.
2. At any position `i`, `(S^(d)b)_i=b̃_(i−d)−b̃_(i+d)`, an integer in `[-2,2]`. The sign before the second term is negative even though the coefficient representation of `S^(d)` has two positive entries; the negative-index shift formula is what resolves that apparent discrepancy.
3. If `(Kb)_i=0`, the equality is `Σ_(d=1)^(m−1)5^(d−1)c_d=0`, each `c_d∈[-2,2]`. Reducing modulo `5` gives `5∣c_1`, which forces `c_1=0`. Divide the remaining equality by `5` and repeat. This is valid balanced-digit uniqueness; no carry can cancel a nonzero lowest digit. A clean Lean induction removes one digit from a finite list at each step.
4. Choose any occupied pair `{j,j+m}`. At both positions all shift tests vanish. For each `1≤d<m`, the test `d` at `j` is `b̃_(j−d)−b̃_(j+d)=0`. The test `m−d`, which is also in `[1,m−1]`, at `j+m` is
   `b̃_(j+d)−b̃_(j+2m−d)=b̃_(j+d)+b̃_(j−d)=0`.
   The last sign uses `b̃_(j+2m−d)=−b̃_(j−d)`; the period is `2m=n`, not `m`.
5. The two equations imply `2b̃_(j−d)=2b̃_(j+d)=0`, hence both are zero in `Z`. No division operation in `Z` is required.
6. The offsets `d` and `−d` for `1≤d<m`, modulo `2m`, cover exactly the residues other than `0,m`. Translation by `j` is a permutation of residues. Therefore all coefficients outside the selected opposite pair vanish. The antiperiodic sign does not affect whether a coefficient is zero.
7. The selected pair already had absolute mass one, so the whole array has exactly one coefficient equal to `1` or `−1`. This proves the conclusion.
8. **Central case `d=m/2`:** when `m` is even, `m−d=d`, but the tests are evaluated at two different positions, `j` and `j+m`. They still provide the required difference and sum. They are not duplicate equations. In the smallest case `m=2`, these are the only two tests and correctly eliminate the other opposite pair.
9. The lack of a test at `d=m` is intentional. That offset is the selected opposite partner, whose simultaneous occupancy was already excluded by the mass-one condition.

### 5. Proposition 3.3: multiplier rigidity and bit sizes

**Precise statement.** Under the Section 3 assumptions and parameter definitions in item 14 above, for all `b,z∈R_n`,

`||z||_∞≤1 ∧ ||Hz−(Q+V)b||_∞≤M  ⇒ b=0 ∨ b∈U_n`.

Moreover the arrays and scalar parameters are computable deterministically in time polynomial in `n` and the maximum binary coefficient length of `H,V`.

**Audit of inequalities and logic.**

1. Put `t=||Db||_∞∈Z_≥0`. Lemma 3.1 gives `||b||_∞≤t`. The convolution bound gives `||Hz||_∞≤F`, `||DKb||_∞≤ρt`, and `||Vb||_∞≤νt`.
2. Since `M>0`, `||MDb||_∞=Mt`. Rearranging `Q=MD+LDK` and using the premise gives
   `Mt≤M+F+(Lρ+ν)t`, or `(M−Lρ−ν)t≤M+F`.
3. The leading scalar is exactly `M−Lρ−ν=Lρ+ν+F+1>0`. If `t≥2`, then
   `2(M−Lρ−ν)≤M+F`, hence `M≤2(Lρ+ν)+F=M−1`, impossible. The `+1` in `M` is exactly sufficient; no asymptotic inequality substitutes for it. As `t` is an integer, `t<2` implies `t≤1`.
4. Put `r=Db`, `v=DKb`, and `e=Vb−Hz`. From `t≤1`, `||e||_∞≤ν+F=L−1`. The second premise says coefficientwise `|Mr_i+Lv_i+e_i|≤M` (the original expression is its negative).
5. At a nonzero `r_i`, the pair map implies `r_i=±1`, whence
   `M+Lr_i v_i+r_i e_i=r_i(Mr_i+Lv_i+e_i)≤|Mr_i+Lv_i+e_i|≤M`.
   Thus `Lr_i v_i≤−r_i e_i≤|e_i|≤L−1<L` and `r_i v_i<1`. Since `r_i v_i` is an integer, it is at most zero. When `r_i=0`, the product is zero directly.
6. Skew-adjointness gives `Σ_i r_i v_i=0`. Every term is nonpositive, so every term is zero. At a nonzero `r_i`, this implies `v_i=0`.
7. Every occupied pair of `b` produces two nonzero entries of `r`, so both corresponding entries of `v=DKb` vanish. Set `w=Kb`. The pair equations `0=w_j−w_(j+m)` and `0=w_j+w_(j+m)` imply `w_j=w_(j+m)=0`. The displayed divisions by two in the paper are justified over `Q` or `R`; a Lean proof over `Z` should instead add/subtract the equations and cancel the nonzero factor `2`.
8. Lemma 3.2 applies. If `t=0`, the pair formula already forces `b=0`; the proof does not need to separate this case, but no occupied pair is then selected inadvertently.
9. If input coefficients have at most `τ≥1` bits in absolute value, `F,ν≤n·2^τ`, giving `O(τ+log n)` bits for these sums and `L`. The largest `K` coefficient is `5^(m−2)`, with `O(m)=O(n)` bits, and `ρ≤5^(m−1)−1` has `O(n)` bits. Products `Lρ`, and hence `M`, have `O(n+τ+log n)` bits. Because `||D||_∞=1` and `||DK||_∞≤ρ`, `||Q||_∞≤M+Lρ`, giving the same bit bound for every `Q` coefficient. The norm sums, signed shift, successive multiplication by five, scalar products, and additions require polynomially many operations on polynomial-length integers. The numerical values can be exponential in `n`; their binary representations are polynomial.


## Part II. Reduction, correctness, and complexity

### Exact statements and verification

#### Theorem 1.1 and the target language

For a positive power of two `n`, put `R_n = Z[X]/(X^n+1)`, represented by arrays `Fin n → Z`. A valid input consists of four explicit length-`n` coefficient arrays forming `G ∈ R_n^(2×2)`, `det G ≠ 0`, and an integer radius `T ≥ 0`; integers are signed binary encoded. Define `Λ(G)={G(a,b)^T : a,b∈R_n}` and the coefficient maximum norm of a pair to be the maximum absolute value of its `2n` coefficients. The language asks for a nonzero member of norm at most `T`; malformed encodings are rejected. The corresponding search problem takes valid `(n,G)` and outputs any nonzero member with minimum norm. The theorem claims deterministic polynomial-time many-one NP-completeness of the language and deterministic polynomial-time Turing NP-hardness of the search relation.

The words "power of two" must mean `n=2^r`, `r∈N`, including `n=1`; `n=0` is invalid. The ring degree is part of the input. No claim of hardness for any one fixed `n` follows. Explicit arrays imply `n` is at most the encoded input length; a parser must check their lengths before allocating according to a malicious binary `n`.

The first minimum exists: `Λ(G)` contains a nonzero integer vector (a column), and the set of nonzero maximum norms is a nonempty subset of positive integers. This elementary fact avoids an analytic discreteness/minimum existence development.

#### Classical introductory embedding, equation (1.1)

For `s≥1`, positive weights `w_j`, and `B≥0`, let

```
W=Σ_j w_j,  C=2(W+B+1),
L_cl = {(2a-b·1_s, b, 2(Σ_j w_j a_j-Bb)+Cc)
        : a∈Z^s, b,c∈Z}.
```

Its square integer basis has block rows `[2I_s,-1_s,0]`, `[0,1,0]`, `[2w^T,-2B,C]`; its determinant is `2^s C`. If a nonzero vector has norm at most one, then `b∈{-1,0,1}`. At `b=0`, `|2a_j|≤1` forces `a=0` and `|Cc|≤1`, with `C≥2`, forces `c=0`, contradiction. Negate to `b=1`; `|2a_j-1|≤1` forces Boolean `a_j`. The last coordinate is even, since `C` is even, and hence equals zero. As `0≤Σw_j a_j≤W`,

`|2(Σw_j a_j-B)|≤2(W+B)<C`,

so its equality to `-Cc` forces `c=0`, then the subset equality. Conversely a satisfying Boolean word with `(b,c)=(1,0)` gives norm exactly one; its `b` coordinate is one. This proof is sound at `B=0`, `B>W`, and `s=1`. The PDF contains the required absolute-value bars. This classical embedding is explanatory and is not needed as an intermediate reduction in the main theorem.

#### Source problem, section 2.4

The source language consists of encodings of `s≥1`, a list of `s` **positive** binary integers, and a **nonnegative** binary target. YES means

`∃ ξ∈{0,1}^s, Σ_j w_j ξ_j=B`.

The empty subset is permitted; repeated weights retain their distinct positions. Let

`bits(t)=max(1,ceil(log_2(t+1)))` for `t≥0`,
`ell=s+bits(B)+Σ_j bits(w_j)`.

This measures the usual list encoding length up to framing conventions. Positivity of the weights is part of the source language, not an unmentioned promise. `B=0` is a valid YES input. Positive-target Subset Sum suffices for NP-hardness. Invalid source encodings map to one fixed target NO instance.

#### Proposition 2.2: NP membership

Given a valid target input, write `N=2n`, let `Ghat∈Z^(N×N)` be its coefficient matrix, and let `A≥1` bound its absolute entries. A certificate is a pair of integer arrays `(v,t)∈Z^N×Z^N` with `0<||v||∞≤T` and `Ghat t=v`. To show polynomial certificate size, choose any YES vector `v`. Its unique integral multiplier `t` satisfies Cramer's rule

`t_i=det(Ghat_i(v))/det(Ghat)`.

For `U=max(A,T,1)`, each replacement matrix column has Euclidean norm at most `sqrt(N) U`, so `|det(Ghat_i(v))|≤N^(N/2) U^N`. The denominator is a nonzero integer and has absolute value at least one. Thus each `t_i` has `O(N(log(N+1)+log(U+1)))` bits; `v` uses `O(N log(T+2))` bits. These are polynomial in explicit input size. Verification is binary integer multiplication/addition and comparison. `T=0` has no witness. Validity is checked by parsing, a power-of-two test, and exact nonsingularity of `Ghat`.

No bound on the *numerical value* of `T` is needed. A Lean proof can replace Hadamard by the looser elementary Leibniz bound `N! U^N≤N^N U^N`, which has the same polynomial bit bound and avoids real Euclidean norms. Determinant validity checking needs a polynomial-bit-time algorithm (e.g. fraction-free elimination), not merely a computable determinant definition.

An optional NP-verifier design avoids implementing polynomial-time nonsingularity elimination in this first milestone: include integer witnesses `(S,d)` with `d≠0` and `Ghat S=d I` in addition to `(v,t)`. These equations certify nonsingularity over `Q`; on valid matrices choose `S=adjugate(Ghat)` and `d=det(Ghat)`. Leibniz bounds give polynomial bit lengths for both. The verifier then uses only bounded integer matrix arithmetic, parsing, and the vector conditions. The equivalence between coefficient nonsingularity and the paper's nonzero ring determinant remains a mathematical bridge. Multiplier recovery still requires a polynomial-time exact solve.

#### Lemma 2.3: membership and multiplier recovery

For valid `(n,G)` and arbitrary integer coefficient vector `v`, solve `Ghat t=coeff(v)` over `Q`. The solution is unique and is integral exactly when `v∈Λ(G)`. Splitting its two length-`n` blocks recovers `(a,b)`. Exact rational or fraction-free elimination with divisibility checks is polynomial bit time. Numerators/denominator obey determinant bounds with the bit length of `v` included. Arbitrarily long `v` is allowed, so the running time is measured in the total input length `(n,G,v)`; later corollaries additionally bound `v` relative to the original source size.

#### Exact construction, equations (4.1)–(4.3)

Let `m=2^ceil(log_2(max(2,s)))`, the least power of two at least `max(2,s)`, and `n=2m`. Then `m≥2`, `s≤m`, and `2s≤n≤4s`. More precisely, if `s≥2` then `s≤m<2s`; for `s=1`, `(m,n)=(2,4)`.

In `R_n`, define

```
D = 1+X^m,
S^(d) = X^d-X^(-d)                  (1≤d<m),
K = Σ_(d=1)^(m-1) 5^(d-1) S^(d),
u = Σ_(j=1)^s X^(j-1),
h = Σ_(j=1)^s w_j X^(-(j-1)),
E = 2B-W,
H = (1-X^m)h = D* h,
V = E(1-X^m) = E D*,
F = ||H||_1,
nu = ||V||_1,
rho = ||DK||_1,
L = F+nu+1,
M = 2(L rho+nu)+F+1,
Q = M D+L D K,
G = [[2H, -Hu-Q-V], [2M, -M u]].
```

Here `D*=1-X^m`, all scalars are constant polynomials, negative powers use `X^n=-1`, and `rho` is the *computed exact norm*, not a substitution by its upper bound. The output is `(n,G,M)`. Avoid a Lean identifier collision: the polynomial `u` and the scalar `nu` are different quantities. All `F,nu,rho,L,M` are natural/nonnegative integer quantities; `E` is a possibly negative integer.

#### Lemma 4.1: Boolean encoding and exact norm

For every `a∈R_n`,

`||2a-u||∞≤1` iff `a=a_xi=Σ_(j=1)^s ξ_j X^(j-1)` for a unique Boolean word `ξ`.

For such `ξ`, write `A=Σ_j w_j ξ_j` and `z_xi=2a_xi-u`. Then

`||(H z_xi-Q-V, M z_xi)||∞ = M+2|A-B|`.

Proof audit:

1. At `0≤i<s`, `|2a_i-1|≤1` is equivalent over integers to `a_i∈{0,1}`. At `s≤i<n`, `|2a_i|≤1` is equivalent to `a_i=0`. This proves both directions and uniqueness. Since `s≥1`, `||z_xi||∞=1`.
2. The Laurent expression `f=h z_xi=Σ_(j,k=1)^s w_j(2ξ_k-1)X^(k-j)` has exponents in `[-s+1,s-1]⊆[-m+1,m-1]`. A negative exponent `-r`, `1≤r<m`, gives `-X^(2m-r)`, at a position strictly above `m`; nonnegative exponents give positions below `m`. Thus only `k=j` contributes at zero, and nothing contributes at `m`: `f_0=2A-W`, `f_m=0`. This remains correct for `s=m`; the forbidden endpoints `±m` never occur.
3. The opposite-pair action of `D*` is `(f_i,f_(i+m))↦(f_i+f_(i+m),f_(i+m)-f_i)`, so `(H z_xi)_0=2A-W`, `(H z_xi)_m=-2A+W`.
4. Since `(DK)_0=(DK)_m=0`, `Q_0=Q_m=M`; `V_0=E`, `V_m=-E`. Therefore the two relevant coefficients are `-M+2(A-B)` and `-M-2(A-B)`. Their maximum absolute value is `M+2|A-B|`, using `M≥0`.
5. For `i∉{0,m}`, `MD` and `V` have coefficient zero, so the other first-coordinate coefficients have absolute value at most `F+Lrho<M`. The difference is exactly `M-(F+Lrho)=Lrho+2nu+1>0`.
6. The second-coordinate norm is `||M z_xi||∞=M`. Consequently the two selected coefficients determine the whole norm, even if `A-B` is very large. There is no hidden assumption `B≤W`.

#### Proposition 4.2: validity, exact separation, size

The constructed `G` has nonzero determinant. For YES source instances, `lambda_1,∞=M`; for NO source instances, `M+1≤lambda_1,∞≤2M`. The construction has deterministic polynomial bit complexity and output length `O(ell^2)`.

Proof audit, with every main numerical step:

1. Expanding `H` gives

   `H=w_1-w_1 X^m-Σ_(j=2)^s w_j(X^(m-j+1)+X^(n-j+1))`.

   The two ranges are `[m-s+1,m-1]⊆[1,m-1]` and `[n-s+1,n-1]⊆[m+1,n-1]`; they are disjoint and avoid `0,m`. When `s=1`, both sums are empty. Therefore `F=2W`; also `nu=2|E|`.
2. Expanding the determinant gives `det G=2M(Q+V)`. Since `(Q+V)_0=M+E` and `M>nu=2|E|`, this coefficient is strictly positive. Thus `Q+V≠0`; multiplication by the positive integer `2M` does not annihilate its positive constant coefficient. Hence the determinant is nonzero. The paper invokes the domain property here, which is sufficient; for this final scalar multiplication the coefficient argument already suffices. The domain is needed for the general equivalence between nonzero module determinant and nonsingular coefficient matrix.
3. For arbitrary multipliers, put `z=2a-ub`. Then `G(a,b)^T=(Hz-(Q+V)b, Mz)`. If this is nonzero of norm at most `M`, its bottom coordinate gives `||z||∞≤1` because `M>0`. Multiplier rigidity yields `b=0` or a signed monomial.
4. At `b=0`, `z=2a`, and `||z||∞≤1` forces `a=0`, contradicting nonzeroness. Thus `b` is a unit in `U_n={±X^j:0≤j<n}`.
5. Multiplying the whole vector by `b^(-1)` preserves its coefficient norm; commutativity gives `b^(-1)G(a,b)^T=G(ab^(-1),1)^T`. The second coordinate and Lemma 4.1 force `ab^(-1)=a_xi`; the exact norm is `M+2|Σw_j ξ_j-B|`. A bound by `M` therefore forces the subset equality, and the norm equals `M`.
6. Every satisfying `ξ` gives `G(a_xi,1)^T` of norm `M`. Its second coordinate has norm `M>0`, proving nonzeroness. Thus YES has first minimum exactly `M`. NO has no nonzero vector of norm at most `M`, so integer norms give the lower bound `M+1`.
7. The first column `(2H,2M)` is nonzero and has norm exactly `2M`, because `||H||∞≤F<M`. This proves a finite upper bound in all cases and the NO upper bound.
8. For bit size put `A0=W+B+1`, `beta=ceil(log_2(W+B+2))`, `q=5^(m-1)≥5`. The paper's inequalities hold:

   `F+1=2W+1<2A0`,
   `nu=2|2B-W|≤4B+2W<4A0`,
   `0≤rho<q`,
   `L=2W+2|2B-W|+1≤4W+4B+1<4A0`.

   Substitution gives `M=2Lrho+2nu+F+1<8A0 q+10A0≤10A0 q<16A0 q`. The middle inequality uses precisely `q≥5`: `10A0≤2A0 q`. Since `A0<2^beta`, `log_2 M<4+beta+(m-1)log_2 5`, so `M` has `O(m+beta)` bits.
9. `||Hu+Q+V||∞≤F+M+Lrho+nu<2M`, because `||u||∞=||D||∞=1` and `M-(F+Lrho+nu)=Lrho+nu+1>0`. Also `||2H||∞≤2F<2M`, the bottom-right coefficients are at most `M`, and the bottom-left constant is `2M`. Hence every basis coefficient has absolute value at most `2M`.
10. There are `4n` explicit coefficients; radius and degree add less size. The output takes `O(n log(M+2))=O(s(s+beta))` bits. Both `s` and `beta` are `O(ell)`: for instance `W≤s·2^(max bits(w_j))` and `B<2^(bits(B))` yield `beta≤O(log(s+1)+max bits(w_j)+bits(B))`. Hence `O(ell^2)` holds.
11. Successive doubling computes `m`; repeated multiplication by five computes all coefficients of `K`. Sums of absolute values compute exact `F,nu,rho`. All polynomial products can be computed by naive `O(n^2)` coefficient convolutions and negacyclic reduction. The arrays have polynomial length and all intermediate coefficients have polynomial bit length. Ordinary binary arithmetic therefore gives deterministic polynomial bit time. There is no need to enumerate values up to `M`, `W`, or `B`.

An optional array-only shortcut to validity of the constructed coefficient matrix is useful for Lean. If `(Q+V)b=0`, then

`M||Db||∞≤(Lrho+nu)||b||∞≤(Lrho+nu)||Db||∞`.

Because `M>Lrho+nu` and `||Db||∞≥||b||∞`, this forces `b=0`. A vector in the kernel of `G` has bottom row `Mz=0`, hence `z=0`; the first row then forces `b=0`, followed by `a=0`. Thus the constructed coefficient matrix is injective without invoking cyclotomic irreducibility. To identify the target family as modules in the cyclotomic ring and handle all general inputs, retain a separate quotient/field bridge.

#### Decision completion

Map malformed source inputs to `(n,G,T)=(4,2I_2,1)`, a valid NO instance because its coefficient lattice is `2Z^8`, with first minimum two. A fixed YES instance, if needed for preprocessing, is `(4,I_2,1)`. Proposition 4.2 and Proposition 2.2 combine with source NP-hardness to establish Theorem 1.1. The invalid-input map must be part of the total reduction on bitstrings rather than relying on a promise.

#### Corollary 4.3: exact witness bijection

Let `Sol={ξ∈{0,1}^s:Σw_j ξ_j=B}`. The function

`Sol × U_n → {v∈Λ(G):v≠0 and ||v||∞≤M}`,
`(ξ,b) ↦ b G(a_xi,1)^T`,

is bijective, and its inverse is polynomial bit time. Thus the number of nonzero vectors in the radius-`M` cube is exactly `2n·|Sol|`.

The norm and membership of every image follow from Lemma 4.1 and the signed-monomial unit action. Given a short vector, uniqueness of module multipliers and the soundness proof yield its unique `b∈U_n` and `ab^(-1)=a_xi`, proving surjectivity. Equality of two images implies equality of multiplier pairs `(ba_xi,b)=(b'a_xi',b')`; the second entries give `b=b'`, then unit cancellation and coefficient equality give `ξ=ξ'`. The `2n` signed monomials are distinct because their coefficient arrays are distinct. Recovery uses Lemma 2.3, identifies the unique nonzero coefficient of `b`, applies the inverse signed shift to `a`, and reads the first `s` entries. The input short vector has `O(n log(M+2))=O(ell^2)` bits. The reasoning works when `B=0`, for repeated weights, and for all tiny `s` allowed by the source.

#### Corollary 4.4: search hardness

A deterministic reduction with one oracle call constructs `(n,G,M)` from a source input, queries an oracle that returns **any** exact shortest nonzero coefficient vector for `(n,G)`, computes its norm, and accepts exactly when the norm is at most `M`. Every possible oracle answer works. Its norm is at most `2M` by the known first-column vector, so its `2n` signed binary coefficients occupy `O(n log(M+2))=O(ell^2)` bits. Thus reading and comparing the answer is polynomial time; no unbounded-output loophole remains. YES answers also give a source witness via Corollary 4.3.

This is a search-relation Turing reduction, not a language many-one reduction to a function. There is no need to prove a general SVP decision-to-search reduction. If formalising the search claim, specify a solver oracle for the relation, require correctness on all valid inputs, and show the reduction succeeds for every shortest-vector choice. Do not call the search relation NP-complete merely because its decision counterpart is.


## Part III. Exact computational audit

### Files and reproducibility

The primary runnable audit is `out/auditA/exact_checks.py`, requiring Python 3 and NumPy. It writes `exact_results.json`, including parameters, exact coefficient-matrix determinants, all search bounds/counts, and a shortest-vector witness for each instance. `exact_checks.log` retains the full-grid run summary. `README_checks.md` explains the finite search in detail. Run from the job directory:

```bash
python3 out/auditA/exact_checks.py
python3 out/auditA/exact_checks.py --quick --output out/auditA/quick_results.json
python3 out/auditA/exact_checks.py --supplemental
```

The implementation uses Python integers for construction, negacyclic arithmetic, exact determinant evaluation by fraction-free Bareiss elimination, and direct verification of each reported witness against the full coefficient basis. Search batches use signed 64-bit NumPy integer matrix arithmetic after an explicit bound proves that all tested products, sums, differences, and norms fit. It uses no floating-point lattice reduction, singular-value estimate, or approximate shortest-vector solver.

### Why the finite search is complete

This is a search of a bounded ball in the actual lattice, not a search restricted in advance to the claimed signed monomials. Put `P=Q+V`, take any radius `R≥0`, and write the lattice vector in its basis-multiplier form

`G(a,b)^T=(Hz-Pb,Mz)`, `z=2a-ub`.

The bottom row implies the integer bound `||z||∞≤k=floor(R/M)`. Let `t=||Db||∞`. The elementary opposite-pair identity gives `||b||∞≤t`. Applying the triangle inequality to the first row, without using either support rigidity or multiplier rigidity, gives

`Mt ≤ R+Fk+(Lrho+nu)t`,

and therefore

`t ≤ tmax=floor((R+Fk)/(M-Lrho-nu))`.

The denominator is the positive integer `Lrho+nu+F+1`. Thus every possible `b` lies in the finite set in which each opposite pair `(b_j,b_(j+m))` has `|b_j|+|b_(j+m)|≤tmax`. There are exactly `1+2tmax(tmax+1)` possible integer pairs, so this set has `[1+2tmax(tmax+1)]^m` arrays. For each such `b`, the search enumerates every `z∈[-k,k]^n` satisfying the necessary and sufficient coefficientwise parity condition

`z+ub ≡ 0 (mod 2)`.

It then reconstructs `a=(z+ub)/2∈Z^n` and evaluates both rows of `G(a,b)^T`. Conversely every enumerated parity-compatible pair comes from such an integer multiplier `a`. The parameterization is injective: the constructed coefficient basis is nonsingular, checked by an exact nonzero integer determinant for each instance. The zero vector is excluded. Consequently this enumeration includes **every** nonzero lattice vector of norm at most `R` and gives its exact minimum and count, if the ball is nonempty.

At `R=M`, `k=1` and `tmax=1`: the search still considers all `5^m` opposite-pair choices for `b`, including all possible multiple-occupancy supports. At `R=M+1`, `k=1` and `tmax=2`, so all `13^m` pair choices are considered. In the primary NO cases a directly verified Boolean candidate has norm `U=M+2`; searching the entire ball of radius `U-1` proves the exact minimum is `U`. More generally the code searches up to one below a directly verified upper witness and takes the exact minimum inside that ball if one exists. It never concludes minimality merely from the norm of a normalized Boolean candidate.

### Main grid and outcomes

The grid consists of every ordered weight list of lengths `s=1,2,3` with entries in `{0,1,2}`, and every target `0≤B≤W+1`. It includes repeated weights, empty-subset witnesses, `B>W`, all-zero lists as an explicitly marked extension, `s=m` at `s=2`, and both output degrees `n=4,8` (coefficient lattice dimensions 8 and 16).

| Quantity | Exact result |
|---|---:|
| Total instances | 180 |
| Valid positive-weight source instances | 79 |
| Additional zero-weight extension instances | 101 |
| YES instances (59 strictly positive-weight; 65 extension) | 124 |
| NO instances (20 strictly positive-weight; 36 extension) | 56 |
| Bounded multiplier pairs evaluated, across all balls | 31,255,688 |
| YES first minima | All exactly `M` |
| NO first minima | All exactly `M+2` |
| Failures of the claimed separation | 0 |

For every instance the entire radius-`M-1` ball contained no nonzero lattice vector. The radius-`M` ball contained exactly `2n·Nsol` nonzero vectors, where `Nsol` was independently computed by exhaustive Boolean Subset Sum, and was empty in NO cases. These checks also test the witness-count corollary, beyond just decision equivalence.

Representative records from the JSON:

| Weights | `B` | `n` | `F` | `nu` | `rho` | `L` | `M` | `Nsol` | Exact `lambda` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `(1)` | 0 | 4 | 2 | 2 | 2 | 5 | 27 | 1 | 27 |
| `(1)` | 2 | 4 | 2 | 6 | 2 | 9 | 51 | 0 | 53 |
| `(1,1)` | 1 | 4 | 4 | 0 | 2 | 5 | 25 | 2 | 25 |
| `(1,2,1)` | 2 | 8 | 8 | 0 | 110 | 9 | 1989 | 2 | 1989 |
| `(2,2,2)` | 1 | 8 | 12 | 8 | 110 | 21 | 4649 | 0 | 4651 |
| `(0,0,0)` — outside stated source domain | 1 | 8 | 0 | 4 | 110 | 5 | 1109 | 0 | 1111 |

For example, the first record uses `D=1+X^2`, `K=X+X^3`, `DK=2X^3`, `u=h=1`, `E=-1`, `H=1-X^2`, `V=-1+X^2`, and

`G=[[2-2X^2, -27-27X^2-10X^3], [54,-27]]`.

The empty subset gives multipliers `(a,b)=(0,1)` and vector `(-27-27X^2-10X^3,-27)`, of norm 27. All other candidates of smaller norm were excluded by the complete search.

### Other algebra checks and limits of the evidence

The primary script checks arbitrary signed shifts across multiple wraps, inverse monomials, involution, and multiplication-matrix transpose identities at `n=1,2,4,8,16`. At `n=4,8,16` it checks `D*D=2`, skewness of `K`, its forbidden coefficients and its norm bound. At `n=4,8` it exhausts all `25` and `625` pair-mass-at-most-one arrays, respectively, checks the pair-norm and orthogonality identities, and verifies that the vanishing hypothesis of support rigidity holds for exactly zero plus the `2n` signed monomials. It also exhausts base-five digit tuples of lengths one through seven with digits in `[-2,2]`, finding only the zero tuple with weighted sum zero.

The observed NO gap of two is a result for the tested instances. The report does not infer it for arbitrary inputs; the paper claims only the general lower bound `M+1`. The exhaustive method is exponential in the degree and is used solely as an audit tool. It is not a polynomial-time algorithm for the original problem. Tests with zero weights establish additional finite evidence for the extension; they do not change the formally stated source domain.

### Supplemental instances and generic filter tests

The separate supplemental run adds six instances and **811,903** complete bounded lattice-multiplier checks. It preserves the main grid's counts and saves its own results in `supplemental_results.json` and `supplemental_checks.log`.

| Weights | `B` | `M` | Exact `lambda` | Purpose |
|---|---:|---:|---:|---|
| `(1)` | 100 | 2403 | 2601 | Target far above `W` |
| `(2^30,2^30)` | `2^30+1` | 21474836509 | 21474836511 | Large binary weights; infeasible target |
| `(1,2,3)` | 6 | 5537 | 5537 | `B=W` |
| `(1,2,3)` | 3 | 2873 | 2873 | `E=0` |
| `(0,0,0)` — extension | 100 | 89021 | 89221 | All-zero weights and large target |
| `(1,2,4)` | 7 | 6423 | 6423 | `B=W`, distinct weights |

These supplemental NO gaps are respectively 198, 2, and 200; they support the stated lower bound without suggesting that every NO gap is two.

The script also persists seven checks of Proposition 3.3 with `H,V` independent of the Subset Sum construction. Four checks use two arbitrary signed pairs in each of `n=4,8`; the elementary triangle bound excludes larger opposite-pair mass, and all remaining nonmonomial multipliers and all ternary `z` arrays are examined without a parity restriction. They evaluate 7,980,768 candidate pairs and find no counterexample. Three further checks each exhaust the full boxes `b∈[-2,2]^4` and `z∈[-1,1]^4`, 50,625 pairs per check:

| `H` | `V` | `L` | `M` | Pairs satisfying premises |
|---|---|---:|---:|---:|
| `(0,0,0,0)` | `(0,0,0,0)` | 1 | 5 | 729 |
| `(1,2,-1,0)` | `(-2,1,0,1)` | 9 | 49 | 425 |
| `(3,0,0,-2)` | `(0,0,4,-1)` | 11 | 60 | 121 |

Every premise-satisfying pair in the three boxes has `b=0` or a signed monomial. Across the seven generic checks there are **8,132,643** candidate pairs and zero counterexamples. These counts are separate from the 31,255,688 and 811,903 reduction-lattice searches; common generic checks are rerun in each script mode and should not be counted as new distinct cases.

For all 186 grid-plus-supplemental instances, the script additionally checks the exact ring determinant identity, `F=2W`, `nu=2|E|`, the dimension inequalities, each integer inequality used in the explicit size estimate, all relevant positive slack formulas, and the `2M` bound on every basis coefficient. The large-weight case demonstrates that this computation uses the binary values directly; the general polynomial-size claim is justified by the symbolic proof above, rather than inferred from the run time.


## Part IV. Classified findings and formalisation plan

### Edge cases and findings classification

#### (a) Blocking mathematical errors

None found in the audited reduction or complexity arguments, with the multiplier-rigidity proposition verified in Part I. The external NP-hardness of the source language remains an explicit theorem dependency, not an error in a mathematical paper that cites it. A Lean development that leaves it as an unproved axiom would establish only conditional NP-hardness.

#### (b) Fixable edges and presentation

- `n=1,2`: valid target-language degrees; no reduction output has either degree, since `n≥4`. The multiplier section has explicit `m≥2` and does not claim its construction for these small degrees. Do not extend its formulas silently. No repair to the theorem is required.
- `s=1`: `(m,n)=(2,4)`; the `j≥2` sum in `H` is empty. All inequalities remain strict as claimed. `s=2` uses the same degree four and may attain `s=m`; the Laurent support still avoids `±m`.
- `s=0`: invalid source input. If broadening the source to allow an empty list, handle it directly (`B=0` is YES; `B>0` is NO), or replace the dimension formula `n=O(s)` by `O(s+1)`. The displayed `2s≤n≤4s` is deliberately stated only for `s≥1`.
- Zero weights: excluded by the paper's source definition and therefore malformed. The construction and proofs actually extend to nonnegative weights, including all-zero weights, because `F=2W` still holds and `M≥1`; one can broaden the source definition, or preprocess zeros and handle the emptied list. Preserve positivity of the source if using an existing theorem with that statement. Negative weights are a different issue: `F=2W` fails and must be normalized before applying this reduction.
- `B=0`: empty subset is a witness; no positive-target assumption is used in the reduction. `B>W`: always NO for nonnegative weights; the formulas and bounds still work without preprocessing.
- The prose after (2.4) calls its convolution bound the “second identity”; “second inequality” is the accurate wording. This is harmless and does not change any proof.
- Apparent missing bars/exponents in `A.txt` are extraction artifacts. Use the PDF formulas in the formal specification.
- The `O(ell^2)` size claim presupposes conventional explicit binary coefficient arrays, as explicitly stated. A future change to a succinct polynomial encoding would need a new statement and proof.

#### (c) Lean-specific care

- Work over integer coefficient arrays first; use finite `max` over a proven nonempty index type (`n>0`) and prove the existence of a first minimum as a least positive integer.
- Keep support indices `j-1`, `m-j+1`, and `n-j+1` in `Z` until range proofs permit conversion to `Fin n`. Natural truncated subtraction can silently change intended identities.
- Define all scalar embeddings and record the distinction between natural norm values and integer coefficients; `E` is signed. Avoid informal integer division by `M` or two: use cancellation/linear arithmetic.
- For the Boolean equivalence, prove the integer interval facts once and transport the coefficient family into an actual `Fin s → Bool` witness.
- Prove the Laurent support exclusion explicitly at `s=m`, including negative exponent signs; no field/canonical embedding is needed for it.
- Module normalization uses the identity of the same commutative ring action on both coordinates, unique multipliers, and the signed permutation norm theorem.
- `M+1` requires integer-valued norms and an attained first minimum. A real-valued norm version alone would provide only `lambda>M`.
- Separate executable algorithms from mathematical formulas involving logarithms. Implement least-power-of-two by bounded doubling and prove it satisfies the inequalities; implement bit length by binary representation, then relate it to the logarithmic notation.
- Show exact `rho` is computed from `DK`; replacing it by an upper bound may preserve correctness but changes the exact construction and all numerical test values.
- Specify malformed bitstrings and total reductions, explicit coefficient order, signed binary encoding, list delimiters, and certificate lengths.
- Polynomial-time NP verification and rational linear algebra are separate complexity theorems. A computable Lean function or a terminating tactic is not a polynomial-time TM proof.
- The coefficient-matrix nonzero determinant equivalence uses irreducibility for general inputs; it is false in this form over an arbitrary reducible negacyclic quotient. The array-only construction proof can establish its own injectivity directly if desirable.

### Source NP-hardness and a full 3SAT option

The main reduction needs the exact positive-integer binary Subset Sum language above, NP-hard under deterministic polynomial-time many-one reductions. It does not intrinsically need a new reduction from 3SAT if a matching formalised Subset Sum NP-hardness theorem can be imported.

If the formal development starts from 3SAT instead, its NP-hardness must itself be available as a theorem. Otherwise Cook–Levin and a suitable conversion to 3CNF remain upstream obligations. A proof of only `3SAT ≤p SubsetSum ≤p ModuleSVP` does not by itself prove reduction from every NP language without that starting theorem.

Karp's original primary treatment includes the equality-form KNAPSACK problem; see [Karp, *Reducibility among combinatorial problems*, scanned reprint](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/Karp.pdf). When adapting a version that allows signed weights, complement a Boolean choice at each negative weight: if `a_i<0`, write `x_i=1-y_i` and replace its weight by `-a_i`; replace target `b` by `b-Σ_(a_i<0) a_i`. Drop zero weights. Negative transformed targets and an empty resulting list are resolved by fixed YES/NO instances. For exact formalisation one must first state exactly which source theorem is imported and prove this normalization preserves its encoding and size.

If no matching library theorem exists, a direct 3SAT-to-Subset-Sum development is straightforward. For a formula with `v` variables and `c` clauses of at most three literal occurrences, use `v+c` base-ten digit columns. For each variable create two positive numbers, for true and false, each with a one in its variable column. In each clause column, the true number carries the number of positive occurrences of that variable and the false number carries the number of negative occurrences. For each clause add two positive slack numbers with clause-column digits one and two, respectively. The target has variable digits one and clause digits four. Every column total in any chosen subset is at most six (at most three literal occurrences plus slack total three), hence no carries occur. Target variable digits force exactly one truth choice per variable. A clause contributes `t∈{0,1,2,3}` satisfied occurrences; adding a subset of slack digits gives four iff `t≥1`, since slack possibilities are exactly `0,1,2,3`. Repeated literals are handled by occurrence counts, not by indicator digits. All weights are positive and binary lengths are `O(v+c)`; there are `2v+2c` weights, and construction size/time are polynomial. Degenerate formulas with no variables/clauses can be handled by fixed instances. This is a proof blueprint, not a claim that the TM development already exists.

### Suggested formalisation dependency order

1. **Integer array algebra:** negacyclic multiplication, coefficient extensionality, `X^n=-1`, signed shifts and inverse shifts, commutativity/associativity, unit monomials, integer `l1` and max norms, convolution inequality, involution and adjoint identities.
2. **Finite opposite-pair algebra:** the `D` and `D*` formulas, pairwise norm equality, `D*D=2`, skew-adjoint `K`, exact support and `l1` bounds, integer balanced-base-five uniqueness, support rigidity, multiplier rigidity. These are pure arrays/finite sums and inequalities; no algebraic number fields or complexity machinery is needed.
3. **Construction and correctness:** executable dimension rounding; `u,h,E,H,V,F,nu,rho,L,M,Q,G`; support of `H`; Boolean-word encoding; Laurent coefficient test; exact norm identity; determinant or direct coefficient injectivity; soundness/completeness and integer first-minimum gap; witness bijection.
4. **General target representation:** coefficient block matrix `Ghat`, free rank-two module/coefficient lattice equivalence, validity. Add irreducibility of `X^n+1` for power-of-two `n` and quotient-domain/field bridges as needed; the identification with the full cyclotomic integer ring is explanatory metadata unless the final theorem explicitly names `Z[zeta]`.
5. **Bit encodings and arithmetic costs:** signed binary integers, arrays and matrices, total valid-input parser, bit-length inequalities, addition/multiplication/divisibility/convolution algorithms, bounded dimension and coefficient size. Turn construction correctness into a total polynomial-time many-one map.
6. **Complexity bridge:** define languages, deterministic polynomial time, reductions, NP verifiers, source Subset Sum and its NP-hardness theorem (import matching theorem, normalize another version, or implement the 3SAT digit reduction); prove NP membership using bounded `(v,t)` certificates and a polynomial-time nonsingularity check. Leibniz determinant bounds can replace Hadamard analytically.
7. **Recovery and search:** exact rational/fraction-free multiplier recovery with bit bounds; inverse bijection algorithm; a correctness relation for shortest-vector outputs; one-call polynomial-time oracle reduction, robust to every valid oracle answer and with explicit answer-length bound.

A practical initial milestone is an unconditional Lean theorem giving the explicit map on integer arrays and the equivalence `SubsetSumYES ↔ ∃ nonzero module vector of norm≤M`, together with the numerical gap and output bit bounds. Label this as the algebraic reduction theorem until the machine-level complexity and source NP-hardness modules are available.
