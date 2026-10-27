# Mathematical audit of Paper B

Paper: **Coefficient infinity-norm SVP on principal cyclotomic ideals**, 27 October 2026, five pages. Audited against [B.pdf](../papers/B.pdf) and [B.txt](../papers/B.txt); layout extraction and visual PDF checks resolve the domain-wall product and the exponent in the finite-\(p\) statement. No Lean code was written. All computations use exact integers.

**Verdict.** I found no mathematical error that invalidates the stated reduction or theorem. Equations (1)–(3), the interaction table, the power-of-two guard, and the additive NO gap are correct. The proof needs substantial expansion before formalisation. There is one literal coefficient-bound correction, several source/encoding conventions to state, and important hypotheses that must remain explicit. The literal parameters are much too large for dense experiments even at three source vertices; the checks below distinguish actual-label sparse enumeration from exhaustive small-ring algebra and lattice enumeration.

The complete proof and the classifications are below. Reproducible programs and their JSON outputs are in [auditB/](auditB/). The separate independent audit notes in that directory supplement this self-contained report.

## 1. Exact statement, input conventions, and source problem

For an integer \(n=2^k\), \(k\ge0\), define
\[
R_n=\mathbb Z[X]/(X^n+1).
\]
Every element has a unique representative of degree less than \(n\), identified with an integer coefficient array \((x_0,\ldots,x_{n-1})\). Set
\[
\|x\|_\infty=\max_{0\le i<n}|x_i|,
\qquad \|x\|_1=\sum_{i=0}^{n-1}|x_i|.
\]
For a nonzero ideal \(I\),
\[
\lambda_{1,\infty}(I)=\min\{\|z\|_\infty:z\in I,\ z\ne0\}.
\]
This minimum exists: the set of attainable norms is a nonempty subset of the positive integers. For the constructed ideals a stronger, finite minimum formula will be proved directly.

The target language consists of legal encodings \((n,f,r)\) with \(n\) a positive power of two, \(f\in R_n\setminus\{0\}\), and \(r\in\mathbb Z\), \(r\ge1\), such that \(\lambda_{1,\infty}(fR_n)\le r\). The encoding explicitly lists all \(n\) coefficients of \(f\) in signed binary and gives \(r\) in binary. One can infer \(n\) from the list length. Fix a convention that malformed encodings are rejected. The theorem concerns a varying dimension, coefficient infinity norm, and exact decision. It makes no assertion about one fixed dimension, canonical norms, Euclidean norm, or a constant approximation factor.

Use **CLIQUE** for finite simple undirected graphs with vertices \(\{1,\ldots,v\}\), explicitly encoded, for example by an adjacency matrix, and target \(h\in\mathbb N\). A YES instance has a set of at least \(h\) pairwise adjacent distinct vertices; equivalently it has one of exactly \(h\). There are no loops or multiple edges. Using an explicit graph encoding ensures that \(v\) is polynomially bounded by input length. A binary vertex count with arbitrarily many unlisted isolated vertices is a different encoding convention and cannot simply be used in the paper's dimension bound without preprocessing.

The main construction assumes \(3\le h\le v\). This restricted source remains NP-hard: solve all omitted cases in polynomial time and map their answers to a fixed YES or fixed NO instance of the restricted source. In detail, \(h=0\) is YES under the empty-clique convention; \(h=1\) is YES iff \(v\ge1\); \(h=2\) is YES iff there is an edge; and \(h>v\) is NO. The fixed restricted instances can be \((K_3,3)\) and \((\overline K_3,3)\). Alternatively send those trivial cases directly to target instances \(n=2,f=1,r=1\) and \(n=2,f=3,r=1\); these have shortest norms 1 and 3, respectively, so even the NO gap is preserved. Thus \(v<3\) and \(h>v\) are not undefined cases of the reduction.

The external complexity starting theorem is NP-hardness of this exact, explicitly encoded CLIQUE language. CLIQUE is among the complete problems in [Karp's original paper, *Reducibility Among Combinatorial Problems* (1972)](https://www2.seas.gwu.edu/~simhaweb/champalg/tsp/papers/KarpOriginal.pdf). The mathematical reduction audited here does not need to start from 3SAT. A fully foundational machine-checked NP-completeness theorem must either import CLIQUE hardness or prove it from a previously formalised NP-complete source; see Section 15.

## 2. Coefficient arrays, signs, adjoints, and wraparound

These conventions underlie every subsequent formula. For an array \(x\) and any integer \(j\), write \(j=qn+r\), \(0\le r<n\), with Euclidean remainder, and define its lift
\[
\widetilde x_j=(-1)^q x_r.
\]
Thus \(\widetilde x_{j+n}=-\widetilde x_j\), including at negative indices. Multiplication is negacyclic convolution:
\[
(ab)_i=\sum_{j=0}^{i}a_jb_{i-j}
       -\sum_{j=i+1}^{n-1}a_jb_{n+i-j}.
\]
For every integer \(d\), including negative \(d\),
\[
(X^d x)_i=\widetilde x_{i-d}.
\]
In particular, \((Xx)_0=-x_{n-1}\) and \((Xx)_i=x_{i-1}\) for \(i>0\). The inverse \(X^{-1}\) exists because \(X^n=-1\); for \(1\le d<n\), \(X^{-d}=-X^{n-d}\). Ordinary cyclic indexing, without this minus sign, gives incorrect guard and wall formulas.

Each multiplier \(X^d\) is a signed permutation, preserving all coefficient \(\ell_p\) norms and the coefficient inner product. Its adjoint is \(X^{-d}\). The involution \(*\) is induced by \(X\mapsto X^{-1}\). Consequently
\[
A_d=X^d-X^{-d}\quad\Longrightarrow\quad A_d^*=-A_d,
\qquad \langle z,A_dz\rangle=0.
\]
The latter identity holds over \(\mathbb R\) and also follows integrally from transposing the inner product and cancelling 2. Linear combinations with real/integer scalar weights remain skew-adjoint. The terms \(X^d+X^{-d}\) are self-adjoint.

If \(J\in R_n\), signed-permutation invariance and the triangle inequality give
\[
\|Jx\|_\infty\le\|J\|_1\|x\|_\infty,
\quad \|Jx\|_1\le\|J\|_1\|x\|_1,
\quad \|Jx\|_p\le\|J\|_1\|x\|_p\quad(1\le p<\infty).
\]
Only the first two, on integer arrays, are needed for the main theorem.

For distinct residues \(i,j\), their unsigned cyclic distance is
\(\operatorname{dist}_n(i,j)=\min(|i-j|,n-|i-j|)\in\{1,\ldots,n/2\}\) when \(n\) is even. Cyclic distance is used solely to describe support locations; interactions still use signed negacyclic multiplication.

## 3. All parameters and polynomials

For the main source range \(v\ge h\ge3\), put
\[
\begin{aligned}
b_0&=3v^3+1, & a_i&=i+b_0i^2+b_0^2i^3\quad(1\le i\le v),\\
A_0&=\max_i a_i=a_v, &D&=\{|a_i-a_j|:\{i,j\}\in E(\Gamma)\},\\
Q&=16, & R_0&=QA_0+2.
\end{aligned}
\]
The \(a_i\) are strictly increasing positive integers. Choose \(n\) to be the least power of two strictly greater than \(8R_0+16\). Define
\[
E_+=\{1,2\}\cup\bigcup_{d\in D}\{Qd-1,Qd,Qd+1,Qd+2\}.
\]
Allowed cyclic differences are exactly \(E_+\cup(-E_+)\pmod n\). Every element of \(E_+\) is at most \(R_0<n/8\). In particular \(n/2\) is forbidden. There are four distances in each far window, not five: the reflected positive window is a window around the negative center, not a second positive-center window with offset \(-2\).

For a deterministic implementation list the forbidden distances in increasing order:
\[
\{d_0<\cdots<d_{s-1}\}=\{1,\ldots,n/2\}\setminus E_+,
\qquad A=\sum_{j=0}^{s-1}5^j(X^{d_j}-X^{-d_j}).
\]
The proof works for any fixed enumeration. Define
\[
T=\sum_{d\in D}(X^{Qd}+X^{-Qd}+X^{Qd+2}+X^{-Qd-2}),
\quad R_T=\|T\|_1,
\]
\[
C=R_T+h+1,\quad \tau=C+h-1,\quad
L=2C+R_T+\tau+1,\quad
G=LA-C(X+X^{-1})+T.
\]
Here \(A\) is skew-adjoint and \(T\) is self-adjoint. \(G\) need not be either.

Let \(m=|D|\). The difference uniqueness proved below implies \(m=|E(\Gamma)|\). Distinct windows are disjoint, positive exponents are less than \(n/8\), and reflected exponents are near \(n\). Therefore no terms of \(T\) collide in the coefficient basis and
\[
R_T=4m,\quad |E_+|=2+4m,\quad s=n/2-2-4m,
\]
\[
\boxed{C=4m+h+1,\quad \tau=4m+2h,\quad L=16m+4h+3.}
\]
The exact margins used in the proof are
\[
\tau-R_T=2h>0,\qquad
2C-R_T=\tau+2,\qquad
-L+2C+R_T=-\tau-1<\tau.
\]
In particular they hold at \(h=3\) and when \(m=0\).

The rest of the construction is
\[
\begin{aligned}
S&=1+X+\cdots+X^{n-1}, & H&=G(1-X), & R_H&=\|H\|_1,\\
B&=R_H+2\tau+1, & K&=BX+H, & R_K&=\|K\|_1,\\
M&=3R_K+1, & f&=(M-K)S, &r&=M+B-2\tau.
\end{aligned}
\]
All norms here mean norms of the unique reduced coefficient arrays. Useful equivalent formulas are
\[
r=M+R_H+1>0,\qquad
f=(M-B)S+2B-2G.
\]
The latter follows from \(XS=S-2\) and \((1-X)S=2\); it also gives an efficient direct output construction.

For complete clarity about coefficients: for \(d<n/2\), the corresponding guard term is \(5^j(X^d+X^{n-d})\); at \(d=n/2\), it is \(2\cdot5^jX^{n/2}\). A term \(X^e+X^{-e}\) of \(T\) has coefficients \(+1\) at \(e\) and \(-1\) at \(n-e\). The nearest-neighbor term has coefficients \(-C\) at 1 and \(+C\) at \(n-1\). Thus \(G_0=0\). One may form \(H\) as \(H_0=G_0+G_{n-1}\), \(H_i=G_i-G_{i-1}\) for \(i>0\), then add \(B\) at coordinate 1 to obtain \(K\). Finally \(f_0=M+B\) and \(f_i=M-B-2G_i\) for \(i>0\). This describes every output coefficient without ambiguous negative exponents.

## 4. Labels and three-term uniqueness: page 1, first proof

**Precise label lemma.** If \(i_1,i_2,i_3,j_1,j_2,j_3\in\{1,\ldots,v\}\), with repetitions permitted, and
\(a_{i_1}+a_{i_2}+a_{i_3}=a_{j_1}+a_{j_2}+a_{j_3}\), then the two index multisets are equal.

For each \(t=1,2,3\), the digit sum \(p_t=i_1^t+i_2^t+i_3^t\) lies between 0 and \(3v^t\le3v^3=b_0-1\). Thus no carry occurs in any of the three base-\(b_0\) digits of either label sum. Successive remainders and quotients by \(b_0\) recover \(p_1,p_2,p_3\), so those power sums agree on both sides.

Write \(e_1,e_2,e_3\) for the elementary symmetric functions of the three indices. Newton's identities here are simply
\[
e_1=p_1,\qquad 2e_2=p_1^2-p_2,\qquad
3e_3=p_3-e_1p_2+e_2p_1.
\]
Equality of power sums implies equality of \(e_1,e_2,e_3\), using injectivity of multiplication by 2 and 3 in \(\mathbb Z\). Hence the two monic polynomials
\(Z^3-e_1Z^2+e_2Z-e_3=\prod_{t=1}^3(Z-i_t)\) are equal. Their integer roots with multiplicity agree, proving the multiset assertion. For a formal proof, one can work over \(\mathbb Q\) or use factor cancellation for split monic polynomials; there is no need to introduce complex roots.

Two-term uniqueness follows by padding both sums with the same arbitrary label \(a_1\), then cancelling its occurrence in the resulting multisets. Thus
\[
a_i-a_j=a_k-a_l\ne0\quad\Longrightarrow\quad (i,j)=(k,l).
\]
Indeed \(\{i,l\}=\{k,j\}\); the alternative matching would have \(i=j\), contradicting a nonzero difference. Consequently positive unordered edge differences are also unique. This justifies both the word “uniquely” in Lemma 1 and \(|D|=|E(\Gamma)|\).

The degree bound is explicit:
\[
b_0\le4v^3,\qquad a_v\le v+4v^5+16v^9\le21v^9.
\]
The labels depend on the full \(v\), including isolated vertices; none of the arguments presupposes that every vertex has an incident edge.

## 5. Lemma 1: difference-clique extraction, including the row/column step

**Precise statement.** Let \(P\subseteq\mathbb Z\) have at least three distinct elements, and suppose that for any distinct \(x,y\in P\), \(|x-y|\in D\). Then there exist a source clique \(C_\Gamma\subseteq\{1,\ldots,v\}\), an integer \(t\), and \(\varepsilon\in\{-1,1\}\) such that
\[
P=\{t+\varepsilon a_i:i\in C_\Gamma\},\qquad |P|=|C_\Gamma|\le v.
\]
If \(P\) was not initially assumed finite, the hypotheses imply finiteness: after anchoring any point, every other point is one of the finitely many signed differences \(\pm D\).

Choose \(p_0\in P\), replace \(P\) by \(P-p_0\), and represent each nonzero point uniquely as \(a_i-a_j\), with \(i\ne j\) and \(\{i,j\}\) an edge. For two distinct represented points \(a_i-a_j\) and \(a_k-a_l\), their difference is some nonzero edge difference \(a_p-a_q\). Rearrangement yields
\[
a_i+a_l+a_q=a_j+a_k+a_p,
\quad\text{so}\quad \{i,l,q\}=\{j,k,p\}.
\]
If \(i=k\), the representing pairs share their first coordinate. If \(i\ne k\), then \(i\ne j\) too, so the occurrence of \(i\) on the right must be \(p\). Cancel that occurrence to obtain \(\{l,q\}=\{j,k\}\). Since \(k\ne l\), the occurrence \(l\) must match \(j\); thus \(l=j\). This reasoning remains valid with all other possible repeated indices: it cancels occurrences of a multiset, not distinct set elements. Therefore every pair of representing ordered pairs shares its first or its second coordinate.

There are at least two representing pairs. If two distinct pairs are \((a,b),(a,c)\) with \(b\ne c\), any third pair \((x,y)\) with \(x\ne a\) would have to share its second coordinate with both, requiring \(y=b=c\), impossible. Hence all pairs are in the single row with first coordinate \(a\). If instead the first two pairs share only their second coordinate, the identical argument with coordinates exchanged puts every pair in one column. A family of just two pairs is covered by the same reasoning. This is the full row/column argument.

For a common second coordinate \(j\), take the clique indices to be that \(j\) and all first coordinates. The represented set, including zero, is \(-a_j+\{a_i:i\in C_\Gamma\}\). For a common first coordinate \(i\), use \(a_i-\{a_j:j\in C_\Gamma\}\). The common index is adjacent to each other index by its representing edge. Two noncommon indices are adjacent because their label difference equals a difference between the represented points; uniqueness of edge differences identifies that edge. Distinct represented points give distinct other indices, so the cardinalities agree. Restoring \(p_0\) gives the claimed translation and sign.

The lower bound three is used to have at least two representing pairs. Sets of size one or two can be dealt with directly, but are not needed when this lemma is invoked at the target \(h\ge3\).

## 6. Sparse spins and Lemma 2: page 2

For each nonempty odd-cardinality set \(W=\{w_0<\cdots<w_{2a}\}\subseteq\{0,\ldots,n-1\}\), let \(\sigma_{w_j}=\eta(-1)^j\), \(\eta\in\{-1,1\}\), and \(\sigma_i=0\) elsewhere. These, and only these, are the sparse spins. Their lifts are antiperiodic. Since the first and last nonzero signs in a period agree, the signs of consecutive active positions in the lifted integer line alternate even across the boundary. Replacing \(\sigma\) by \(-\sigma\) leaves every field \(\sigma_i(G\sigma)_i\) unchanged.

Define the finite integer maximum
\[
\Theta(G)=\max_{\sigma\text{ sparse spin}}\ \min_{i\in\operatorname{supp}\sigma}\sigma_i(G\sigma)_i.
\]
The indexing sets for both extrema are finite and nonempty. Equivalently one may use just the positive initial sign for each odd support. No undefined minimum at the empty support occurs.

**Lemma 2, precise version.** If a sparse spin satisfies \(\sigma_i(G\sigma)_i\ge\tau\) at every active coordinate, then every pair of distinct support positions has cyclic distance in \(E_+\). In addition \((A\sigma)_i=0\) at every active coordinate. In fact the guard's vanishing conclusion only uses that \(\sigma\) is ternary and every active field is greater than \(-\tau-1\); alternation and odd support are not needed for the guard itself.

Let \(a_i=\sigma_i(A\sigma)_i\), an integer. The notation here is temporary and should not be confused with the source labels. The remaining field is bounded in absolute value by \(2C+R_T\), because each neighbor coefficient has absolute value at most one and \(\|T\sigma\|_\infty\le R_T\). If \(a_i<0\), integrality gives \(a_i\le-1\), and therefore
\[
\sigma_i(G\sigma)_i\le-L+2C+R_T=-\tau-1<\tau,
\]
contradicting the assumption. Hence all \(a_i\ge0\). Their sum over active coordinates equals the sum over all coordinates, which is \(\langle\sigma,A\sigma\rangle=0\). A finite sum of nonnegative integers is zero only when every summand is zero. Since \(\sigma_i=\pm1\) at active coordinates, \((A\sigma)_i=0\) there.

At each such \(i\), put
\[
u_j=(A_{d_j}\sigma)_i=\widetilde\sigma_{i-d_j}-\widetilde\sigma_{i+d_j}\in\{-2,-1,0,1,2\}.
\]
The zero-field equation is \(\sum_{j=0}^{s-1}5^ju_j=0\). Reducing modulo five forces \(u_0=0\), since zero is the only multiple of five in \([-2,2]\). Divide by five and repeat. Thus every digit \(u_j\) vanishes. The argument applies unchanged at the antipodal distance, where the digit is still in \([-2,2]\); one must not replace that summand by zero.

It remains to prove the propagation claim rather than assume it. Fix a forbidden \(d\), \(1\le d\le n/2\). Zero active \(A_d\) fields mean
\[
\widetilde\sigma_{x-d}=\widetilde\sigma_{x+d}
\quad\text{whenever }\widetilde\sigma_x\ne0.
\tag{G}
\]
This holds at every integer lift of an active coordinate because both sides change sign on adding \(n\). Suppose there is an active step-\(d\) pair \(x,x+d\). Applying (G) at \(x+d\) gives \(\widetilde\sigma_{x+2d}=\widetilde\sigma_x\ne0\); applying it at \(x\) also propagates backwards. Repeatedly applying (G) at the newly active coordinates proves that the entire step-\(d\) orbit is active and that values repeat with step \(2d\).

Let \(g=\gcd(n,d)\) and \(\ell=n/g\). Since \(n\) is a power of two and \(0<d<n\), \(\ell\) is an even power of two and \(d/g\) is odd: it is coprime to the even power of two \(n/g\). Iterating the step-\(2d\) period \(\ell/2\) times gives
\[
\widetilde\sigma_{x+\ell d}=\widetilde\sigma_x,
\qquad \ell d=n(d/g).
\]
Antiperiodicity and oddness of \(d/g\) instead give \(\widetilde\sigma_{x+\ell d}=-\widetilde\sigma_x\), a contradiction to nonzero integer values. Thus there is no such pair. Either orientation of a cyclic-distance-\(d\) pair supplies the required active lifted pair, so all forbidden cyclic distances are excluded.

**Antipodal check.** When \(d=n/2\), \(\ell=2\) and \(A_d=2X^{n/2}\); zero active field at one endpoint of an antipodal pair already says twice the other signed value is zero, impossible. The orbit argument gives exactly the same contradiction.

**Necessity of the power-of-two assumption.** For \(n=6,d=2\), the odd alternating spin \((1,0,-1,0,1,0)\) has active distance-two pairs but \((X^2-X^{-2})\sigma=0\). Here the step orbit has odd length. This is an out-of-scope counterexample to a generalisation, not a counterexample to the paper.

## 7. Lemma 3: short arc, gaps, and the unique trimer

**Precise statement.** Under Lemma 2's hypotheses, after a signed monomial shift there is a lift of the support inside \([0,R_0]\) consisting of one run of three consecutive integers and any number of runs of two consecutive integers. A run is a maximal consecutive support block in this short integer interval. Write \(t\) for the trimer start. A left dimer has start \(t+Qq\), \(q<0\), and a right dimer has start \(t+Qq+1\), \(q>0\). The resulting set \(P\) of component integers \(q\), including 0 for the trimer, has distinct elements and all positive pair differences in \(D\).

**No isolated point.** The guard fields are zero, leaving \(-C(X+X^{-1})+T\). If an active point has no adjacent support point, its nearest-neighbor field is zero and its whole field is at most \(R_T<\tau\). Thus every active point has a neighbor. For adjacent support points, alternation in the lifted ordering makes their signs opposite, so each contributes \(+C\), including when the adjacent pair crosses residue zero. A run cannot have length four, since then its first and fourth points have forbidden distance three. Distance three is forbidden because the first far distance is at least \(Q-1=15\). Hence all runs have length two or three; a full circular run is also excluded by the distance-three condition.

**At least three zeros between runs.** If one zero separates a run ending at \(a\) from the next run starting at \(a+2\), that next run contains \(a+3\), producing a forbidden distance-three pair. If two zeros separate them, the endpoints \(a\) and \(a+3\) themselves violate the guard. All runs have length at least two, so the second point used in the first argument exists. These statements are valid circularly as well, before choosing a cut.

**Short-interval lemma.** All pairwise cyclic distances are at most \(R_0\). Move one point to residue zero and lift every other point to its unique representative in \([-R_0,R_0]\). Let \(u\le0\le w\) be the extreme representatives and \(\Delta=w-u\le2R_0\). The cyclic distance of the extremes is at most \(R_0\). Were \(\Delta>R_0\), the other branch would have to obey \(n-\Delta\le R_0\). But \(\Delta\le2R_0<n-R_0\), because \(n>8R_0+16\), so \(n-\Delta>R_0\), contradiction. Therefore \(\Delta\le R_0\) and the support lies on one integer arc of diameter at most \(R_0\).

The complementary arc has edge-length at least \(n-R_0\), and thus at least \(n-R_0-1\) empty coordinates between its occupied endpoints. The paper's “gap length” should be read as edge-length, not a count of empty positions. It is a suitable long gap at which to cut. The stronger \(R_0<n/8\) also guarantees uniqueness of a gap this long, though uniqueness is not needed.

**Why moving the cut preserves the hypotheses.** Multiplication by \(X^k\) permutes positions with a possible sign \(\epsilon_i\) at each moved coordinate. It commutes with \(G\), and so the new field at that position is
\(\epsilon_i\sigma_i\cdot\epsilon_i(G\sigma)_i=\sigma_i(G\sigma)_i\).
It also preserves the class of sparse spins: consecutive active signs in the integer lift alternate, and an odd support makes the signed wrap compatible with alternation after resorting its residues. One may therefore place the arc in \([0,R_0]\). In this lift all relevant pair differences are ordinary signed integers of magnitude at most \(R_0<n/2\). The negative-exponent terms already incorporate the negacyclic signs; no extra boundary sign is to be inserted in the ensuing ordinary-distance interaction calculations.

**At most one trimer.** Two trimers with start difference \(\delta\) have \(\delta\ge6\), because there are at least three intervening zeros. Their cross differences include all five integers \(\delta-2,\ldots,\delta+2\), all greater than two. They would all have to lie in far windows
\(I_d=[Qd-1,Qd+2]\cap\mathbb Z\). Every such window contains exactly four integers; distinct centers differ by at least \(Q\), and the difference from one window's last integer to the next window's first is at least \(Q-3=13\). Thus five consecutive allowed far integers cannot exist. This excludes two trimers, regardless of edges or unused labels. Odd total support size and even dimer sizes now force exactly one trimer.

**Offsets relative to that trimer.** For a left dimer start \(p<t\), the cross differences to the trimer are exactly
\((t-p)+\{-1,0,1,2\}\). They are greater than two by the gap bound. Four consecutive allowed far integers must fill one complete window, hence \(t-p=Qd\) for some \(d\in D\). Therefore \(p=t+Qq\) with \(q=-d<0\). For a right dimer start \(p>t\), the differences are \((p-t)+\{-2,-1,0,1\}\), forcing \(p-t=Qd+1\), so \(q=d>0\).

For two left dimers or two right dimers, write \(m=|q-q'|>0\). Their distinct cross-distance values are \(Qm+\{-1,0,1\}\). Inclusion in a far window \([Qd-1,Qd+2]\) implies \(d\le m\) and \(Q(m-d)\le1\), hence \(d=m\). For a left and a right dimer, \(m=q'-q>0\) and the values are \(Qm+\{0,1,2\}\). Inclusion implies \(d\ge m\) and \(Q(d-m)\le1\), again \(d=m\). In either case the three consecutive values cannot straddle distinct far windows. Pairs with the trimer were already covered. All component integers are distinct, so \(P\) has the claimed pair-difference property.

## 8. Converse support construction

Let \(C_\Gamma\) be any nonempty source clique and choose its vertex \(c\) for the trimer. Put
\(q_i=a_i-a_c\) for \(i\in C_\Gamma\). Place the trimer at \(0,1,2\). For \(q_i<0\), put a left dimer at \(Qq_i,Qq_i+1\); for \(q_i>0\), put a right dimer at \(Qq_i+1,Qq_i+2\). There are \(q=|C_\Gamma|\) components and \(2q+1\) points. Distinct labels and large \(Q\) make them disjoint.

Within components all distances are one or two. Between trimer and dimer the distances fill exactly a prescribed four-point window because \(|q_i|\in D\). Between same-side dimers they are \(Q|q_i-q_j|+\{-1,0,1\}\); between opposite-side dimers they are \(Q|q_i-q_j|+\{0,1,2\}\). The clique property gives \(|q_i-q_j|=|a_i-a_j|\in D\), so all are allowed. Consecutive components in their ordering have edge-distance at least \(Q-1\); the paper's weaker separation estimate \(Q-2\) is therefore safe.

The entire support has diameter at most
\[
Q(\max_{i\in C_\Gamma}a_i-\min_{i\in C_\Gamma}a_i)+2\le QA_0+2=R_0.
\]
This is slightly stronger than the paper's \(QA_0+3<n/2\). Translate it into \([0,R_0]\). Put alternating signs on the sorted support. Choosing the trimer signs as \((+,-,+)\) gives left dimer signs \((+,-)\) and right dimer signs \((-,+)\): crossing any preceding dimer changes the ordinal index by two, whereas crossing the trimer changes it by three. The resulting spin has odd support, no forbidden pairs, and hence zero active guard fields. The field threshold follows from the next section. This proves the converse with an actual valid finite-ring support, including possible negative pretranslation positions.

## 9. Every entry of the interaction table: pages 3–4

Let \(k=Qd\), \(d\in D\), and write \(t_e\) for the ordinary signed-offset kernel of \(T\) on the short lift. Its only relevant near-center coefficients are
\[
(t_{k-1},t_k,t_{k+1},t_{k+2})=(0,1,0,1),\qquad t_{-e}=t_e.
\]
Other centers cannot contribute at these offsets, since their spacing is at least 16. Within a component, distances are zero, one, or two, and \(T\) has no such coefficient, so within-component fields are zero.

For a receiver position \(x\) with sign \(r_x\), a sender component contributes
\(r_x\sum_y t_{x-y}s_y\). The following computations give the signed local field, rather than just the unsigned convolution.

* Same-side dimers have equal sign patterns and start difference \(k\). At the lower receiver's two endpoints the fields are \(t_k-t_{k+1}=1\) and \(-t_{k-1}+t_k=1\). At the higher receiver they are \(t_k-t_{k-1}=1\) and \(-t_{k+1}+t_k=1\). Global reversal of both sign patterns does not change these values.
* Opposite-side dimers have patterns \((+,-)\), \((-,+)\) and start difference \(k+1\). At the left receiver the fields are \(-t_{k+1}+t_{k+2}=1\) and \(t_k-t_{k+1}=1\). At the right receiver they are \(-t_{k+1}+t_k=1\) and \(t_{k+2}-t_{k+1}=1\).
* The trimer \((0,+),(1,-),(2,+)\) receiving from a left dimer at \(-k,-k+1\) gets endpoint fields \(t_k-t_{k-1}=1\), \(t_{k+2}-t_{k+1}=1\), and center field \(-t_{k+1}+t_k=1\).
* The trimer receiving from a right dimer at \(k+1,k+2\) gets endpoint fields \(-t_{k+1}+t_{k+2}=1\), \(-t_{k-1}+t_k=1\), and center field \(t_k-t_{k+1}=1\).
* A left dimer at \(-k,-k+1\) receiving from the trimer gets
\[
(t_k-t_{k+1}+t_{k+2},\ -t_{k-1}+t_k-t_{k+1})=(2,1).
\]
* A right dimer at \(k+1,k+2\) receiving from the trimer gets
\[
(-t_{k+1}+t_k-t_{k-1},\ t_{k+2}-t_{k+1}+t_k)=(1,2).
\]

This verifies all directions and all rows of the paper's table:

| Receiver from sender | Endpoint contributions |
|---|---:|
| Dimer from any other dimer | \((1,1)\) |
| Trimer from a dimer | \((1,1)\) |
| Left dimer from trimer | \((2,1)\) |
| Right dimer from trimer | \((1,2)\) |

If there are \(q\) components, summing the contributions gives
\[
\begin{array}{c|c}
\text{component}&\text{total }T\text{-fields in increasing position order}\\\hline
\text{left dimer}&(q,q-1)\\
\text{trimer}&(q-1,q-1,q-1)\\
\text{right dimer}&(q-1,q).
\end{array}
\]
For \(q=1\) only the trimer row occurs and all three values are zero. In particular, **not every endpoint has field \(q-1\)**. The two trimer endpoints have exactly \(q-1\); each dimer has one endpoint of field \(q-1\) and one of field \(q\). The paper states these facts correctly and its displayed minimum is correct.

Each endpoint has exactly one nearest support neighbor with opposite sign, giving nearest-neighbor field \(C\). The trimer center has two, giving \(2C\). Hence the exact whole small-field minimum on every such configuration is
\[
\boxed{\min_{i\in W}\sigma_i((-C(X+X^{-1})+T)\sigma)_i=C+q-1.}
\]
The center field is actually \(2C+q-1\). Even without computing that stronger fact, the paper's bound \(2C-R_T=\tau+2>\tau\) suffices. The threshold inequalities hold precisely when
\(C+q-1\ge C+h-1\), equivalently \(q\ge h\).

## 10. Equation (1), its quantifiers, and graph edge cases

If \(\Theta(G)\ge\tau\), finiteness gives a sparse spin attaining a minimum at least \(\tau\). Lemmas 2 and 3 give its \(q\)-element component set \(P\), with all positive differences in \(D\). The table gives \(q\ge h\ge3\). Lemma 1 therefore applies, producing a source clique with exactly \(q\le v\) vertices. Selecting \(h\) of them proves the source is YES.

Conversely, a clique of size at least \(h\) supplies one of exactly \(h\). The support construction gives \(q=h\), all active guard fields zero, and exact minimum \(C+h-1=\tau\). Thus
\[
\boxed{\Gamma\text{ has an }h\text{-clique}\ \Longleftrightarrow\ \Theta(G)\ge\tau.}\tag{1}
\]
There is no assumption that an optimiser of \(\Theta\) initially has a classified support; the classification is invoked only after choosing a support with the required lower bound.

At \(h=3\) the number of components must be at least three, exactly the lower bound needed by Lemma 1. When the graph has no edges, \(D=\varnothing\), \(T=0\), \(C=h+1\), \(\tau=2h\), \(L=4h+3\). A classified support can only have the trimer, whose minimum is \(C<\tau\), so it cannot pass. A singleton has field zero and cannot pass either. Isolated vertices introduce no extra distances and cause no problem; a clique extracted with at least three vertices cannot contain one.

As a useful optional strengthening, the same arguments prove for every graph in the main source range
\[
\Theta(G)=C+\omega(\Gamma)-1,
\]
where \(\omega\ge1\) is its clique number. A maximum clique constructs the lower bound. Any spin with minimum at least \(C\) has no negative guard field, since the negative-field upper bound is \(-\tau-1<C\); its guard fields therefore vanish. Since \(C>R_T\), the geometry proof excludes isolated points and applies unchanged. Its component count is at most \(\omega\), using Lemma 1 for counts at least three and the direct edge argument for counts one or two. The table gives the upper bound. Any remaining spin has minimum below \(C\), so cannot improve it. This strengthening is not needed to establish (1), but explains the exact source minima observed in the tests.

## 11. Full signs, walls, and equation (2): page 4

Define
\[
\Psi(K)=\max_{s\in\{-1,1\}^n}\ \min_{0\le i<n}s_i(Ks)_i.
\]
For a full sign \(s\), always interpret \(s_{-1}=-s_{n-1}\). Define a wall at \(i\) by \(s_i\ne\widetilde s_{i-1}\), and set \(e=(1-X)s\). Then \(e_i=0\) at nonwalls and \(e_i=2s_i\) at walls. Moreover
\[
\prod_{i=0}^{n-1}s_i\widetilde s_{i-1}=-1:
\]
every ordinary sign occurs twice, while the closing predecessor supplies one minus sign. The product is also \((-1)^{\#\text{walls}}\), so there is a nonempty odd number of walls. At successive walls the new sign alternates, since no sign change occurs between walls. Thus \(\sigma=e/2\) is an odd alternating sparse spin.

Conversely, if \(\sigma\) is such a spin with initial sign \(\eta\), then \(u=\sum_j\sigma_j=\eta\). Put \(s=S\sigma\). Direct negacyclic convolution gives
\[
s_i=\sum_{j\le i}\sigma_j-\sum_{j>i}\sigma_j
   =2\sum_{j\le i}\sigma_j-u.
\]
For \(\eta=1\), the prefix sums are 0 or 1, hence \(s_i\in\{-1,1\}\). Negation handles \(\eta=-1\). Telescoping gives
\[
(1-X)S=1-X^n=2,\qquad XS=S-2.
\]
Thus \((1-X)s=2\sigma\). Conversely \(S((1-X)s/2)=s\), by the same identity and cancellation of 2 in integer arrays. We have an actual bijection between full signs and sparse spins when both initial signs are included. There are \(2^n\) such spins, or \(2^{n-1}\) supports with an irrelevant initial sign fixed.

The clock field is
\[
s_i(BXs)_i=B s_i\widetilde s_{i-1}
=\begin{cases}B&\text{at a nonwall},\\-B&\text{at a wall}.\end{cases}
\]
The perturbation satisfies \(|s_i(Hs)_i|\le R_H\). Since
\(B-R_H=2\tau+1>0\), every nonwall field is positive and every wall field is negative. There is at least one wall; therefore the overall minimum is attained at a wall, strictly below all nonwall fields if any exist. At a wall, \(s_i=\sigma_i\), and
\(Hs=G(1-X)s=2G\sigma\). Consequently for each paired sign and spin,
\[
\min_i s_i(Ks)_i=-B+2\min_{i\in\operatorname{supp}\sigma}\sigma_i(G\sigma)_i.
\]
Taking maxima over the bijection proves
\[
\boxed{\Psi(K)=-B+2\Theta(G).}\tag{2}
\]
Neither symmetry of \(G\) nor symmetry of \(K\) is required. The identity holds in both source YES and source NO instances; there is no promise \(\Theta\ge\tau\). If this bridge is generalised, its real hypothesis is \(B>R_H\). It would be false to claim the chosen formula ensures that hypothesis for an arbitrary negative \(\tau\); here \(\tau>0\) was proved explicitly.

## 12. The parity ideal, lattice separation, and equation (3): pages 4–5

From \((1-X)S=2\), \(2R_n\subseteq SR_n\); also \(\mathbb ZS\subseteq SR_n\). For the opposite inclusion, \(XS=S-2\) implies by induction that every shifted generator \(X^jS\) lies in \(\mathbb ZS+2R_n\). These shifts generate \(SR_n\) additively, so
\[
SR_n=2R_n+\mathbb ZS
=\{y\in\mathbb Z^n:y_i\equiv y_j\pmod2\text{ for all }i,j\}.
\]
For the final equality, one direction follows by reducing modulo two, and the other by writing \(y=2z+cS\) with the common parity \(c\in\{0,1\}\). A useful explicit preimage is
\[
y\text{ has common parity}\quad\Longrightarrow\quad
a=\tfrac12(1-X)y\in R_n,\quad Sa=y.
\]
At coordinate zero the numerator is \(y_0+y_{n-1}\), which is even; at other coordinates it is \(y_i-y_{i-1}\), also even.

If a nonzero \(y\in SR_n\) has infinity norm one, all its coordinates belong to \(\{-1,0,1\}\). Common even parity would force \(y=0\), so its parity is odd and every coordinate is \(\pm1\). Conversely every full sign lies in the parity ideal and has norm one. Every other nonzero \(y\) has integer norm at least two. This includes \(n=1\), although the graph construction never uses so small a dimension.

Let \(P=M-K\), so \(f=PS\). The reverse triangle inequality and the convolution bound give for every array
\[
\|Py\|_\infty\ge M\|y\|_\infty-\|Ky\|_\infty
\ge(M-R_K)\|y\|_\infty,
\qquad M-R_K=2R_K+1>0.
\]
Thus \(P\) is injective on integer arrays, independently of cyclotomic irreducibility. Also \(S\) is injective, since \((1-X)Sa=2a\). In particular \(f=PS\ne0\), and the zero lattice vector has only the zero multiplier.

For a full sign, \(|(Ks)_i|\le R_K<M\). Multiplying the coordinate of \(Ps\) by \(s_i\) preserves its absolute value and makes it the positive number \(M-s_i(Ks)_i\). Therefore
\[
\|Ps\|_\infty=\max_i(M-s_i(Ks)_i)
=M-\min_i s_i(Ks)_i\le M+R_K.
\]
Every other nonzero \(y\in SR_n\) instead satisfies
\[
\|Py\|_\infty\ge2(M-R_K)=4R_K+2
>M+R_K=4R_K+1.
\]
The comparison is strict by exactly one and works even if \(R_K=0\). Since \(fR_n=P(SR_n)\) and \(P\) is injective, every shortest nonzero vector comes from the full-sign layer. Minimizing over that finite layer and then applying (2) proves
\[
\boxed{\lambda_{1,\infty}(fR_n)=M-\Psi(K)=M+B-2\Theta(G).}\tag{3}
\]
The injectivity statement is important: images of nonzero parity vectors are nonzero, and all nonzero ideal vectors are represented in the comparison.

Now \(r=M+B-2\tau=M+R_H+1\ge1\). Equations (1) and (3) imply the exact decision equivalence. Moreover \(\Theta(G)\) is an integer, as a finite maximum of finite integer minima. A source NO instance has \(\Theta\le\tau-1\), whence
\[
\lambda_{1,\infty}(fR_n)\ge M+B-2(\tau-1)=r+2.
\]
A source YES instance has \(\lambda\le r\). No rounding or strict/non-strict threshold ambiguity remains. Since the numerical radius is exponential in a polynomial of source size, the ratio \((r+2)/r\) need not be bounded away from one. This is only an additive gap.

## 13. Polynomial size, actual running time, and NP membership

### 13.1 The reduction's bit complexity

Let the graph be explicitly encoded and \(3\le h\le v\). The least-power choice obeys
\[
8R_0+16<n\le2(8R_0+16)=256A_0+64\le5440v^9.
\]
The upper bound follows from \(A_0\le21v^9\) and \(v\ge1\). Finding this power of two uses a polynomial number of bit operations, not a search through all numerical dimensions.

The guard has \(s\le n/2\) weights, and
\[
\operatorname{bits}(5^{s-1})\le1+(s-1)\log_2 5=O(n).
\]
This is an exponential numerical value with a linear bit count. With the increasing forbidden-distance enumeration, the largest *reduced coefficient* of \(A\) is actually \(2\cdot5^{s-1}\), because the last distance is \(n/2\). More generally every coefficient has magnitude at most this quantity. The paper's phrase “largest guard coefficient \(5^{s-1}\)” should read “largest guard weight,” or have a factor 2 in the coefficient bound. This is a literal correction with no complexity consequence.

Disjoint supports of the guard terms give
\[
\|A\|_1=2\sum_{j=0}^{s-1}5^j=(5^s-1)/2.
\]
Their supports are also disjoint from the nearest-neighbor and \(T\) supports, giving
\[
\|G\|_1=L\|A\|_1+2C+R_T,
\quad R_H\le2\|G\|_1,
\quad R_K\le B+R_H,
\quad \|f\|_1\le n(M+R_K).
\]
Here \(C,\tau,L\) are numerically polynomial in \(v\), since \(m\le\binom v2\). All subsequent coefficients, norms, and scalars have \(O(n+\log(v+1))=O(n)\) bits in this source range. The dense output has \(n\) coefficients and therefore \(O(n^2)\) bits. The radius also has polynomially many bits.

One explicit deterministic algorithm computes the labels and the edge-difference set, constructs a membership table for \(E_+\) on \(1,\ldots,n/2\), scans the complement while updating a weight by multiplication by 5, writes the signed coefficient arrays described in Section 3, and computes norms by integer additions and absolute values. It obtains \(H\) by one signed shift, forms \(K,M\), and outputs \(f=(M-B)S+2B-2G\) and \(r\). Naive dense convolutions would also be polynomial: \(O(n^2)\) integer products and additions with polynomial bit lengths. This is a bit-time argument, not a unit-cost assumption for enormous integers.

The actual constants are exceptionally large. At \(v=3\),
\[
b_0=82,\quad A_0=182289,\quad R_0=2916626,\quad n=33554432=2^{25}.
\]
At \(v=4\), \(n=536870912\); at \(v=5\), \(n=4294967296\). None contradicts a polynomial reduction. They do preclude a meaningful dense “tiny graph” brute-force experiment on the literal output. Powers of five have been retained exactly in the genuinely small-ring tests.

### 13.2 Nonsingularity for every legal target input

NP membership is not restricted to outputs of the reduction. For an arbitrary legal \(f\ne0\), one needs to justify the paper's assertion that the multiplication matrix \(m_f\) is nonsingular.

For \(n=2^k\), \(X^n+1\) is irreducible over \(\mathbb Q\). If \(k=0\), it is linear. Otherwise consider \((Y+1)^n+1\). Its leading coefficient is 1, its constant coefficient is 2, and every intermediate binomial coefficient is even. The last assertion follows by reducing in \(\mathbb F_2[Y]\) and repeatedly squaring: \((Y+1)^{2^k}=Y^{2^k}+1\). The shifted polynomial is Eisenstein at 2, since its constant term is not divisible by 4. Translation by 1 is an automorphism of \(\mathbb Q[Y]\), so irreducibility transfers back.

Thus \(\mathbb Q[X]/(X^n+1)\) is a field. The nonzero reduced polynomial \(f\) remains nonzero there, because its degree is less than \(n\), and multiplication by it is invertible. The coefficient-basis integer matrix \(m_f\) is therefore nonsingular over \(\mathbb Q\). Its entries are signed copies of coefficients of \(f\):
\[
(m_f)_{ij}=\begin{cases}f_{i-j},&i\ge j,\\-f_{n+i-j},&i<j.\end{cases}
\]
This matrix has full-rank lattice image \(fR_n\). The nonsingularity argument for constructed \(f\), obtained earlier from domination, is sufficient for (3) but by itself would not establish NP membership on all legal inputs.

### 13.3 Exact certificate verifier and its time bound

The paper's certificate is \(z\in\mathbb Z^n\setminus\{0\}\), with \(|z_i|\le r\). Its length is \(O(n\log(r+1))\), including signs. The verifier checks that bound and nonzeroness, solves \(m_fx=z\) over \(\mathbb Q\) exactly, and accepts iff every coordinate of the unique solution is integral. This is equivalent to ideal membership: an integral solution is a multiplier in \(R_n\), and any ideal representation is that unique rational solution.

For the bit bound, set \(F=\max(1,\|f\|_\infty)\) and \(U=\max(F,r)\). By the Leibniz determinant bound,
\[
|\det m_f|\le n!F^n,\qquad
|\det(m_f\text{ with column }i\text{ replaced by }z)|\le n!U^n.
\]
All determinants have \(O(n(\log n+\log U))\) bits. They can be computed by fraction-free elimination, with a polynomial number of arithmetic operations on polynomial-length integers. Cramer's rule then checks divisibility of each replacement determinant by the nonzero integer \(\det m_f\). Merely computing a floating point inverse would not be a verifier. Nor should one compute the determinant by enumerating \(n!\) permutations: the Leibniz formula here supplies a size bound, not the algorithm.

A convenient alternative for Lean is to certify both \(z\) and its integer multiplier \(x\), checking \(fx=z\), the radius, and nonzeroness by integer arithmetic only. Cramer's bound and \(|\det m_f|\ge1\) prove that whenever a bounded \(z\) has an integer preimage, it has
\(|x_i|\le n!U^n\); therefore this longer witness is still polynomial in input length. This route avoids verifying rational elimination as an algorithm, at the cost of formalising the determinant size bound. Either route proves NP membership.

## 14. The finite-\(p\) obstruction: page 5, Section 1.6

The PDF states \(n\ge4^p\), with an exponent. The plain extraction “4p” is not the formula. For a fixed real \(1\le p<\infty\), full signs have \(\|s\|_p=n^{1/p}\). The signed-shift operator bound yields
\[
\|(M-K)s\|_p\ge(M-R_K)\|s\|_p
\ge4(M-R_K)>2(M+R_K),
\]
since
\[
4(M-R_K)-2(M+R_K)=2M-6R_K=2.
\]
On the other hand \(2=(1-X)S\in SR_n\), and
\[
2(M-K)=f(1-X)\in fR_n,\qquad
\|2(M-K)\|_p\le2(M+\|K\|_p)\le2(M+R_K).
\]
This ideal vector is nonzero by injectivity of \(M-K\), or by its norm lower bound on the nonzero vector 2. Thus every image of a full sign is strictly longer than an explicit competitor. For \(p=2\), \(n\ge16\) suffices. These inequalities verify every step of Section 1.6. They exclude direct reuse of this specific minimum-layer proof for those finite norms, not every possible finite-norm reduction or a hardness theorem obtained differently. This section can be formalised independently after the main theorem, since the main theorem needs no real \(p\)-norm machinery.

## 15. Formalisation plan and proof dependency order

No Lean implementation has been started. The following order separates finite algebra from encoding and complexity. Choose one clear convention for \(\operatorname{Fin}(n)\) coefficients and for signed integer lifts before formalising the gadgets.

| Order | Component and intended precise result | Nature |
|---:|---|---|
| 1 | Integer arrays, negacyclic multiplication, coefficient uniqueness, ring equivalence with \(\mathbb Z[X]/(X^n+1)\), integer monomials, signed shifts, antiperiodic lift | Pure algebra |
| 2 | Shift-adjoint identities, skew quadratic form zero, coefficient \(1\)- and infinity-norm bounds, nonnegative-sum-zero lemma | Pure array algebra and finite sums |
| 3 | Odd alternating supports, their lifted alternation and invariance under signed monomial shifts; nonempty finite extrema | Finite combinatorics on arrays |
| 4 | Base-\(b_0\) no-carry extraction, Newton identities for triples, multiset root cancellation, two-term and ordered-difference uniqueness | Integer/polynomial algebra |
| 5 | Row/column family lemma and difference-clique extraction, including \(|P|=|C_\Gamma|\le v\) | Finite graph/multiset combinatorics |
| 6 | Balanced-base-five zero lemma; power-two gcd/orbit facts; zero-active-field step guard, with antipodal case | Integer arrays plus elementary number theory |
| 7 | Guard amplitude domination and Lemma 2; separate this from alternation since the guard works for arbitrary ternary arrays | Pure array algebra |
| 8 | Cyclic-diameter-to-short-arc lemma and signed translation invariance | Finite modular and integer-order combinatorics |
| 9 | No singleton, forbidden distance three, gap cases, at most one trimer, odd parity, dimer offset rules | Finite support geometry |
| 10 | Explicit source-clique support construction and span bound | Finite integer combinatorics |
| 11 | Directed component interaction computations, exact table totals, \(C+q-1\) minimum, then (1) | Pure array algebra plus graph lemmas |
| 12 | \(S\) identities, odd-wall/full-sign bijection, clock domination \(B>R_H\), then (2) | Pure integer-array algebra/combinatorics |
| 13 | Parity ideal and norm-one layer; injectivity/coercivity of \(M-K\); finite minimum formula, then (3), \(f\ne0\), \(r>0\), additive gap | Pure integer-array algebra and inequalities |
| 14 | Canonical graph/integer/list encodings, explicit construction function, output legality, trivial-source preprocessing, all bit bounds and polynomial-time algorithms | Complexity/encoding layer |
| 15 | Irreducibility for every power-two dimension, nonsingular multiplication matrix; bounded NP certificate and a polynomial-time verifier | Algebra plus NP machinery |
| 16 | CLIQUE hardness, composition of reductions, NP-completeness of the target language | Complexity theorem layer |
| Optional | Real finite-\(p\) operator bound and competing-vector obstruction | Normed real-vector analysis |

The main mathematical equivalence can first be proved over arrays, with no Turing machines. An arbitrary computable construction with polynomial output length is not enough to conclude a polynomial-time reduction: the actual construction and verifier algorithms must be bounded in a chosen bit-cost model. Likewise a mathematical decidability proof using rational inverses is not yet an NP verifier complexity proof.

For the source, there are three sensible levels of result:

1. Prove a concrete polynomial reduction from explicitly encoded CLIQUE to the target and state hardness conditional on an imported CLIQUE NP-hardness theorem.
2. If a suitable formal 3SAT NP-hardness theorem is available instead, formalise the usual 3SAT-to-CLIQUE reduction: make one vertex for each literal occurrence; connect vertices from distinct clauses unless their literals conflict; target the number of clauses. A satisfying assignment picks a compatible occurrence per clause, and a clique of that size picks one per clause and defines a consistent satisfying partial assignment. Ensure at least three nonempty clauses by duplicating a nonempty clause as necessary; handle the empty-clause and zero-clause cases separately. Then compose. This is extra source work, not a flaw in B.
3. If neither source-hardness theorem is available, a fully foundational NP-hardness theorem also needs a starting result such as Cook–Levin or an equivalent verified foundation. One cannot replace that dependency by the informal phrase “reduce from CLIQUE.”

Do not assume any particular current Lean library contains the needed complexity result without checking it. The proof above only uses mathematical statements, not an assertion about installed library coverage.

Specific Lean care points:

* Use an integer lift with Euclidean quotient/remainder. Negative exponents, negative coordinates, and repeated wraps must all carry the sign \((-1)^q\).
* State \(n>0\) globally and \(n\ge2\) for the guard-distance interval. The target language can include \(n=1\); the graph gadget's \(n\) is far larger. Distinguish residues from their chosen short integer lifts.
* Keep support adjacency, cyclic distance, and actual signed convolution as different notions. In particular \(d=n/2\) is its own unsigned distance but gives a nonzero skew operator.
* Define max/min on nonempty finite types or use explicit witnesses, so an empty-support default cannot leak into \(\Theta\). Both global spin signs can be retained initially and quotiented out later.
* Work with multisets, including repeated labels in three-term uniqueness; do not replace multiset equality by set equality. Make cancellation of a common occurrence explicit.
* Prove row/column extraction as a reusable finite relation lemma. It avoids complicated graph reasoning at that step.
* Use an auxiliary list of support positions to count runs and alternate signs. Prove “short arc then sorted linear support” before calculating the interaction table.
* The base-five argument concerns integer digits in \([-2,2]\), even at the antipode. It must be applied at each active coordinate before the orbit argument.
* Preserve exact strict margins. The guard contradiction is an integer field at most \(-\tau-1\), the center margin is 2, the layer separation margin is 1, and the final NO gap is 2.
* \(G\) and \(K\) are arbitrary nonsymmetric multipliers for the sign and lattice bridges. A spectral or symmetric-matrix assumption would be unnecessary and misleading.
* Separate input nonsingularity via irreducibility from output nonsingularity via domination. The former proves general NP membership; the latter is the elementary ingredient of (3).
* Define bit size with a harmless convention at zero and include sign bits. Prove polynomial bounds in total encoding length, not in the numerical radius or the numerical value of a guard weight.

## 16. Reproducible computational checks and their limits

Run from `/workspace/shared/jobs/hardness-power2-new`:

```sh
python3 out/auditB/check_combinatorial.py > out/auditB/check_combinatorial_results.json
python3 out/auditB/brute_checks.py > out/auditB/brute_results.json
python3 out/auditB/check_algebra.py > out/auditB/check_algebra_results.json
```

The programs use only the Python standard library, exact integers, and deterministic enumeration; the random graph samples in `brute_checks.py` use a fixed seed. Each contains assertions, so a failed check exits unsuccessfully. All three were rerun during this audit and passed.

### 16.1 Labels, extraction, guards, wraps, geometry, and table

[check_combinatorial.py](auditB/check_combinatorial.py) and [its results](auditB/check_combinatorial_results.json) check:

* Three-term uniqueness with repetitions for all labels at \(v=1,\ldots,9\), and every nonzero ordered label difference at those sizes.
* Every simple graph on \(v\le4\): 75 graph instances and 206 anchored difference-clique sets of size at least three, allowing signed differences around the anchor. All extracted sets had the exact row/column and translated/reflected clique form.
* Every ternary vector for \(n=2,4,8\) and every \(1\le d\le n/2\): 26,415 vector/distance cases for the zero-active-field implication, including the antipode. This tests more vectors than the odd alternating class.
* All 20 directed interactions among two left dimers, a trimer, and two right dimers. With five components, the total \(T\)-fields are \((5,4),(5,4),(4,4,4),(4,5),(4,5)\), exactly as derived above.
* Exhaustive anchored pair-allowed odd supports for scaled windows with \(Q=8\), \(D=\varnothing,\{1\},\{1,2\},\{1,3\}\), dimensions \(64,128,256,256\), respectively. These use small hand-chosen distance sets, not the literal source labels. The corresponding maximum small-field minima are \(4,9,14,13\), versus thresholds \(6,10,14,14\) at \(h=3\). The scaled triangle case \(D=\{1,2\}\) is YES and reaches the threshold; the others are NO. The exact support classification and \(C+q-1\) formula hold in each enumerated case. Guard and interval lemmas justify restricting to pair-allowed anchored supports; this is not a dense enumeration of all spins in dimensions 64 or larger.

[brute_checks.py](auditB/brute_checks.py) and [its results](auditB/brute_results.json) independently check:

* Actual label uniqueness through \(v=10\): 715 triple multisets and 330 ordered nonzero differences across those sizes.
* 141 graph instances, all graphs through four vertices plus empty, complete, and seeded samples through seven vertices; 840 normalized difference-clique sets of size at least three. Normalization here fixes the minimum point at zero, rather than allowing both signs around an arbitrary anchor, so its count is not the preceding script's count.
* The 26,415 single-distance ternary guard cases, of which 6,651 use \(d=n/2\); 97,655 balanced-base-five digit vectors of lengths one through seven; and 2,120 signed monomial shifts, including wraps, of all odd alternating supports at \(n=2,4,8\).
* The actual base-five aggregate guard on every odd alternating support, with its global sign fixed, in \(n=8,16\), allowed distances \(\{1,2\}\), \(T=0\), and \(h=1\) or \(h=3\): 65,792 supports. At \(h=3\) none pass, as required for an empty graph. At \(h=1\), used only as a small guard analogue outside the main source range, exactly the \(n\) shifted trimers pass. These are genuinely exhaustive whole-ring guard tests.
* Actual paper labels and \(Q=16\) for 97 graph instances through five vertices, without allocating dense enormous arrays. After anchoring a support's minimum at zero, recursively enumerate every subset of \(\{0\}\cup E_+\) with all pair differences allowed. This covers all supports surviving the proved guard and interval lemmas. There are 15,746 odd supports, 1,161 without an isolated point, and 2,749 threshold comparisons. Every no-isolate support has exactly the asserted runs and offsets; every endpoint and the trimer center has the exact field; maximum component count equals the graph clique number. The \(v=3\) triangle passes \(h=3\), and all seven other graphs on those three vertices fail. The tests include no edges, isolated vertices, and targets beyond the clique number. These are sparse actual-label checks of the remainder of (1), conditional on the guard and short-arc coverage proof.

Both guard programs retain the explicit \(n=6,d=2\) counterexample outside the allowed dimension family. This is an intentional check that the code actually uses the power-of-two restriction.

### 16.2 Full \(\Theta\), full \(\Psi\), and actual lattice-basis enumeration

[check_algebra.py](auditB/check_algebra.py) and [its results](auditB/check_algebra_results.json) exhaust all \(G\in\{-1,0,1\}^n\) for \(n=1,2,4\), with \(\tau=1\), and three additional multipliers at \(n=8\). This gives 96 bridge instances: 34 YES and 62 NO. For each it directly enumerates every full sign and every odd alternating sparse spin with both initial signs; computes \(\Theta(G)\) and \(\Psi(K)\); verifies the wall bijection and wall minimum; constructs the actual \(f\); and checks (2), (3), and the threshold/gap.

It enumerates actual ideal vectors through the multiplication lattice basis:
\[
fa=\sum_{j=0}^{n-1}a_jX^jf,\qquad a\in\{-1,0,1\}^n\setminus\{0\}.
\]
Across the cases this is 26,238 nonzero multiplier vectors, not just images of selected signs. For \(n\le4\), it also exhausts every common-parity vector in the coefficient box \([-2,2]^n\), checks the explicit integer preimage \((1-X)y/2\), and verifies its ideal image.

The multiplier search is **complete for shortest vectors** in these cases, for a proved reason. A full sign supplies an upper bound \(U\le M+R_K\). If an ideal vector \(fa\) could attain or improve it, put \(y=Sa\); coercivity gives
\[
\|y\|_\infty\le\frac{U}{M-R_K}<2.
\]
Since \(y\ne0\) has common parity, it must be a full sign. Then
\(2a=(1-X)y\), so every coefficient of \(a\) lies in \(\{-1,0,1\}\). Thus no multiplier outside the searched box can yield a missing shorter vector. The code compares the directly enumerated lattice minimum to \(M-\Psi\) and to \(M+B-2\Theta\); it does not define the minimum by those formulas.

Representative exact outputs are:

| \(n\) | \(G\) | \(\tau\) | \(\Theta\) | \(\Psi\) | \(M\) | \(B\) | \(r\) | Enumerated \(\lambda_{1,\infty}\) |
|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 4 | \((1,0,0,0)\) | 1 | 1 | −3 | 16 | 5 | 19 | 19 = \(r\) |
| 4 | \((0,0,0,0)\) | 1 | 0 | −3 | 10 | 3 | 11 | 13 = \(r+2\) |
| 8 | \((2,-1,0,1,0,0,-1,0)\) | 1 | 3 | −7 | 52 | 13 | 63 | 59 \(\le r\) |
| 8 | \((0,1,-2,0,1,0,0,-1)\) | 2 | 0 | −15 | 76 | 15 | 87 | 91 \(\ge r+2\) |

For the first two cases the program finds multiplier \((-1,0,0,0)\) and shortest vectors \((-19,-11,-11,-11)\) and \((-13,-7,-7,-7)\). They explicitly realise both the YES boundary and the exact two-unit NO gap.

A finite-\(p\) check uses \(p=2,n=16,K=(2,-1,0,\ldots,0),M=10\). The competitor \(2(M-K)\) has squared norm 260; three sampled sign images have squared norms 1264, 816, and 1264. The universal symbolic inequality in Section 14, also checked exactly in squared form, bounds every sign image above the competitor; the samples alone are not claimed to enumerate all such signs.

**Coverage limitation.** These experiments do not enumerate the literal huge ideal attached to even a three-vertex graph. Equation (1) is checked via exact actual-label sparse geometry and independent small-ring guard tests, while (2)–(3) are exhaustively checked on small unrestricted integer multipliers. No claim is made that the full graph gadget satisfies its scale-separation hypotheses in dimension 4 or 8. The symbolic proofs above provide the all-parameter result; computation is corroboration and detects sign, antipodal, and threshold errors in independent finite implementations.

## 17. Finding classification and page-by-page disposition

### (a) Real mathematical gaps/errors that would block the theorem

**None found in the stated power-of-two, coefficient-infinity, explicitly encoded setting.** In particular, neither the endpoint table, the row/column argument, the forbidden-distance guard, nor the transition to a principal ideal requires changing the construction. The orbit and minimum-layer arguments can be completed with the proofs given above.

There are necessary dependencies that must not be omitted from a fully formal theorem: a precise NP-hard CLIQUE source, irreducibility/nonsingularity for arbitrary legal target inputs, and polynomial-time construction/verifier proofs. Their compressed treatment in B is a proof-expansion obligation, not an identified false mathematical claim. Extending the guard to general even dimensions would be false, as the retained counterexample demonstrates, but B does not make that extension.

### (b) Fixable edge cases, wording, and extraction issues

1. **Guard coefficient factor two.** Replace “largest guard coefficient \(5^{s-1}\)” by “largest guard weight \(5^{s-1}\), with coefficient magnitudes at most \(2\cdot5^{s-1}\).” For the sorted enumeration equality holds at the antipode. The bit bound remains \(O(n)\).
2. **Source normalisation.** State that the graph is finite simple undirected and explicitly encoded; explain why restricting to \(3\le h\le v\) preserves NP-hardness, or supply the trivial-case outputs in Section 1. This covers small \(v\), \(h=3\), and \(h>v\) without attempting an undefined maximum over no labels.
3. **Deterministic forbidden ordering.** Specify an order, preferably increasing, to make the reduction a function. The proof is independent of that choice.
4. **Gap terminology.** A complementary arc has edge-length at least \(n-R_0\) and at least \(n-R_0-1\) empty positions. Either terminology is fine if stated consistently; no geometry estimate fails.
5. **PDF extraction.** The wall formula contains a product \(\prod_i s_i\widetilde s_{i-1}=-1\), not a stray “Q”; the finite-\(p\) hypothesis is \(n\ge4^p\), not \(n\ge4p\). These are text-extraction artifacts, not PDF errors.
6. **Endpoint phrasing.** Keep the paper's distinction between the minimum and individual endpoint fields. “All endpoints have field \(q-1\)” would be wrong; the actual table and displayed minimum are correct.

### (c) Points needing extra care in Lean

The principal risks are negative-index signs, the antipodal guard term, multiset cancellation with repeated indices, preserving odd alternation under signed shifts, nonempty finite extrema, the passage from cyclic supports to a short integer lift, and the distinction between output injectivity and input nonsingularity. Exact inequality margins and finite certificate bit bounds should be separate named lemmas. Sections 2 and 15 give their dependencies and precise statements.

The source reduction, sign bridge, and lattice separation are finite integer-array mathematics. Only the final encoded reduction and NP-membership layer need polynomial-time machines/certificates. A 3SAT reduction is optional if CLIQUE hardness is imported; without an imported source theorem, the foundational complexity chain remains an explicit additional task.

| Paper location | Audited claim | Disposition |
|---|---|---|
| Page 1, Theorem 1 and scope paragraphs | Exact varying-dimension NP-completeness and additive gap | Supported after all reductions, NP verification, and source-hardness dependency |
| Page 1, labels and Newton argument | Triple uniqueness, ordered-difference uniqueness, polynomial labels | Correct; digit bounds and multiplicity proof supplied |
| Page 1, Lemma 1 | Difference clique extraction and row/column step | Correct, including exactly three points |
| Page 2, sparse-spin definition | Odd support, sign choice, antiperiodic extension | Correct; extrema are nonempty finite integer extrema |
| Page 2, all parameter definitions | Allowed distances, four-point windows, guard, small interaction | Correct; deterministic ordering and antipodal coefficient clarified |
| Page 2, Lemma 2 | Domination, skew sum, balanced digits, orbit contradiction | Correct; complete orbit proof and antipodal case supplied |
| Page 3, Lemma 3 | Runs, gaps, short arc, unique trimer, offsets | Correct; all case distinctions and modular signs supplied |
| Page 3, converse paragraph | Clique support construction and no wrap conflict | Correct; stronger span bound supplied |
| Pages 3–4, table and (1) | Endpoint contributions, threshold iff component count at least \(h\) | Correct; all directed computations supplied |
| Page 4, walls and (2) | Odd-wall bijection, clock dominance, sign objective | Correct with explicit \(B>R_H\) |
| Pages 4–5, parity ideal and (3) | Minimum layer, coercivity, exact shortest norm | Correct; nonzeroness/injectivity and strict margins supplied |
| Page 5, threshold and gap paragraphs | Positive radius, NO norm at least \(r+2\) | Correct by integer \(\Theta\) |
| Page 5, complexity paragraph | Polynomial output and NP verifier | Correct after factor-two wording correction and standard irreducibility/bit-algorithm expansion |
| Page 5, Section 1.6 | Finite-\(p\) competitor and \(p=2,n\ge16\) | Correct; the dimension hypothesis is exponential in \(p\) |

The mathematical proof is ready to be decomposed into formal lemmas in the order above. The complexity layer should be treated as a separate deliverable with an explicitly chosen source theorem and encoding model.
