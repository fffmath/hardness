
YOUR JOB: JOBNAME = r5-separation. Files: Rank2ModuleSVP/RobustCenter.lean (rewrite for v2), new
Rank2ModuleSVP/Separation.lean if useful. Imports: Descent, Descent2, BennettPeikert, Sparse,
SparsePolynomial, PrimeCyclotomic. Do NOT import Checker*/Completions/Asymptotics*.
v2 §3.3 (lines ~719-798): Lemma 3.5 (already: Sparse.sparse_tools_i, second_shell — re-export or
wrap with v2 names), Lemma 3.6 (SparsePolynomial.sparse_tools_ii), c := h + π^{⌊k/2⌋} (eq. 11) with
h = ⌊21k/20⌋, and **Theorem 3.7**: for k ≥ sepK0, q odd prime ≥ (2k)^sepC0 (or simply q ≥ some
explicit polynomial in k — whatever the proof needs, e.g. 2k ≤ q and k − ⌊k/2⌋ > 5, 2k/5+6 ≤ ⌊k/2⌋),
every nonzero w with normSq w ≤ 3q satisfies dist(wc, ramifiedIdeal k)² > L/10 = kq/5, i.e.
∀ a ∈ ramifiedIdeal k, 10·normSq (w*c − a) > 2kq (state in ℤ; ideal distance as min, reuse v1
idealDistanceSq if convenient). The v1 file proved an L/100 version with q-derived parameters; adapt
the same polynomial argument (sparse reps of e and w, (X−1)^m divisibility, Lemma 3.6) to v2's
constants. Also prove the coefficient-sum fact Σ c_a = h for the explicit representative of
h + (1−X)^{⌊k/2⌋} (needed for Lemma 3.3 / Cor 4.5).
