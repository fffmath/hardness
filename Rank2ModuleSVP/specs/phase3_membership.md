
YOUR JOB: JOBNAME = r3-membership. Files: Rank2ModuleSVP/Membership.lean (and optionally
Rank2ModuleSVP/MembershipAux.lean). Imports allowed: Rank2ModuleSVP.Problem, Rank2ModuleSVP.PrimeCyclotomic,
and any IdealCVP module.

GOAL: prove `theorem moduleSVP_mem_NP : ModuleSVPLang ∈ NP encSVP` (complexitylib `NP`), i.e. the
upper-bound half of the paper's NP-completeness (Thm main-intro, "in NP" part; see intro.tex / pre.tex
/ reduction.tex for the paper's remarks). Model your proof on IdealCVP's
`moduleSIVPGeneral_mem_NP` (IdealCVP/Complexity/GeneralModule.lean, ~lines 116-445), which does the same
for power-of-two cyclotomics: list-ring arithmetic verifier, `moduleGeneralVerifier`, polynomial-time
compilation (IdealCVP/Complexity/Compile*.lean, Verifier.lean, CertificateBits.lean, Witness.lean), and a
bounded-certificate theorem (`moduleSIVPGeneral_bounded_certificate`, IntegerPreimage / CertificateBound).
Steps:
1. List-level arithmetic in Z[x]/(Φ_q) for prime q in the power basis 1..x^{q-2}: multiplication via
   cyclic convolution mod x^q-1 followed by reduction with x^{q-1} = -(1+...+x^{q-2}); prove it agrees
   with `powerElement`/`classOf` multiplication in `IntegerRing q`. Computable `pairNormSq` on lists
   (canonical norm q Σ z_a² − (Σ z_a)² on the length-q coefficient vector, or whatever matches
   PrimeCyclotomic's `normSq`/`pairNormSq` — prove equality).
2. A Bool well-formedness check equivalent to `SVPInput.WellFormed`: primality of q is decidable in
   poly time because q is encoded in UNARY in encSVP (= IdealCVP.encModuleSIVP) — check this in the
   encoding and use trial division; lengths; q%4=3; determinant ≠ 0 via list arithmetic; threshold ≥ 0.
3. Verifier on (input, certificate (z,w) as lists) checking the vector is nonzero and norm ≤ S.
4. Certificate bound: if x ∈ ModuleSVPLang there is a witness (z,w) whose coefficients have bit size
   polynomial in the input length (Cramer / adjugate over the power basis: the module vector v has
   ‖v‖² ≤ S so its coefficients are bounded; (z,w) = M⁻¹ v with M the 2(q-1)×2(q-1) integer matrix
   of the module, so z,w have entries bounded via determinant/Hadamard; reuse IdealCVP's
   exists_bounded_integer_preimage / CertificateBound machinery if it fits).
5. Polynomial-time verifier via IdealCVP's compile pipeline, concluding `moduleSVP_mem_NP`.
If the full chain is too long for this round, finish as many layers as possible with clean statements
(e.g. a `theorem moduleSVP_mem_NP_of_resource_bounds` in the style of IdealCVP's
`principalCVP_mem_NP_of_resource_bounds`), and record precisely what is missing.
