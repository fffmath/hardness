
YOUR JOB: JOBNAME = r6-map. Files: Rank2ModuleSVP/Problem.lean, Rank2ModuleSVP/Membership.lean,
MembershipAux.lean, MembershipCert.lean (you may edit these), new Rank2ModuleSVP/ReductionMap.lean
(+ ReductionMapAux.lean). Imports: anything committed except Reduction* (job r6-reduction is writing it).
1. v2 Theorem 1.1 covers every ODD prime: change `SVPInput.WellFormed` to require `x.q.Prime ∧ x.q ≠ 2`
   (drop q % 4 = 3), update MembershipAux's wellFormedCheck and all proofs so `moduleSVP_mem_NP` still
   holds unconditionally. Keep `SVPYes`, `moduleVector`, `powerPair`, `encSVP` unchanged.
2. The computable reduction map (paper v2 §5.3, lines ~1264-1302) on IdealCVP's `X3CList` inputs
   (IdealCVP/Complexity/X3CList.lean; `X3CLang`, `encX3C`, `toInstance`):
   - fixed outputs: malformed input → fixed NO; M = 0 (no universe) → fixed YES; zero row → fixed NO.
     v2 uses Z[ζ₃] with (2,0),(0,2) and S = 8 (YES) / S = 1 (NO): define these SVPInputs (q = 3) and
     prove their membership/non-membership in ModuleSVPLang (squared minimum 8: in the model for q=3,
     normSq ≥ 2·? — compute; prove both facts).
   - otherwise k := max K0 ((n+2)²) with K0 a parameter of the map (a later job plugs the constant from
     Reduction.lean; make the map and all theorems take `K0 C0 : ℕ` as arguments), Y := (2k)^C0,
     q := least odd prime in [Y, 2Y] found by scanning (existence by Mathlib `Nat.bertrand`), Sidon
     positions IdealCVP.cubic n (or erdosTuran), and the four generator coordinate lists in the power
     basis: U·π^k, 0, U·c − V, −QΓ, with U = Q + g², g = Σ (ζ^{d}+ζ^{-d}), V = 6Σζ^{α_j},
     π = 1 − ζ, c = h + π^{⌊k/2⌋}, Γ, S exactly as Checker.lean / RobustCenter.lean define them (import
     those modules; READ their definitions: Checker.U, Checker.V, Checker.Q, Checker.g, sepCenter, pi,
     Checker.B₀, kappa, threshold_integral). Compute via list arithmetic (Membership list ring
     multiplication, cyclic length-q coefficient vectors then power-basis conversion c_a − c_{q−1}).
   - Prove semantic agreement: `powerPair` of the produced lists equals the ring elements
     (Checker.U … * pi^k, 0) and (U*sepCenter k − V, −(Q*Γ)), and the produced threshold equals the
     integer S of threshold_integral — state these as `reductionMap_m₁`, `reductionMap_m₂`,
     `reductionMap_S` so the final assembly can combine them with Reduction.exact_X3C_encoding.
   - Prove the map is polynomial-time computable in the complexitylib sense used by IdealCVP
     (see IdealCVP's X3C → CVP reduction: IdealCVP/Complexity/X3CToCVP.lean, CompileFast*.lean,
     `PolyTimeReducible` proofs, and polytime list arithmetic in Membership*), including the prime
     scan (≤ Y+1 candidates, trial division is polynomial since Y is polynomial in n for fixed C0)
     and the bound q ≤ 2(2·max K0 ((n+2)²))^C0.
   If the full polytime proof is too long, finish the semantics and as much of the polytime proof as
   possible, and record exactly what remains.
