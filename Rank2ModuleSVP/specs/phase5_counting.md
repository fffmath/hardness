
YOUR JOB: JOBNAME = r5-counting. Files: Rank2ModuleSVP/Completions.lean, Rank2ModuleSVP/Asymptotics.lean,
Rank2ModuleSVP/AsymptoticsAux.lean (all three may be rewritten for v2), new Rank2ModuleSVP/Admissible.lean
if useful. Imports allowed: Wan, Descent, Descent2, BennettPeikert, PrimeCyclotomic, Sparse, IdealCVP.
Do NOT import Checker*/GaussSum/RobustCenter (other jobs rewrite them); currently Asymptotics*.lean
import Checker — remove that dependency.
v2 §3.2 (eq. 6-10, Thm 3.4) and §4.3 Thm 4.4 (lines ~592-718, 1054-1114 of rank2svp_v2.txt):
1. Parameters: h = ⌊21k/20⌋, H = h(q−h), L = 2kq, explicit constants cntK0, cntC0; regime k ≥ cntK0,
   q odd prime, q ≥ (2k)^cntC0. Remove v1 rsK/rsT/rsH and v1 ReductionParameters (dead).
2. Theorem 3.4 under hWan : WanPowerSumEstimates: for u with u₀ = h, P with |P| ≤ √k (Nat.sqrt k),
   η ∈ {0,1}^P, t = Σ η: |F(u;P,η)| within factor [3/4, 5/4] of q^{h−t−k+1}/(h−t)! (the paper's
   relative error < 1/4). Reuse the v1 counting skeleton (ordered tuples bijection, wan_good_count_bounds).
3. Ratio bound: |F_J|/|F| < 2 (h/q)^{|J|} for |J| ∈ {1,2}, |P|+|J| ≤ √k.
4. Abstract Theorem 4.4: given P = {α_1..α_n} (distinct), ξ, n+2 ≤ √k, and a finite set of offsets
   D ⊆ ZMod q \ {0} with |D| ≤ c·n² (state with explicit card bound, e.g. |D| ≤ 100·n²+100), and a
   family of "forbidden pairs" (a, a+d), d ∈ D, each with at least one coordinate outside P, prove
   existence of x ∈ F with x_a x_{a+d} = 0 for all forbidden pairs, for k ≥ cntK0, q ≥ (2k)^cntC0.
   Phrase it so that the later job can instantiate D := D_wit ∪ D_bad and the forbidden pairs from
   v2 eq. (20) without needing anything else (e.g. predicate `forbidden : ZMod q → ZMod q → Prop`
   with the stated structure). Use the union bound O(n³h + n²h²)/q < 1.
