
YOUR JOB: JOBNAME = r4-cert. Files: Rank2ModuleSVP/MembershipCert.lean (optionally
MembershipCertAux.lean). Imports: Rank2ModuleSVP.Membership, MembershipAux, Problem, PrimeCyclotomic,
any IdealCVP module. Do NOT import Reduction*/Clearing* (another job is editing them).
GOAL: the UNCONDITIONAL `theorem moduleSVP_mem_NP : ModuleSVPLang ∈ NP encSVP`, by discharging the
premise `hcertificateBits` of `moduleSVP_mem_NP_of_resource_bounds` (Membership.lean) for an explicit
polynomial B. Follow exactly the 4-step plan in Rank2ModuleSVP/notes/r3-membership.md "Open
obligation": multiplication matrix of the two generators in the power basis (2(q-1) columns), agreement
with Membership.product, entry bounds by the encoding length, IdealCVP's exists_integer_preimage_bits
(see how IdealCVP's moduleSIVPGeneral_bounded_certificate in IdealCVP/Complexity/GeneralModule.lean
uses it) applied to a short vector bounded by powerCoeffs_abs_le_norm / exists_norm_bounded_rep, and
transfer back to multiplier lists with a polynomial bound in (encSVP x).length.
