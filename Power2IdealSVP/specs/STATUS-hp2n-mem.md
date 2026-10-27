# hp2n-mem progress

Completed the ideal language's native NP membership proof.

- `Membership/Verifier.lean`: dyadic/length/nonzero generator checks, negacyclic multiplier
  product, binary radius scan, and exact verifier correctness for `IdealSVPLang`.
- `Membership/PolyTime.lean`: native tidy multitape-TM polynomial-time certificates for the
  checker, product, verifier, and auxiliary bound input `(d,f,[],d*r²)`.
- `Membership/Certificates.lean`: nonsingularity plus `IdealCVP.certificate_coeff_le` bounds
  every accepted multiplier; imported framing and `cvpCertificateBound_bits` give polynomial
  signed-binary witness length.
- `Membership/NP.lean`: `Power2IdealSVP.idealSVP_mem_NP :
  IdealSVPLang ∈ Cslib.Complexity.NP encIdeal`, via `mem_NP_of_witness`.

The shared radius scan is imported from
`Power2ModuleSVPSubsetSum/Membership/Radius.lean`.
All ideal files elaborate successfully, including the complete NP theorem, using
`LAKE_CACHE_DIR=/tmp/hardness-lake-cache lake env lean ... -o ...`.
The final combined Lake build of both new NP modules passed (7067 jobs), with no
warnings in the new membership files. Existing imported modules emit module-system warnings.

No open mathematical or certificate obligations for the ideal membership theorem.

Axiom audit: `idealSVP_mem_NP` uses only `propext`, `Classical.choice`, and `Quot.sound`.

Final build command:

```sh
LAKE_CACHE_DIR=/tmp/hardness-lake-cache lake build \
  Power2ModuleSVPSubsetSum.Membership.NP Power2IdealSVP.Membership.NP
```

No remaining work for hp2n-mem. No existing problem definitions or library roots changed.
