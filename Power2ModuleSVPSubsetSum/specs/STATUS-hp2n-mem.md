# hp2n-mem progress

Proved:

- `Membership/Radius.lean`: shared exact coefficient-radius scan, native runtime
  certificate, and squared norm bound `d*T²`.
- `Membership/Verifier.lean`: exact executable checks and correctness for the fixed
  arbitrary-radius module language, with two signed-binary integer multiplier lists.
- `Membership/PolyTime.lean`: native tidy multitape-TM certificates for the verifier,
  plus polynomial-time auxiliary bound inputs with squared bound `2*d*T²`.
- `Membership/Certificates.lean`: Cramer coefficient bound for every accepted pair
  and polynomial framed witness length, reusing the old general matrix and bit bounds.
- `Membership/NP.lean`: `Power2ModuleSVPSubsetSum.moduleSVP_mem_NP`, via
  `Cslib.Complexity.mem_NP_of_witness` and the paired integer-list decoder.

Exact endpoint:

```lean
Power2ModuleSVPSubsetSum.moduleSVP_mem_NP :
  Power2ModuleSVPSubsetSum.ModuleSVPLang ∈
    Cslib.Complexity.NP Power2ModuleSVPSubsetSum.encSVP
```

Validation:

- All four module-specific files directly elaborated with `lake env lean -o ...`;
  exit 0 and no warnings.
- `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.
- Combined Lake build of both new NP modules passed (7067 jobs), with no warnings in
  the new membership files. Existing imported modules emit module-system warnings.
- No mathematical obligations remain open.

Final build command:

```sh
LAKE_CACHE_DIR=/tmp/hardness-lake-cache lake build \
  Power2ModuleSVPSubsetSum.Membership.NP Power2IdealSVP.Membership.NP
```

No remaining work for hp2n-mem. No existing problem definitions or library roots changed.
