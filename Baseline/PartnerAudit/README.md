# Partner scalar-decomposition audit

Reference: eid-privacy/spartan-backend ffbbd372afd559d7e2c4a7f7ab26f4d87cee79cb.
This is a local gadget-level reproduction, not a claim of a deployed-protocol forgery.

Reproduce:

```
python3 prepare.py
cargo +1.96.1 run --release --locked
```

`prepare.py` retrieves `allocated_point.rs`, `constant_point.rs`, and `constraints_utils.rs` at the measured partner commit and verifies their SHA-256 hashes against `sources.json`. The ONLY source change replaces its two production calls (and the cfg(test) reference-helper call) to `s.to_bits_le` with `audit_bits`. For ordinary witnesses that function calls the original. For a malicious witness with scalar field value zero, it chooses the 256 bits of the P-256 field modulus p instead of 256 zero bits. It allocates the same boolean constraints and the same field-recomposition constraint with identical names and coefficients. No constraint is weakened or deleted.

Both the variable-base multiplication (2665 constraints) and fixed-base multiplication (803 constraints) pass `TestConstraintSystem::is_satisfied()` with scalar zero and output p*G, a finite nonzero point. The honest scalar-zero witnesses return infinity. For each gadget `TestConstraintSystem::hash()` is IDENTICAL between honest and malicious execution, establishing equal constraint matrices (up to the hash check).

A composition of the exact four partner ladder gadgets plus final addition and coordinate equality also accepts:

- Q=G
- R=2G
- supplied s_inv=0
- digest=0xa1057a6ab423ff6d0200604f75f86dfac5a35eed0b764e01248f9589585925

The actual computed digest is printed by the test. The composite gadget harness has 8834 constraints; the published field variant has 8851 because of ACIR wiring/input bookkeeping absent from this harness. This is not a full ACIR serialization/proof test.

Interpretation: canonical scalar multiplication semantics are false for these constraints, because bit reconstruction is modulo p. The two s_inv uses have independent decompositions. The accepted s_inv=0 example corresponds to a perfectly valid ECDSA signature using the DIFFERENT effective inverse p mod n, so it is not itself a signature forgery. It prevents unconditional equivalence claims about the supplied scalar without specifying its allowed representatives.

Also note: the current Longfellow ValidEcdsaWitness relation has only field equality for reconstructed digest, not a natE<p bound. Therefore analogous noncanonical DIGEST ambiguity is not automatically a difference from the challenge. The exact scalar/signature mapping must be specified.

Other source observations at the measured commit:

- OPTIMISATIONS.md's listed unconstrained constants, infinity flags, and ignored high scalar limb have already been fixed in actual code.
- The naive s_inv=0,R=(0,0) path with canonical scalar bits is blocked: the next chained multiplication treats (0,0) as finite and its doubling equation yields 0=-3.
- Fixed-base window offsets use an unknown-discrete-log argument for incomplete-add noncollision, not an all-input mathematical proof. A universal Lean equivalence proof needs explicit handling or a justified restriction.

## Source and licensing boundary

No partner implementation source is distributed in this directory. The inspected
upstream commit has no tracked LICENSE, COPYING, or NOTICE file and no package
license declaration. We do not assume permission to redistribute it or assign a
license to its copied Crescent-derived code. `prepare.py` obtains those files
locally in the ignored `upstream/` directory for the audit.

To reproduce entirely from an existing local checkout, use:

```sh
python3 prepare.py --source-tree /path/to/spartan-backend
cargo +1.96.1 run --release --locked --offline
```

The expected release output is recorded in `results.log`. The primitive
noncanonical decomposition has 257 rows; strict canonical decomposition has 384.
This audit preserves the noncanonical constraints and changes only witness
choices to demonstrate their actual accepted set.
