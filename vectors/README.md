# Vector provenance and expectations

The unchanged pinned C2SP/Wycheproof P-256/SHA-256/P1363 corpus supplies 262 cases.
`docs/sources.json` records its source and hash. The remaining 14 cases cover
canonical encoding, the generator key, direct-x overflow, and four exceptional
affine-table additions. Total: 276 cases; 166 accepted, 110 rejected on the tested
Longfellow generated-witness path.

`cases.json` retains three separate expectations:

- `standard_expected`: ordinary ECDSA; original upstream classifications unchanged.
- `direct_x_expected`: ordinary ECDSA restricted to direct x-coordinate equality.
- `expected`: Longfellow generated-witness/circuit checks, including table exceptions.

Wycheproof 115 and 257 and the constructed overflow case distinguish direct-x.
Wycheproof 215–220, the alternate-s generator case, and the four added table
exceptions additionally distinguish the circuit from the direct-x specification.
The alternate-s case is not generally interchangeable when it changes a table
addition into infinity.

`import_vectors.py` deterministically derives expectations with a small affine
model. RustCrypto independently checks the ordinary signatures, reconstruction
and exception conditions. The Lean oracle uses upstream projective arithmetic,
precomputation equality and the circuit loop. `check_cpp.py` runs the actual pinned
C++ evaluator for all cases that pass the explicit byte/canonical-scalar envelope.

These are diagnostic checks on generated witnesses, not a proof deciding all
possible witnesses. The authoritative relation directly checks the supplied upstream witness.

## Native challenge boundary

These serialized fixtures are external test adapters, not native challenge inputs.
Their signatures generate specific source witnesses. A failing fixture means that
adapter or generated witness fails; it does not mean no valid signature exists for
the same key/digest. The native challenge accepts pkX, pkY, digest and a supplied
source witness, and checks ValidEcdsaWitness pointwise. The old byte-envelope and
existential-signature wrapper are no longer part of the trusted definition.
