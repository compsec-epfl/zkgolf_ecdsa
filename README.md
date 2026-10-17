# Longfellow ECDSA P-256 zkGolf challenge

Optimize Longfellow’s ECDSA circuit behavior as R1CS **over the P-256 base field**.
Preserve its exceptional-case rejections. Correctness targets the pinned
`ValidEcdsaWitness` circuit model, not the broader `StandardEcdsaVerify` specification.

[Challenge statement](CHALLENGE.md) · [Trusted relation](Challenge/Specs/ECDSAP256.lean)
· [Interface](Challenge/Instances/ECDSA_P256_Digest/Interface.lean)
· [Comparator contract](configs/ECDSA_P256_Digest.json)

```sh
scripts/bootstrap.sh
scripts/check.sh
python3 scripts/check_cpp.py /path/to/longfellow-zk
python3 scripts/check_comparator.py /path/to/pinned/comparator
python3 scripts/package.py
```

The upstream checkout for the C++ check must be at
`4fe092be7e8e9634cd3b27daf55695a3a416043e`
([PR #215](https://github.com/longfellow-zk/longfellow-zk/pull/215)).
The C++ adapter evaluates the actual `verify_signature3` constraints on generated
witnesses. The 276-case corpus also has Lean and RustCrypto-based diagnostics,
retaining distinct ordinary-ECDSA, direct-x and circuit-path expectations.

The byte envelope binds the supplied key, 32-byte digest and signature to the
circuit model. The digest is cast into the P-256 base field at its native input
boundary. See the exact relation for its binding rules.

This package defines the challenge; it does not supply a contestant circuit or
measured baseline. See [validation](docs/validation.md),
[provenance](docs/references.md) and [handoff](docs/publication.md).
