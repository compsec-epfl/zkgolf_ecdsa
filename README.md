# Longfellow ECDSA P-256 zkGolf challenge

Optimize Longfellow’s native ECDSA constraint check as R1CS over the P-256 base
field. Preserve `ValidEcdsaWitness` **pointwise**, including exceptional-case
rejections and checks on every supplied witness. No byte interface or separate
signature envelope is added to the trusted relation.

[Challenge statement](CHALLENGE.md) · [Trusted relation](Challenge/Specs/ECDSAP256.lean)
· [Native interface](Challenge/Instances/ECDSA_P256_Digest/Interface.lean)
· [Comparator contract](configs/ECDSA_P256_Digest.json)

```sh
scripts/bootstrap.sh
scripts/check.sh
python3 scripts/check_cpp.py /path/to/longfellow-zk
python3 scripts/check_comparator.py /path/to/pinned/comparator
python3 scripts/package.py
```

The C++ checkout must be at `4fe092be7e8e9634cd3b27daf55695a3a416043e`
([PR #215](https://github.com/longfellow-zk/longfellow-zk/pull/215)).
External byte vectors remain test adapters: they generate source witnesses and
compare the Lean arithmetic path, RustCrypto and actual C++ constraint evaluator.
Their encoding rejection cases are not constraints of the native challenge.

This package defines a single signature-component optimization challenge; no
contestant circuit or measured baseline is supplied. See
[validation](docs/validation.md), [provenance](docs/references.md), and
[handoff](docs/publication.md).
