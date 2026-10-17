# Third-party material

- Six Longfellow Lean modules are vendored under `vendor/longfellow/ECDSA/`
  from PR #215 commit `4fe092be7e8e9634cd3b27daf55695a3a416043e`.
  Apache-2.0 license retained at `vendor/longfellow/LICENSE`. Two proof-only
  tactic adaptations in Nat.lean are recorded in `docs/references.md`;
  `docs/longfellow-sources.json` records original and local source hashes.
- C2SP/Wycheproof's selected corpus is copied unchanged at its recorded revision.
  Its Apache-2.0 license is retained in `vectors/LICENSE-Wycheproof`.
- `Challenge/Utils/CostR1CS.lean`, `Challenge/Utils/WitgenIR.lean` and comparator
  template structure originate in zksecurity/zk-golf-challenges, downloaded
  from https://zk.golf/challenges.tar.gz on 2026-10-15. Snapshot provenance is
  in `docs/zkgolf-source.json`. No upstream license was identified for those
  helpers; this package does not grant redistribution rights to that material.
- Clean and Mathlib are fetched as pinned dependencies, not included in the
  source bundle. RustCrypto p256 and its dependencies are pinned by Cargo.lock
  and fetched by Cargo; their source is not vendored.

No Sparkle, ETHCryptoLean or ML-DSA implementation is included.

`reference/cpp/probe.h` adapts Longfellow’s Apache-2.0 circuit test helper; its
copyright header and the upstream license are retained.
