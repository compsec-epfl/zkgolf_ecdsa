# Challenge handoff

The deliverable is a challenge-authoring package pinned to Longfellow PR #215
commit `4fe092be7e8e9634cd3b27daf55695a3a416043e`. `CHALLENGE.md` supplies page
copy, `challenge.json` metadata, and `configs/ECDSA_P256_Digest.json` the exact
proof contract. No circuit solution or measured par is supplied. Template
placeholders and zero cost slots must not be submitted as a solution or score.

The target is Longfellow’s `ValidEcdsaWitness` circuit model over the P-256
base field, with the byte/signature envelope in `Challenge/Specs/ECDSAP256.lean`.
Do not substitute the broader `StandardEcdsaVerify` proposition.

The supported toolchain is Lean 4.34.0, with exact Clean and Mathlib revisions
in `lakefile.lean` and transitive pins in `lake-manifest.json`. The inspected
zkGolf public repository uses 4.33.1; deployment would need a compatible cached
image. No deployment or remote registration is part of this deliverable.

## Reproduce comparator checks

```sh
git clone https://github.com/leanprover/comparator.git /tmp/ecdsa-comparator
cd /tmp/ecdsa-comparator
git checkout 51491237b1d2f96cca203af9c34bced6fe38e0d8
ELAN_TOOLCHAIN=leanprover/lean4:v4.34.0 lake build comparator lean4export
cd /path/to/zkgolf_ecdsa
python3 scripts/check_comparator.py /tmp/ecdsa-comparator
```

The script verifies Comparator and lean4export revision pins. Four checks cover
a valid theorem using the real acceptance relation, an unfinished proof, a
changed theorem statement, and misuse of the actual challenge template as a
solution. Logs are written to `dist/comparator-checks/`.

This local test uses upstream's development shim without Linux Landrun isolation;
use it only for the included self-authored fixtures. The deployed site's exact
checker revision and sandbox require deployment-specific validation.

## Source bundle

Run `python3 scripts/package.py`. The archive excludes local caches, dependency
checkouts, build outputs and credentials and contains a SHA-256 source manifest.
The test fixture proofs are integration checks, not an R1CS implementation.

The challenge intentionally supplies no baseline solution or measured score.
The site registration should preserve `baseline_score: null`; the cost-slot zeros
are template placeholders. Site maintainers control registry and scoring UI
integration. The copied zkGolf utility files retain a provenance notice; no
upstream license was identified, so this bundle makes no new grant of rights
for those files. See `THIRD_PARTY_NOTICES.md`.

The projective-infinity fix is pinned even if the PR changes later. Changing the
pin requires an explicit review, source-hash update and rerun of validation.
Deployment and registration are outside this local deliverable.

For direct implementation validation, run `python3 scripts/check_cpp.py
/path/to/longfellow-zk` with the checkout at the pinned commit and `clang++`
available. This evaluates the real C++ constraints on generated witnesses.
