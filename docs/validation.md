# Validation of the circuit target

Native-interface validation (2026-10-18; C++ adapter evidence retained from the unchanged pinned implementation):

| Check | Result |
|---|---|
| Lean 4.34.0 challenge build | Passed |
| Infinity/exceptional-affine regressions | Passed |
| Trusted axiom audit | 4 roots passed; standard axioms only |
| Lean circuit-path vectors | 276/276 |
| RustCrypto-based vector checks | 276/276; 262 original-message checks |
| External C++ byte-adapter diagnostics | 276/276 (200 C++, 76 envelope rejections) |
| Comparator positive/negative checks | 4/4 |
| Source hashes and deterministic corpus | Passed |

The authoritative challenge relation wraps Longfellow's `ValidEcdsaWitness` at
commit `4fe092be7e8e9634cd3b27daf55695a3a416043e`. The circuit field is P-256's base
field. The wrapper directly checks the supplied native witness.

## Vector coverage

The 276 inputs comprise 262 unchanged Wycheproof cases and 14 local regressions.
The tested Longfellow path accepts 166 and rejects 110. Expected ordinary ECDSA,
direct-x and circuit-path results are stored separately. Fourteen inputs are
ordinary-ECDSA valid but rejected by the circuit path: three direct-x overflows
and eleven exceptional table cases (including existing upstream fixtures).

- RustCrypto p256 0.13.2 verifies the ordinary signatures and independently
  reconstructs the point and table exceptions for all 276 inputs. All 262
  upstream messages are also checked with the message API.
- The Lean oracle uses upstream projective arithmetic, affine equality checks,
  selectors and the circuit loop to test generated witnesses.
- `scripts/check_cpp.py` compiles a focused adapter against the pinned, unmodified
  C++ `verify_signature3` evaluator and witness generator. It evaluates 200 cases;
  the other 76 fail the declared byte/canonical-scalar envelope before the core
  circuit is called. See `cpp-validation.json`.

These tests establish observed agreement on the corpus, not a universal decision
procedure for existential witnesses. Challenge acceptance checks the supplied native witness directly using the
upstream relation, not an existential statement or executable oracle. The Lean model uses
selectors 0..7; C++ uses their centered encoding 2*v-7.

## Proof and integration checks

`scripts/check.sh` checks original/local source hashes, deterministic corpus
reconstruction, the Lean build, regressions, axiom policy and vector oracles.
`Tests/Regressions.lean` retains the PR's infinity-representation regression and
checks that G+(-G) has zero Z and nonzero Y. A general Lean lemma proves that such
a point cannot satisfy the affine point-equality assertion.

The trusted-root audit covers the wrapper, `ValidEcdsaWitness`, scalar
multiplication and the Pratt primality proof. Only standard Lean axioms are
allowed. No BN254 or P-256 primality axiom is added.

The comparator checks acceptance of a valid proof using the actual target,
and rejection of an unfinished proof, changed statement and template submitted
as a solution. Its exact revisions and outcomes are recorded in
`comparator-validation.json`. It is tested with self-authored fixtures using the
upstream development shim, not a production sandbox.

No R1CS baseline, proof of the C++ compiler, production deployment or full
credential protocol is claimed. Contestants must prove equivalence to the pinned
circuit relation, not completeness for all mathematical ECDSA inputs.

The 276 serialized fixtures remain external adapters after the native-interface
migration. Their 76 byte-envelope rejections do not establish native constraints.
The comparator positive fixture now proves definitional equivalence directly to
`ValidEcdsaWitness` for the supplied native input/witness tuple. The fixed 1,037
input elements are outside additional-allocation scoring.

The native regression also proves that a supplied witness with `rx_inv = 0`
cannot satisfy the target, independently of the key or digest.
