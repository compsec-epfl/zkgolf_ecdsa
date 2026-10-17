# Pinned Longfellow circuit target

The challenge pins commit `4fe092be7e8e9634cd3b27daf55695a3a416043e` from
[PR #215](https://github.com/longfellow-zk/longfellow-zk/pull/215).
The authoritative upstream relation is
[ValidEcdsaWitness in EcdsaCircuit.lean](https://github.com/z-tech/longfellow-zk/blob/4fe092be7e8e9634cd3b27daf55695a3a416043e/formal/circuits/ECDSA/EcdsaCircuit.lean#L248).
It models the constraints of
[verify_signature3](https://github.com/z-tech/longfellow-zk/blob/4fe092be7e8e9634cd3b27daf55695a3a416043e/lib/circuits/ecdsa/verify_circuit.h).

The circuit field is P-256's base field. The wrapper preserves the existing byte
interface, checks canonical key/scalar encoding, and existentially quantifies the
upstream witness. It binds `natR (w.bi.map val3) = r` and
`natS (w.bi.map val3) = n - s`. The digest is cast into the base field as the C++
verifier's `e` input is. It does not add a separate mathematical ECDSA acceptance
condition or require completeness outside Longfellow's circuit relation.

The Lean model represents selector values as 0..7; the C++ witness generator uses
the centered encoding `2*v - 7` for its polynomial mux. These are different witness
representations. The comparator checks the Lean model; the C++ tests independently
check the actual upstream implementation. No new theorem proving the C++ compiler
correct is claimed.

The model includes nonzero key/r/negative-s checks, affine precomputation equality,
the complete projective loop, final accumulator checks and scalar bounds. Hence
exceptional precomputations such as `PK = -G` remain excluded. The direct-x rule is
also preserved. Neither missing standard-ECDSA cases nor those exceptional cases
are work contestants must add.

Six Apache-2.0 modules are vendored: Nat, EC, EcdsaSpec, EcdsaCircuit, PowMod and
Pratt. All definitions are unchanged at the pin. Two `dsimp` proof steps in Nat
become `simp only [cond]` for Lean 4.34.0. Source hashes and reversible edits are
checked by `scripts/check_sources.py`. P-256 field primality is proved by the
upstream Pratt certificate, rather than assumed.

PR #215 fixes structural infinity equality in `StandardEcdsaVerify`; it does not
change C++ verification behavior. That broader specification is retained as an
upstream import, but no longer defines challenge acceptance. The challenge's
previous BN254 field and mathematical-ECDSA target have been replaced.

The upstream soundness/completeness proofs describe the relationship between its
circuit model and mathematical ECDSA under their stated hypotheses. They do not
supply the contestant's R1CS proof. The challenge asks contestants to preserve the
circuit model itself, with the explicit byte/signature envelope above.

No Google Wallet binary or production circuit hash is claimed to have been tested.
Credential hashing, trust and disclosure bindings remain application concerns.
