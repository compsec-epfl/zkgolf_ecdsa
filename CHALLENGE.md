# ECDSA P-256: Efficient Longfellow Circuit Verification

Build the cheapest R1CS implementation of Longfellow’s ECDSA circuit relation.
Match its accepted inputs and its rejections, including exceptional point-addition
cases. The target is the pinned `ValidEcdsaWitness` relation, not the broader
mathematical ECDSA specification.

## Field and inputs

The circuit runs over the **P-256 base field**, just like Longfellow’s ECDSA circuit:

`p = 115792089210356248762697446949407573530086143415290314195533631308867097853951`.

This is neither BN254 nor the P-256 scalar field. P-256 curve-coordinate arithmetic
is native circuit-field arithmetic. Its subgroup order is
`n = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551`.

The byte interface is retained. Each byte occupies one field element; the caller
establishes only that these elements lie in `[0,256)`.

| Input | Bytes | Encoding |
|---|---:|---|
| publicKey | 64 | Affine x || y, unsigned big-endian; no SEC1 prefix |
| digest | 32 | Supplied unsigned big-endian digest |
| signature | 64 | P1363 r || s, unsigned big-endian |

The wrapper checks lengths, canonical key coordinates (`x,y < p`), and canonical
nonzero signature scalars (`r,s < n`). It requires the existence of a Longfellow
witness satisfying `ValidEcdsaWitness` with those key coordinates and the digest
cast into the base field. Its selector streams must encode the supplied `r` and
`n − s`, binding the supplied signature to the circuit witness. The digest has the
upstream field-input semantics, including reduction modulo `p` at that boundary.

The relation retains Longfellow’s affine precomputation requirements, nonzero
checks and all loop constraints. Contestants must not expand acceptance to
ordinary-ECDSA inputs that this relation rejects, such as `PK = −G`.

> Longfellow uses `r = R.x` directly and excludes exceptional affine-table additions.

The authoritative definition is `Challenge.Specs.ECDSAP256.Spec`, wrapping
`ValidEcdsaWitness` from `ECDSA/EcdsaCircuit.lean` at commit
`4fe092be7e8e9634cd3b27daf55695a3a416043e`
([PR #215](https://github.com/longfellow-zk/longfellow-zk/pull/215)). The exact pinned
Lean relation prevails over this summary. `StandardEcdsaVerify` is not the challenge’s
acceptance relation. The PR’s specification correction does not alter the C++ circuit.

## Scoring and proofs

Score = witness allocations + R1CS constraint rows. The circuit has unit output.
Cost slots in `Cost.lean` are replaced during checking; their zeros are placeholders.

Submissions provide a Clean circuit and the seven template obligations:
soundness, completeness, exact cost, R1CS structure, witness-generation IR,
computable witnesses and lawful requirement channels. Completeness is relative
to the circuit relation above, including its existing restrictions.

Only standard Lean axioms are permitted. P-256 primality is proved by the imported
Longfellow Pratt certificate. No extra field-primality axiom is needed. Template
`sorry` placeholders and native-decide proof axioms are not accepted in submissions.

## Credential composition

The supplied digest isolates signature verification. The surrounding credential
proof must bind it to the credential encoding and hash and establish issuer trust
and disclosure predicates. The interface does not assign public/private visibility.
Message hashing and credential parsing are outside the score.

This is an optimization challenge for the pinned Longfellow circuit model with
an explicit byte/signature binding envelope. It is not a claim about a particular
deployed Google Wallet binary. No contestant R1CS baseline is supplied. ECDSA is
not post-quantum.
