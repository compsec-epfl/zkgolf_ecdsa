# ECDSA P-256: Efficient Longfellow Circuit Verification

Build the cheapest R1CS implementation of Longfellow’s ECDSA circuit relation.
For every native input and supplied circuit witness, preserve the upstream
accept/reject result, including exceptional point-addition cases.

## Native field and interface

The circuit runs over the **P-256 base field**, as Longfellow does:

`p = 115792089210356248762697446949407573530086143415290314195533631308867097853951`.

The subgroup order is
`n = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551`.

| Native input | Field elements | Meaning |
|---|---:|---|
| pkX, pkY | 2 | Affine verification-key coordinates |
| digest | 1 | Digest already mapped into the base field |
| rx, ry, rxInv, sInv, pkInv | 5 | Signature-point coordinates and inverse witnesses |
| pre | 8 | Affine precomputation table |
| bi | 256 | Upstream Lean selector values, 0..7 when valid |
| intX, intY, intZ | 3 × 255 | Projective intermediate-state witnesses |

These are three statement fields and 1,034 source-witness fields. In a proof-system
integration the source witness is private; being an `Input` in the Lean circuit
API does not make it public. The signature is encoded in that witness, rather
than supplied as a separate byte array.

The acceptance relation is exactly:

```lean
ValidEcdsaWitness w { X := pkX, Y := pkY } digest n params
```

`params` fixes P-256 and 256 scalar bits. Fixed-size vectors in the interface map
to the upstream witness lists. There are no caller assumptions: key validity,
selector ranges, inverse checks, table equalities and loop constraints are all
part of the relation. There is no extra byte parsing or signature binding envelope.

Correctness is **pointwise in the supplied witness**. An optimized circuit may add
internal wires, but must accept exactly the same native input/witness tuples.
Merely proving that some signature exists for the key and digest is insufficient.

The pinned source is `ECDSA/EcdsaCircuit.lean` at commit
`4fe092be7e8e9634cd3b27daf55695a3a416043e`
([PR #215](https://github.com/longfellow-zk/longfellow-zk/pull/215)). The authoritative
wrapper is `Challenge.Specs.ECDSAP256.Spec`; the comparator checks its exact types.

> Longfellow uses direct-x signature verification and excludes exceptional affine-table additions.

The formal model uses selector values 0..7. The C++ implementation represents
these as `2*v - 7` for its mux; this is a witness-encoding conversion, not a change
to the target’s acceptance conditions. This challenge pins the Lean circuit model,
not an independently certified production binary or C++ compiler.

## Scoring and proofs

Score = additional witness allocations + R1CS constraint rows. The fixed 1,037
input field elements are common to every submission and are not counted as
additional allocations. Cost-slot zeros are placeholders, not a baseline score.
The circuit has unit output.

Submissions provide a Clean circuit and the seven template obligations:
soundness, completeness, exact cost, R1CS structure, witness-generation IR,
computable witnesses and lawful requirement channels. Completeness is relative
to the pointwise circuit relation, not all ordinary-ECDSA signatures.

Only standard Lean axioms are permitted. P-256 primality is proved by the imported
Longfellow Pratt certificate. Template `sorry` placeholders and native-decide proof
axioms are not accepted in submissions.

## Scope

This challenge isolates one ECDSA circuit invocation. Credential hashing,
mdoc/COSE parsing, device-key commitments, age predicates and the full credential
proof are outside its scope. The native digest is already a field element; message
hashing and byte-to-field conversion happen before this component.

No contestant R1CS baseline is supplied. ECDSA is not post-quantum.
