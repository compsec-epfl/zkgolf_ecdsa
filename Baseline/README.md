# Baselines for the Longfellow P-256 challenge

Score = additional witness allocations + R1CS rows, over the P-256 base field.
Nothing here is a submission (no end-to-end soundness/completeness proofs); these are measuring sticks.
`OptimizationLemmas.lean` proves local algebraic/bit-comparison facts only.

The newest [projected-signature experiment](Projected/README.md) scores **9,267**,
47.55% below the partner reference. Its change of mathematical representation is
proved in Lean; its complete circuit proof remains unfinished.

## 1. Longfellow's relation, lowered literally to R1CS

`Baseline/Circuit.lean` transcribes `verify_signature3`
(`lib/circuits/ecdsa/verify_circuit.h` at `4fe092be7e8e9634cd3b27daf55695a3a416043e`) gate for gate
as a Clean circuit and is counted with the challenge's own `Challenge.CostR1CS.circuitCount`.

| | allocations | rows | score |
|---|---:|---:|---:|
| Longfellow `verify_signature3`, literal lowering | 11,375 | 12,415 | **23,790** |
| Previous optimized lowering | 9,441 | 10,481 | **19,922** |
| Further optimized lowering (`Optimized.lean`) | 9,296 | 10,334 | **19,630** |

The latest score saves **292** over the prior optimization (145 allocations + 147 rows),
and **4,160 / 17.49%** against the literal lowering. It remains 1,962 above the partner's
17,668 reference score, which targets a different relation.

The optimized circuit retains the boolean selector decomposition and binary-tree point mux.
The latest changes are:

* Replace the two `< n` comparators with inclusive comparisons to `n-1`. For each zero-bit
  run, let `missing` count missing bound-one bits in the preceding prefix and `sum` count
  set bits in the zero run. Assert `missing * quotient = sum`. If `missing=0`, the run must
  be zero; otherwise a quotient exists and the prefix is already smaller (or an earlier
  constraint has rejected it). Both sums are at most 256, below the field characteristic.
  Each of the 34 zero runs costs one allocation and one row per scalar.
* Substitute `(0,1,0)` into the first addition before lowering. The exact result is
  `(tx*ty, ty*ty, ty*tz)`; this preserves the original projective scale rather than
  replacing the result by the normalized table point.

`OptimizationLemmas.lean` proves the exact first-addition identity, the quotient gate's
zero-implication semantics, and a bit-level gated lexicographic comparison theorem. It
**does not** yet connect the grouped field-sum implementation and the whole Clean circuit
to `ValidEcdsaWitness`, nor supply the submission's `mainCost` proof. Counts below are
measured using the challenge counter, not certified by a completed submission proof.

Reproduce the local lemmas and full circuit checks:

```sh
lake build baseline Baseline.OptimizationLemmas
lake exe baseline --optimized
```

There is no established lower bound showing that the partner's 17,668 score is unreachable
for the pinned relation. The earlier estimate in the discussion was not such a proof.

Lowering conventions (see the header of `Circuit.lean`): linear ops free; each non-constant product
is one row and one wire when used as a multiplication operand; an assertion keeps one product in its
own row; constants fold; shared sub-terms (selector powers, comparator nodes) built once; unused
comparator outputs not built. The mux polynomials are in `2v-7` (the challenge note), with Lean's
`0..7` selector as input. The structure (12 products per `addE`, 11 per `doubleE`, degree-8
Lagrange mux, tree comparator against the constant order) is Longfellow's own.
This is one specific lowering, not the only one a reader could choose.

Checks (run `lake exe baseline`; `--count-only` skips the vector tests):

* 0 assertions fail the challenge's own single-row predicate (`r1csProducts ≤ 1`).
* Differential test against a Bool transcription of `ValidEcdsaWitness`, on the same full witness:
  all 252 vectors in `vectors/cases.json` that have a native witness agree (166 accepted,
  86 rejected); 24 byte-format-only cases (bad sizes) have no native witness and are skipped.
  Single-field mutations of accepted witnesses (all statement/witness fields, selected `bi`/`int_*`
  positions, deltas ±1) are rejected by both: 232/232 agree in the full run (4 witnesses).
* The optimized comparator additionally passes 2,568 order/field-boundary, bit-transition and
  deterministic pseudo-random tests against integer `< n`. These exercise its actual Clean
  constraints and generated quotient witnesses; every row passes the R1CS shape check.
* `lake build baseline Baseline.OptimizationLemmas` passes, including the three local theorems.
* This establishes agreement on a finite corpus plus the stated local lemmas, not a proof
  of whole-circuit equivalence. The full `soundness`, `completeness` and `mainCost` submission
  obligations remain outstanding.

## 2. The partner's Noir ECDSA (eid-privacy/spartan-backend)

Measured with the partner's own toolchain: Noir fork `eid-privacy/noir` tag `t256-v0.26-1`
(nargo 1.0.0-beta.26), `spartan-backend` commit `ffbbd372afd559d7e2c4a7f7ab26f4d87cee79cb`,
`spartan-backend -c <circuit>` (Vega backend `ShapeCS`, unpadded). Source:
`circuits/c0102_signature_vanilla_equation` with SHA-256 removed and all inputs as `Field`
(the closest match to this challenge's native interface).

| variant | constraints | aux vars | input vars | additional vars | score |
|---|---:|---:|---:|---:|---:|
| digest + pk + R as `Field` | 8,851 | 8,823 | 6 | 8,817 | **17,668** |
| digest as `Field`, pk and R as `[u8;32]` | 9,044 | 9,974 | 130 | 9,844 | 18,888 |
| c0102 as-is (with SHA-256 over 218 bytes) | 117,401 | 121,858 | 347 | 121,511 | 238,912 |

The 8,851 includes one row per public input (2). `fixed_base_constraint_count` in their test suite
prints 803 (fixed-base msm) and 2,665 (variable-base msm), matching the standalone circuits.

**This is a different encoding of ECDSA validity.** The partner supplies R and an
inverse-signature scalar and evaluates four scalar multiplications. Equivalence
requires specifying the scalar representatives and how the actual signature is bound.

A source audit at the measured commit found that the old OPTIMISATIONS.md warnings
about unconstrained constants, infinity flags and ignored high scalar limbs were
already fixed. The simple canonical-zero-inverse / (0,0) attack is also blocked.
Those are not reasons to dismiss the partner's score.

The audit did reproduce a distinct issue: field bit recomposition permits a scalar
0 to use the bits of p. The exact ladder constraints then accept p*G instead of the
canonical result infinity. A composed example with supplied inverse 0 passes, but
corresponds to another valid signature, so it is not a demonstrated forgery. The
[reproducible audit](PartnerAudit/README.md) records the precise scope and source hashes.
Longfellow itself permits a noncanonical digest lift, so that behavior alone is not
an ECDSA validity discrepancy.

## 3. A substantially smaller projected-signature circuit

[Projected/README.md](Projected/README.md) records a measured **9,267** score:
4,631 additional variables and 4,636 R1CS rows. It uses five fixed statement fields
and counts all auxiliary data. This is **47.55% below** the partner's 17,668.

The gain comes from a different internal representation, joint scalar multiplication,
constant generator tables and ELM double-and-add formulas. It does not come from
omitting the retained Longfellow validity checks. The P-256 representation bridge is
proved in Lean, but the whole Clean implementation is not yet a proved submission.
The current pointwise-witness challenge remains unchanged.
