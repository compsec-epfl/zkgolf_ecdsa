# Projected-signature ECDSA experiment

**Measured score: 9,267 = 4,631 additional variables + 4,636 R1CS rows.**
This is 8,401 (47.55%) below the measured partner field-input variant's 17,668.
The comparison counts every auxiliary bit, table coordinate, offset coordinate,
inverse and intermediate in this experiment; only five statement fields are free.
The partner variant has six free input fields. Counting those inputs too gives
9,272 versus 17,674, so the input-count difference does not explain the gain.

This is an experimental baseline, **not a completed challenge submission**.
The current challenge checks supplied Longfellow intermediates point by point.
This experiment instead binds `(pk_x, pk_y, digest, r, s)` and existentially chooses
its internal witnesses. It must be used with the projected-signature contract,
not submitted under the current pointwise-witness contract. The trusted challenge
files have not been changed.

## Why it is smaller

The partner computes four scalar multiplications through an inverse-signature
representation. Here we directly check Longfellow's three-term equation:

```
[E]G + [r]Q + [n-s]R = infinity,  R.x = r
```

The generator multiplication uses 128 constant two-bit windows. The other two
multiplications share a 256-step ladder with four-way table selection. Each
ladder step uses the Eisentraeger–Lauter–Montgomery double-and-add identity,
omitting the intermediate y coordinate. See the original
[ELM circuit discussion](https://github.com/zcash/zcash/issues/3924).

A prover chooses an on-curve offset H. Alternating signed offsets keep every
selected table entry affine, including when both scalar bits are zero. Every
ordinary-addition denominator and the first ELM denominator has an explicit
inverse constraint. The second ELM denominator is provably nonzero from the
other equations and curve nonsingularity; checking it again would waste 512
score points. The corresponding doubling guard is also redundant. The final
step constrains the target directly instead of allocating another output point.

The scalar ranges, nonzero checks, public-key/signature-point curve checks and
original Longfellow precomputation checks are retained. In particular, this does
not silently admit the exceptional public keys excluded by the pinned relation.

The digest is a field element. As in Longfellow, the internal 256-bit integer E
can be either the canonical digest or `digest + p` when the latter fits. The
extra test for `E = p+1`, field digest `1`, prevents a canonicalization change.

## What is proved

The representation bridge states that existence of a Longfellow witness with
bound r, s and digest is equivalent to a relation without its intermediate
coordinate arrays. Its right-hand side retains the original exceptional cases
and the integer digest lift. It does not redefine validity as unrestricted
standard ECDSA.

`Algebra.lean` proves the ELM identities, affine curve-equation preservation and
redundant-denominator results. `P256Algebra.lean` checks the concrete P-256
nonsingularity hypotheses. `AffineBridge.lean` and `ProjectiveBridge.lean` prove
that the affine and ELM row equations produce the same group points as
Longfellow's addition and doubling. `OffsetExistence.lean` proves the finite-exception
counting argument abstractly. The bridge modules connect the original witness
relation to the representation-independent mathematical relation.

Remaining formal obligations:

* Connect the actual Clean operations, including the scalar comparator, all
  table constants, selectors and loop invariants, to that mathematical relation.
* Instantiate the offset-existence argument for the complete circuit, including
  a proved safe finite candidate family. The generic counting theorem alone
  does not establish this circuit's completeness.
* Supply the challenge's complete soundness, completeness, cost and R1CS-shape
  proof package. Executable counting and vector tests do not replace these.
* The sparse matrix exporter is tested tooling, not a verified compiler.

There are no `sorry` placeholders or custom axioms in the included new proofs.
The unproved obligations above are absent theorems, not hidden assumptions in a
claimed complete circuit proof.

## Executable evidence

`validation.txt` records the full run:

* 4,631 allocations, 4,636 rows, score 9,267; zero non-R1CS assertions.
* 252 native test vectors agree with the original relation: 166 accepted,
  86 rejected. The 24 malformed-byte-length cases have no native-field witness
  and are skipped.
* Two accepted fixtures require retrying H=G with H=2G. This exercises actual
  exceptional-addition avoidance.
* The `E=p+1` digest-lift regression passes.
* The explicit `Q=3G, R=2G, E=1` regression rejects H=G at an exceptional
  table addition and accepts H=2G.

For rejected vectors, the driver checks the generated witness with H=G. This is
negative-test coverage, not an exhaustive proof that no alternate witness exists.
The independent Python matrix checker evaluates the exported sparse R1CS and
checks statement-input and auxiliary-wire corruptions. Some gated comparator
quotients are legitimately unconstrained for a particular witness; those are
reported separately rather than treated as soundness failures.

## Reproduce

From the repository root:

```sh
lake build projected Baseline.Projected.Audit
lake exe projected
lake exe projected --export Baseline/Projected/generated
python3 Baseline/Projected/check_matrices.py Baseline/Projected/generated
```

`--count-only` skips vector tests. `--quick` checks twelve native vectors.
Generated matrix JSON uses column 0 for the constant one and column i+1 for
Clean wire i. The first five variable columns are pk_x, pk_y, digest, r, s.
Each row is `[A,B,C]`, each linear combination is a list of
`[column, coefficient-as-decimal-string]`, and the constraint is `A(z)*B(z)=C(z)`.
Duplicate terms in a linear combination are summed modulo p.
