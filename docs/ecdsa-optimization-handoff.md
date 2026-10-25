# ECDSA challenge: optimization results and specification direction

Status as of 25 October 2026.

We have an implemented experimental circuit scoring **9,267**, compared with the
partner reference's **17,668**: a **47.55% reduction**. Its exported matrices and
vector tests have been checked. The alternative mathematical representation and
elliptic-curve arithmetic components have Lean proofs. **The complete circuit's
soundness and completeness proofs remain unfinished.**

The recommended next direction is a challenge for **fully complete standard P-256
ECDSA verification**, with freedom to choose internal witnesses. That specification
change is a proposal; the current trusted challenge has not been changed.

## 1. What the current challenge and experiment mean

The current challenge pins Longfellow's `ValidEcdsaWitness` at commit
`4fe092be7e8e9634cd3b27daf55695a3a416043e`. Its contract checks the supplied original
intermediate coordinates point by point.

The new experiment instead takes five fields `(pk_x, pk_y, digest, r, s)` and
allows its internal witnesses to vary. The signature remains bound. This is an
existential projection of the source witness relation, not permission to choose
an unrelated signature or ignore signature checking. Input fields here need not
all be public in an enclosing anonymous-credential proof.

A Lean theorem proves that this signature-bound projection is equivalent to a
representation-independent mathematical relation on the exact P-256 parameters:

```
[E]G + [r]Q + [n-s]R = infinity
R.x = r
```

It retains Longfellow's scalar bounds, curve/nonzero checks, exceptional-point
restrictions and digest-lift semantics. The theorem is
[`p256_boundLF_iff_representation_independent`](../Baseline/Projected/P256Bridge.lean).
It does not establish equivalence between every execution of the new Clean
implementation and that relation. Nor does it make the experiment a submission
under the old pointwise-witness contract.

## 2. Measured circuit costs

Score means **additional witness allocations + R1CS constraint rows** over the
P-256 base field. It is not a measurement of mobile proving time or proof
verification time.

| Implementation | Additional variables | Rows | Score |
|---|---:|---:|---:|
| Literal Longfellow lowering | 11,375 | 12,415 | 23,790 |
| Optimized lowering preserving the original witness format | 9,296 | 10,334 | 19,630 |
| Partner field-input reference | 8,817 | 8,851 | 17,668 |
| New projected-signature experiment | 4,631 | 4,636 | **9,267** |

These are different interfaces, not four certified submissions to one unchanged
contract. The experiment counts every auxiliary bit, table coordinate, inverse,
offset and intermediate. Five input fields are excluded; the partner excludes
six. Including those inputs gives 9,272 versus 17,674, so that difference does
not explain the improvement. The partner measurement uses commit
`ffbbd372afd559d7e2c4a7f7ab26f4d87cee79cb` and its Vega backend `ShapeCS` counter.

The gain comes from:

- A joint two-scalar ladder plus a separate fixed-base generator multiplication,
  instead of the partner's four scalar multiplications.
- Constant two-bit generator tables and four-way variable-point selection.
- Eisentraeger–Lauter–Montgomery (ELM) double-and-add equations that omit an
  intermediate y coordinate.
- A prover-chosen offset that permits affine formulas while checking exceptional
  denominators. Proved redundancy of the second ELM denominator guard saves
  512 score points; the doubling guard saves another two.
- Constraining the final point directly, avoiding redundant output wires.

The [ELM circuit discussion](https://github.com/zcash/zcash/issues/3924) explains
the underlying arithmetic technique. Our checked component proofs are in
[Algebra](../Baseline/Projected/Algebra.lean),
[AffineBridge](../Baseline/Projected/AffineBridge.lean) and
[ProjectiveBridge](../Baseline/Projected/ProjectiveBridge.lean).

## 3. Verification status

Completed:

- Repository build and Lean axiom audit pass. The audited theorems depend only
  on `propext`, `Classical.choice` and `Quot.sound`; no `sorry` or custom axiom
  fills the missing whole-circuit proof.
- 252 native vector comparisons agree with the source diagnostic: 166 accepted
  and 86 rejected. Another 24 malformed-byte-length cases are outside that native
  interface and skipped.
- Digest `p+1` represented by field element `1` is tested explicitly, preserving
  the source relation's possible noncanonical digest lift.
- Exceptional-offset tests reject an unsuitable H and succeed with another.
- All 4,636 assertions have single-row R1CS form. An independent Python checker
  verifies the exported matrices against a sample witness and detects all five
  single-input and 4,631 single-auxiliary-wire corruptions in that sample.

The negative vector tests use generated witnesses with H=G; they do not exhaust
all possible malicious witnesses. Mutation tests likewise do not prove soundness.

Still required:

1. Connect the actual Clean operations, scalar comparator, selectors, constant
   tables and loops to the mathematical relation.
2. Instantiate the abstract offset-existence proof with a certified P-256
   candidate family, establishing completeness for all valid inputs.
3. Complete the circuit soundness, completeness, cost and R1CS-shape proof package.
4. Treat export correctness separately: the sparse matrix exporter is tested
   tooling, not a formally verified compiler.

See the [experiment README](../Baseline/Projected/README.md),
[vector log](../Baseline/Projected/validation.txt),
[proof audit](../Baseline/Projected/proof-validation.txt) and
[matrix measurements](../Baseline/Projected/matrices-validation.json).

## 4. Why Longfellow rejects some standard-valid signatures

Standard ECDSA checks `r = R.x mod n`. The pinned Longfellow circuit checks
`r = R.x` directly, excluding the rare case where reduction modulo n changes
that coordinate. Its affine precomputation tables also exclude certain sums
that are infinity, including a public key `Q = -G`. It additionally requires a
nonzero public-key x coordinate.

These restrictions simplify the circuit. The authors describe their approach as
almost perfectly complete and accept the omitted cases for their applications
([paper, section 4.1](https://eprint.iacr.org/2024/2010.pdf)). The cases are
extraordinarily unlikely under ordinary random generation, but deliberately
chosen inputs can hit them. They are genuine compatibility restrictions, not
requirements of anonymous credentials.

For an exact Longfellow benchmark, retain them. For a fully complete standard
ECDSA challenge, implement the omitted behavior and prove the broader relation.
Simply deleting checks is not sufficient.

## 5. Estimated cost of full completeness

The new representation may support the missing cases at approximately the same
cost. The following is a **component-based estimate, not a measured or proved
full-standard-ECDSA circuit**:

| Proposed change | Score delta |
|---|---:|
| Build shifted tables directly, removing original table checks | -74 |
| Permit valid public keys with x=0 | -2 |
| Add an overflow bit and conditional bound for `R.x = r + n` | approximately +70 |
| Estimated total for those changes | **9,261** |

The table change builds shifted sums directly instead of requiring unshifted
`Q+R` to have affine coordinates. It retains the group-operation constraints.
The overflow branch must enforce `r+n < p`; a field equality alone would allow
wraparound. The estimate uses one Boolean overflow bit and 34 gated zero-run
comparisons for `r < p-n` when that bit is set.

Full standard verification should also bind the exact 32-byte digest. A single
P-256 field element cannot distinguish every 256-bit digest. Two 128-bit input
limbs, with the existing digest bits recomposed separately, appear to add one
constraint, giving an estimated **9,262** under the same input-exclusion scoring
convention. These numbers are a design estimate: the implementation, all-input
proofs and final measurement still need to be done. Budget roughly **9.3k**,
not a guaranteed exact result.

## 6. Recommended specification

Use an implementation-independent standard P-256 ECDSA predicate, reusing the
existing Longfellow/Mathlib curve machinery and applicable proofs. Bind the exact
digest and signature; validate the key and scalar ranges; compute the standard
verification point; reject infinity; and require `r = R.x mod n`. Do not impose
conditions merely because one implementation uses a particular table or
intermediate-coordinate representation.

The vendored function named
[`StandardEcdsaVerify`](../vendor/longfellow/ECDSA/EcdsaSpec.lean) still ends in
direct x-coordinate equality. Its name does not make it a ready-to-use full
standard specification; that final condition needs correction for this direction.

The alternative repositories do not currently offer a demonstrated reason to
replace our mathematical foundation:

- [ETHCryptoLean](https://github.com/revofusion/ETHCryptoLean#primitives) targets
  secp256k1 ECDSA recovery, not this P-256 verification problem.
- [Sparkle](https://github.com/Verilean/sparkle#crypto--wallets) includes P-256
  ECDSA, but its catalog does not claim an ECDSA correctness proof. It may be useful
  as an independent executable reference. This assessment is not an exhaustive
  audit of every Sparkle source file.

The recommendation is therefore to broaden the mathematical target, retain the
useful existing proofs, and adapt the experimental circuit. The current challenge
and the measured 9,267 circuit still preserve Longfellow's restrictions.

## 7. Partner audit and handoff

The improvement does not depend on declaring the partner's implementation broken.
Old notes about unconstrained constants, infinity flags and ignored high scalar
limbs were already addressed at the measured commit.

A separate reproduction found noncanonical scalar decompositions: scalar field
value zero can use the bits of p and produce p*G. A composed example accepts a
supplied inverse of zero, but corresponds to another valid signature; it is not
a demonstrated signature forgery. This matters when claiming equivalence of the
supplied scalar representations. See the
[reproducible audit](../Baseline/PartnerAudit/README.md). Its preparation script
fetches hash-pinned partner source; that source is not redistributed in our package.

Reproduce the current experiment from the repository root:

```sh
lake build projected Baseline.Projected.Audit
lake exe projected
lake exe projected --export Baseline/Projected/generated
python3 Baseline/Projected/check_matrices.py Baseline/Projected/generated
```

Generated matrices are ignored by Git and reproducible with those commands.
The additional upstream proof modules are pinned and their compatibility edits
are recorded in [the provenance manifest](../Baseline/Projected/upstream-proof-provenance.json).

For committing this work, the relevant paths are `Baseline/`, `lakefile.lean`,
this document, and the four additional upstream modules:

```sh
git add Baseline/ lakefile.lean docs/ecdsa-optimization-handoff.md \
  vendor/longfellow/ECDSA/ECBridge.lean \
  vendor/longfellow/ECDSA/Ecdsa.lean \
  vendor/longfellow/ECDSA/NoRoot.lean \
  vendor/longfellow/ECDSA/P256NoRoot.lean
git diff --cached --stat
```

No specification migration or full-completeness implementation is included in
this handoff. The next substantive work is to settle and review the full-standard
predicate, implement the proposed changes, and complete the remaining proofs.
