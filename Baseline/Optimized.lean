import Baseline.Circuit

/-!
# Optimized lowering of the same relation (no proofs yet)

Targets the same accepted set as `Baseline.main` (tested differentially in
`Baseline.Check`; not yet proved end to end). Cheaper structure:

* selector: three boolean bits `bi = b0 + 2 b1 + 4 b2` (2 allocations, 3 rows) instead of the
  degree-8 polynomial mux and range polynomial; e/r/s bits are then the bits themselves;
* point mux: a 3-level binary tree, the constant (∞, G) pair costs nothing;
* `r, s < n`: compare to `n-1`, tracking only its one-bit runs; zero runs
  use one quotient witness and one gated-sum row each;
* first addition: substitute the exact infinity coordinates before lowering.

Doubling and addition are Longfellow's formulas exactly (the relation pins their outputs).
-/

namespace Optimized
open Baseline Challenge.Instances.ECDSA_P256_Digest.Interface

def bitOf (x : E) (j : Nat) : C E :=
  Circuit.witnessField (.ite (.bit (.expr x) j) (.const 1) (.const 0))

def assertBool (b : E) : C Unit := Circuit.assertZero (.mul b b - b)

/-- `x0` if `b = 0`, `x1` if `b = 1`; free when `x1 - x0` is constant. -/
def sel (b x0 x1 : E) : C E := mat (x0 + .mul b (x1 - x0))

def mux8 (b0 b1 b2 : E) (v : List E) : C E := do
  let g := fun i => v.getD i (cst 0)
  let l0 ← sel b0 (g 0) (g 1)
  let l1 ← sel b0 (g 2) (g 3)
  let l2 ← sel b0 (g 4) (g 5)
  let l3 ← sel b0 (g 6) (g 7)
  let m0 ← sel b1 l0 l1
  let m1 ← sel b1 l2 l3
  sel b2 m0 m1

/-- Runs of equal bits of the inclusive bound `n-1`, most significant first. -/
def boundRuns : List (Nat × Nat × Bool) := Id.run do
  let nb := fun k => (Challenge.Specs.ECDSAP256.n - 1).testBit k
  let mut out : Array (Nat × Nat × Bool) := #[]
  let mut hi := 255
  for j in [0:256] do
    let k := 255 - j
    if k == 0 || nb (k - 1) != nb k then
      out := out.push (hi, k, nb k)
      hi := k - 1
  return out.toList

/-- Assert `a < n` as `a ≤ n-1`, given boolean affine bits.

`missing` counts missing ONE bits of the bound in the preceding prefix.
For each ZERO run with bit-sum `sum`, impose `missing * quotient = sum`.
If `missing = 0` this forces the whole zero run to zero; otherwise the input
already has a smaller preceding bit and the quotient exists for any sum.
Both sums count ≤256 boolean bits, so zero cannot arise by field wraparound.
One allocation and one R1CS row per zero run; no equality flags are needed.
-/
def assertLtOrder (a : Nat → E) : C Unit := do
  let mut missing : E := cst 0
  for (hi, lo, bit) in boundRuns do
    let len := hi - lo + 1
    if bit then
      for j in [0:len] do
        missing := missing + (cst 1 - a (hi - j))
    else
      let sum := (List.range len).foldl
        (fun s j => s + a (hi - j)) (cst 0)
      let quotient ← Circuit.witnessField (.mul (.expr sum) (.inv (.expr missing)))
      Circuit.assertZero (pm missing quotient - sum)

def main (inp : Var Input Fp) : C Unit := do
  let one := cst 1
  let zero := cst 0
  let pre := inp.pre.toList
  let pk := fun i => pre.getD i zero
  -- table checks (as in the baseline)
  let (a1x, a1y, a1z) ← addE (cst gx) (cst gy) one inp.pkX inp.pkY one
  let (a2x, a2y, a2z) ← addE inp.rx inp.ry one (cst gx) (cst gy) one
  let (a3x, a3y, a3z) ← addE inp.rx inp.ry one inp.pkX inp.pkY one
  let (a4x, a4y, a4z) ← addE (cst gx) (cst gy) one (pk 4) (pk 5) one
  pointEquality a1x a1y a1z (pk 0) (pk 1)
  pointEquality a2x a2y a2z (pk 2) (pk 3)
  pointEquality a3x a3y a3z (pk 4) (pk 5)
  pointEquality a4x a4y a4z (pk 6) (pk 7)
  let tabX := [zero, cst gx, inp.pkX, pk 0, inp.rx, pk 2, pk 4, pk 6]
  let tabY := [one, cst gy, inp.pkY, pk 1, inp.ry, pk 3, pk 5, pk 7]
  let bis := inp.bi.toList
  let ix := inp.intX.toList
  let iy := inp.intY.toList
  let iz := inp.intZ.toList
  let mut ax := zero
  let mut ay := one
  let mut az := zero
  let mut est := zero
  let mut rst := zero
  let mut sst := zero
  let mut rbits : Array E := #[]
  let mut sbits : Array E := #[]
  for i in [0:256] do
    let v := bis.getD i zero
    let b0 ← bitOf v 0
    let b1 ← bitOf v 1
    let b2 := sc (4 : Fp)⁻¹ (v - b0 - sc 2 b1)
    assertBool b0
    assertBool b1
    assertBool b2
    est := b0 + sc 2 est
    rst := b1 + sc 2 rst
    sst := b2 + sc 2 sst
    rbits := rbits.push b1
    sbits := sbits.push b2
    let tx ← mux8 b0 b1 b2 tabX
    let ty ← mux8 b0 b1 b2 tabY
    let w ← mm (one - b0) (one - b1)
    let nz ← mm w (one - b2)
    let tz := one - nz
    if i > 0 then
      let (dx, dy, dz) ← doubleE ax ay az
      ax ← mat dx
      ay ← mat dy
      az ← mat dz
    -- The first accumulator is exactly (0,1,0). Substituting it in addE
    -- gives (tx*ty, ty^2, ty*tz), not the normalized selected point.
    -- Keep those products in the existing witness-equality rows.
    let (nx, ny, nz') ← if i == 0 then
        pure (pm tx ty, pm ty ty, pm ty tz)
      else addE ax ay az tx ty tz
    if i < 255 then
      assertZeroLazy (nx - ix.getD i zero)
      assertZeroLazy (ny - iy.getD i zero)
      assertZeroLazy (nz' - iz.getD i zero)
      ax := ix.getD i zero
      ay := iy.getD i zero
      az := iz.getD i zero
    else
      assertZeroLazy nx
      assertZeroLazy nz'
  assertZeroLazy (est - inp.digest)
  assertZeroLazy (rst - inp.rx)
  isOnCurve inp.pkX inp.pkY
  isOnCurve inp.rx inp.ry
  assertZeroLazy (.mul inp.rx inp.rxInv - one)
  assertZeroLazy (.mul sst inp.sInv - one)
  assertZeroLazy (.mul inp.pkX inp.pkInv - one)
  assertLtOrder (fun k => rbits.getD (255 - k) zero)
  assertLtOrder (fun k => sbits.getD (255 - k) zero)

end Optimized
