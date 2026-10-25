import Baseline.Count
import Baseline.Optimized
import Clean.Circuit.WitnessGeneration
import Lean

/-!
Differential test of the baseline circuit against a Bool transcription of
`ValidEcdsaWitness` (`vendor/longfellow/ECDSA/EcdsaCircuit.lean`).  Both are evaluated on
the same full witness; they must give the same verdict.
-/

namespace Baseline.Check
open Lean Challenge.Specs.ECDSAP256 Challenge.Instances.ECDSA_P256_Digest.Interface

def fromBytes (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun a b => 256 * a + b.toNat) 0

def vec {α : Type} [Inhabited α] (n : Nat) (l : List α) : Vector α n :=
  Vector.ofFn fun (i : Fin n) => l.getD i default

/-- Honest-prover witness for an (external-format) test case, with no early rejection:
bad inputs still yield a full witness, which the relation must then reject. -/
def buildWitness (publicKey digest signature : ByteArray) : Option (Input Fp) := do
  guard (publicKey.size == 64 && digest.size == 32 && signature.size == 64)
  let x := fromBytes (publicKey.extract 0 32)
  let y := fromBytes (publicKey.extract 32 64)
  let r := fromBytes (signature.extract 0 32)
  let s := fromBytes (signature.extract 32 64)
  let e := fromBytes digest
  let pk : AffinePoint K := { X := x, Y := y }
  let g : AffinePoint K := { X := params.gx, Y := params.gy }
  let inv := ((s : ZMod n)⁻¹).val
  let pr := _root_.addE (bsmul (padBits (natToBits ((e * inv) % n)) 256) g.toProjective params)
    (bsmul (padBits (natToBits ((r * inv) % n)) 256) pk.toProjective params) params
  let R : AffinePoint K := { X := r, Y := pr.Y * pr.Z⁻¹ }
  let aff (q : ProjectivePoint K) : List K := [q.X * q.Z⁻¹, q.Y * q.Z⁻¹]
  let pre3 := aff (_root_.addE g.toProjective pk.toProjective params) ++
    aff (_root_.addE g.toProjective R.toProjective params) ++
    aff (_root_.addE pk.toProjective R.toProjective params)
  let q4 := _root_.addE g.toProjective
    ({ X := pre3.getD 4 0, Y := pre3.getD 5 0 } : AffinePoint K).toProjective params
  let pre := pre3 ++ aff q4
  let bi : List Nat := (List.range 256).map fun i =>
    (e / 2^(255-i)) % 2 + 2*((r / 2^(255-i)) % 2) + 4*(((n-s) / 2^(255-i)) % 2)
  let accs := (bi.foldl (fun (st : List (ProjectivePoint K) × ProjectivePoint K × Bool) v =>
      let (l, acc, first) := st
      let t := muxPoint v pk R.X R.Y pre params
      let d := if first then acc else _root_.doubleE acc params
      let nx := _root_.addE d t params
      (l ++ [nx], nx, false)) ([], infinityPoint, true)).1
  return {
    pkX := (x : K), pkY := (y : K), digest := (e : K),
    rx := (r : K), ry := R.Y, rxInv := (r : K)⁻¹,
    sInv := (((n - s : Nat) : K))⁻¹, pkInv := (x : K)⁻¹,
    pre := vec 8 pre, bi := vec 256 (bi.map fun v => (v : K)),
    intX := vec 255 (accs.map (·.X)), intY := vec 255 (accs.map (·.Y)),
    intZ := vec 255 (accs.map (·.Z)) }

/-- Bool transcription of `ValidEcdsaWitness` (computable parts of the vendored library). -/
def specCheck (w : Input Fp) : Bool := Id.run do
  let bn : List Nat := w.bi.toList.map (·.val)
  if !(w.bi.toList.all (fun v => v.val < 8)) then return false
  let pk : AffinePoint K := { X := w.pkX, Y := w.pkY }
  let pre := w.pre.toList
  let g : AffinePoint K := { X := params.gx, Y := params.gy }
  let eqPt (q : ProjectivePoint K) (ax ay : K) : Bool := q.X == q.Z * ax && q.Y == q.Z * ay
  let R : AffinePoint K := { X := w.rx, Y := w.ry }
  let p4 : AffinePoint K := { X := pre.getD 4 0, Y := pre.getD 5 0 }
  let preOk :=
    eqPt (_root_.addE g.toProjective pk.toProjective params) (pre.getD 0 0) (pre.getD 1 0) &&
    eqPt (_root_.addE R.toProjective g.toProjective params) (pre.getD 2 0) (pre.getD 3 0) &&
    eqPt (_root_.addE R.toProjective pk.toProjective params) (pre.getD 4 0) (pre.getD 5 0) &&
    eqPt (_root_.addE g.toProjective p4.toProjective params) (pre.getD 6 0) (pre.getD 7 0)
  if !preOk then return false
  let ix := w.intX.toList
  let iy := w.intY.toList
  let iz := w.intZ.toList
  let mut acc : ProjectivePoint K := infinityPoint
  for i in [0:255] do
    let t := muxPoint (bn.getD i 0) pk w.rx w.ry pre params
    let d := if i == 0 then acc else _root_.doubleE acc params
    let nx := _root_.addE d t params
    if !(nx.X == ix.getD i 0 && nx.Y == iy.getD i 0 && nx.Z == iz.getD i 0) then return false
    acc := { X := ix.getD i 0, Y := iy.getD i 0, Z := iz.getD i 0 }
  let t := muxPoint (bn.getD 255 0) pk w.rx w.ry pre params
  let fin := _root_.addE (_root_.doubleE acc params) t params
  let onCurve (q : AffinePoint K) : Bool :=
    q.Y * q.Y == q.X * q.X * q.X + params.a * q.X + params.b
  return fin.X == 0 && fin.Z == 0 &&
    (reconstructE bn : K) == w.digest && (reconstructR bn : K) == w.rx &&
    onCurve pk && onCurve R &&
    w.rx * w.rxInv == 1 && (reconstructS bn : K) * w.sInv == 1 && w.pkX * w.pkInv == 1 &&
    decide (natR bn < n) && decide (natS bn < n)

def opsOf (c : Var Input Fp → C Unit) : List (FlatOperation Fp) :=
  (Circuit.operations (c inputVar) numInputs).toFlat

/-- Run the circuit's witness generation from the inputs, then evaluate every assertion. -/
def circuitCheck (ops : List (FlatOperation Fp)) (w : Input Fp) : Bool := Id.run do
  let init : Array Fp := (toElements w).toArray
  let arr := FlatOperation.witgen (default : ProverHint Fp) ops init
  let env : Environment Fp := Environment.fromArray arr (fun _ _ => #[])
  for op in ops do
    match op with
    | .assert e => if e.eval env != 0 then return false
    | _ => pure ()
  return true

def mutate (w : Input Fp) (k : Nat) (delta : Fp) : Input Fp :=
  let arr := (toElements w).toArray
  let arr' := arr.set! k (arr.getD k 0 + delta)
  fromElements (Vector.ofFn fun (i : Fin (size Input)) => arr'.getD i 0)

/-- Number of assertions that are not a single R1CS row (must be 0 for the count to be valid),
plus any lookups/interactions. Uses the challenge's own `r1csProducts`. -/
def r1csViolations (ops : List (FlatOperation Fp)) : Nat :=
  ops.foldl (fun acc op => match op with
    | .assert e =>
        match Challenge.CostR1CS.r1csProducts e with
        | some k => if k ≤ 1 then acc else acc + 1
        | none => acc + 1
    | .lookup _ => acc + 1
    | .interact _ => acc + 1
    | _ => acc) 0

end Baseline.Check
