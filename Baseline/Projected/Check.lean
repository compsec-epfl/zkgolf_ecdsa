import Baseline.Projected.Offset
import Baseline.Check
import Lean

/-! Executable diagnostics for the projected-interface offset experiment.
These are generated-witness tests, not end-to-end equivalence proofs. -/
namespace Baseline.Projected.Offset.Check
open Lean Baseline Challenge.CostR1CS

abbrev OldInput := Challenge.Instances.ECDSA_P256_Digest.Interface.Input Fp

def inputVar : Var Baseline.Projected.Offset.Input Fp := varFromOffset Baseline.Projected.Offset.Input 0

def project (w : OldInput) : Baseline.Projected.Offset.Input Fp := {
  pkX := w.pkX, pkY := w.pkY, digest := w.digest, r := w.rx,
  s := (Challenge.Specs.ECDSAP256.n - natS (w.bi.toList.map (·.val)) : Nat) }

def hintValues (w : OldInput) (h : Fp × Fp) : Array Fp := Id.run do
  let mut a := #[w.ry,h.1,h.2] ++ w.pre.toArray
  for i in [0:256] do
    let v := (w.bi.toArray.getD (255-i) 0).val
    a := a ++ #[((v%2 : Nat) : Fp),((v/2%2 : Nat) : Fp),((v/4%2 : Nat) : Fp)]
  return a

def hintProvider (a : Array Fp) : ProverHint Fp :=
  fun _ n => a.map fun v => Vector.ofFn fun (_ : Fin n) => v

def firstFailure (ops : List (FlatOperation Fp)) (w : OldInput) (h : Fp × Fp) : Option Nat := Id.run do
  let init := (toElements (project w)).toArray
  let wires := FlatOperation.witgen (hintProvider (hintValues w h)) ops init
  let env : Environment Fp := Environment.fromArray wires (fun _ _ => #[])
  let mut row := 0
  for op in ops do
    match op with
    | .assert e =>
      if e.eval env != 0 then return some row
      row := row + 1
    | _ => pure ()
  return none

/-- Search finite H=kG representatives. For rejected source cases one representative
is tested; that is a negative diagnostic, not exhaustive unsatisfiability. -/
def searchH (ops : List (FlatOperation Fp)) (w : OldInput) (maxH : Nat) : Option Nat := Id.run do
  let mut h := Baseline.Projected.Offset.gPoint
  for i in [1:maxH+1] do
    if (firstFailure ops w (Baseline.Projected.Offset.affine h)).isNone then return some i
    h := _root_.addE h Baseline.Projected.Offset.gPoint Challenge.Specs.ECDSAP256.params
  return none

def unhex (s : String) : Except String ByteArray := do
  let chars := s.toList.toArray
  if chars.size % 2 != 0 then throw "odd hex length"
  let data ← (List.range (chars.size/2)).toArray.mapM fun i => do
    let digit (c : Char) : Except String Nat :=
      if c ≥ '0' && c ≤ '9' then pure (c.toNat-'0'.toNat)
      else if c ≥ 'a' && c ≤ 'f' then pure (c.toNat-'a'.toNat+10)
      else if c ≥ 'A' && c ≤ 'F' then pure (c.toNat-'A'.toNat+10)
      else throw "bad hex"
    return ((← digit chars[2*i]!) * 16 + (← digit chars[2*i+1]!)).toUInt8
  return ⟨data⟩

def bytes32 (v : Nat) : ByteArray :=
  ⟨(List.range 32).toArray.map fun i => ((v / 256^(31-i)) % 256).toUInt8⟩

/-- A valid digest represented by p+1 in the original selector bits, whose
field input is1. Preserve Longfellow's permitted noncanonical digest lift. -/
def liftedDigestWitness : Option OldInput := do
  let e := Challenge.Specs.ECDSAP256.p + 1
  let (rx, _) := Baseline.Projected.Offset.affine (Baseline.Projected.Offset.mulG 2)
  let n := Challenge.Specs.ECDSAP256.n
  let sigS := ((e+rx.val) * ((n+1)/2)) % n
  Baseline.Check.buildWitness (bytes32 gx.val ++ bytes32 gy.val)
    (bytes32 e) (bytes32 rx.val ++ bytes32 sigS)

def log (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

def retryWitness : Option OldInput := do
  let (qx,qy) := Baseline.Projected.Offset.affine (Baseline.Projected.Offset.mulG 3)
  let (rx,_) := Baseline.Projected.Offset.affine (Baseline.Projected.Offset.mulG 2)
  let n := Challenge.Specs.ECDSAP256.n
  let s := ((1+3*rx.val) * ((n+1)/2)) % n
  Baseline.Check.buildWitness (bytes32 qx.val ++ bytes32 qy.val)
    (bytes32 1) (bytes32 rx.val ++ bytes32 s)

end Baseline.Projected.Offset.Check

open Baseline.Projected.Offset.Check Baseline Challenge.CostR1CS

def Baseline.Projected.Offset.Check.run (args : List String) : IO UInt32 := do
  log "Building offset circuit operations and fixed tables..."
  let operations := Circuit.operations (Baseline.Projected.Offset.main Baseline.Projected.Offset.Check.inputVar) 5
  let k := operationCount operations
  let ops := operations.toFlat
  let bad := Baseline.Check.r1csViolations ops
  log s!"Projected-signature offset experiment (5 fixed inputs)"
  log s!"allocations={k.allocations} rows={k.constraints} score={k.allocations+k.constraints} R1CS violations={bad}"
  if args.contains "--count-only" then return if bad == 0 then 0 else 1
  let text ← IO.FS.readFile "vectors/cases.json"
  let tests ← IO.ofExcept do (← Lean.Json.parse text).getArr?
  let mut agree := 0
  let mut disagree := 0
  let mut accepted := 0
  let mut skipped := 0
  let mut maximumH := 0
  let mut sumH := 0
  let mut checked := 0
  for test in tests do
    if args.contains "--quick" && checked ≥ 12 then break
    let id ← IO.ofExcept do (← test.getObjVal? "id").getStr?
    let field (name : String) : IO ByteArray := IO.ofExcept do
      unhex (← (← test.getObjVal? name).getStr?)
    let some w := Baseline.Check.buildWitness (← field "pk") (← field "digest") (← field "signature")
      | skipped := skipped + 1; continue
    let spec := Baseline.Check.specCheck w
    let found := searchH ops w (if spec then 1040 else 1)
    let circ := found.isSome
    checked := checked + 1
    if spec == circ then agree := agree + 1
    else
      disagree := disagree + 1
      let fail := firstFailure ops w (Baseline.Projected.Offset.affine Baseline.Projected.Offset.gPoint)
      log s!"DISAGREE {id}: original={spec} offset={circ} H=1 first failure={fail}"
    if spec then
      accepted := accepted + 1
      if let some h := found then
        maximumH := max maximumH h
        sumH := sumH + h
        if h > 1 then log s!"H search {id}: H={h}G"
    if checked % 16 == 0 then log s!"progress: {checked} native cases, {disagree} disagreements"
  log s!"vectors: {agree} agree, {disagree} disagree ({accepted} source accepted, {skipped} byte-format cases skipped)"
  log s!"offset search: max H={maximumH}, sum H={sumH}; rejected cases tested only H=G"
  let some lifted := liftedDigestWitness | throw (IO.userError "failed to construct lifted-digest case")
  let liftedSpec := Baseline.Check.specCheck lifted
  let liftedH := searchH ops lifted 1040
  log s!"digest p+1 lift: original={liftedSpec} offset H={liftedH} field digest={lifted.digest.val}"
  let some retry := retryWitness | throw (IO.userError "failed to construct offset-retry case")
  let retrySpec := Baseline.Check.specCheck retry
  let retryFail := firstFailure ops retry (Baseline.Projected.Offset.affine Baseline.Projected.Offset.gPoint)
  let retryH := searchH ops retry 1040
  log s!"Q=3G,R=2G,e=1 retry: original={retrySpec}, H=G failure={retryFail}, first satisfying H={retryH}"
  unless retrySpec && retryFail.isSome && (retryH.getD 0 > 1) do
    throw (IO.userError "offset retry failed")
  return if bad+disagree == 0 && liftedSpec && liftedH.isSome then 0 else 1
