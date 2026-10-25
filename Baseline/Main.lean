import Baseline.Check

open Lean Baseline Baseline.Check Challenge.Instances.ECDSA_P256_Digest.Interface
open Challenge.CostR1CS

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

def report (name : String) (c : Var Input Fp → C Unit) : IO Unit := do
  let k := circuitCount (c inputVar) numInputs
  IO.println s!"{name}"
  IO.println s!"  additional witness allocations: {k.allocations}"
  IO.println s!"  R1CS constraint rows:           {k.constraints}"
  IO.println s!"  challenge score:                {k.allocations + k.constraints}"
  IO.println s!"  assertions that are not one R1CS row: {r1csViolations (opsOf c)}"

/-- Exercise the actual range-check circuit at the order/field boundaries and
at every bit transition. Inputs are bits, as guaranteed by the selector checks. -/
def checkRangeBoundaries : IO Bool := do
  let n := Challenge.Specs.ECDSAP256.n
  let p := Challenge.Specs.ECDSAP256.p
  let limit := 2^256
  let rangeOps := (Circuit.operations
    (Optimized.assertLtOrder (fun k => .var ⟨k⟩)) 256).toFlat
  let mut cases : Array Nat := #[0, 1, n-1, n, n+1, p-1, p, limit-1]
  for k in [0:256] do
    let power := 2^k
    let highPart : Nat := (n / power) * power
    cases := cases ++ #[power-1, power, highPart-1, highPart, highPart+1,
      (highPart + power - 1) % limit, (n + power) % limit, n-power]
  let mut seed := 1
  for _ in [0:512] do
    seed := (seed * 6364136223846793005 + 1442695040888963407) % limit
    cases := cases.push seed
  let mut failures := 0
  for value in cases do
    let bits : Array Fp := (List.range 256).toArray.map
      (fun k => if value.testBit k then 1 else 0)
    let wires := FlatOperation.witgen (default : ProverHint Fp) rangeOps bits
    let env : Environment Fp := Environment.fromArray wires (fun _ _ => #[])
    let accepted := rangeOps.all fun op => match op with
      | .assert e => e.eval env == 0
      | _ => true
    if accepted != decide (value < n) then
      failures := failures + 1
      IO.println s!"RANGE DISAGREEMENT: {value}, accepted={accepted}"
  IO.println s!"range boundary/random tests: {cases.size - failures}/{cases.size} agree"
  return failures == 0 && r1csViolations rangeOps == 0

def main (args : List String) : IO UInt32 := do
  report "Longfellow verify_signature3 as R1CS (literal lowering)" Baseline.main
  report "Optimized lowering of the same relation" Optimized.main
  if args.contains "--count-only" then return 0
  let rangesOK ← checkRangeBoundaries
  let opt := args.contains "--optimized"
  let ops := opsOf (if opt then Optimized.main else Baseline.main)
  IO.println s!"differential test of the {if opt then "optimized" else "baseline"} circuit"
  let text ← IO.FS.readFile "vectors/cases.json"
  let tests ← IO.ofExcept do (← Json.parse text).getArr?
  let mut agree := 0
  let mut disagree := 0
  let mut accepted := 0
  let mut skipped := 0
  let mut validWitnesses : Array (Input Fp) := #[]
  for test in tests do
    let id ← IO.ofExcept do (← test.getObjVal? "id").getStr?
    let field (name : String) : IO ByteArray := IO.ofExcept do
      unhex (← (← test.getObjVal? name).getStr?)
    let some w := buildWitness (← field "pk") (← field "digest") (← field "signature")
      | skipped := skipped + 1; continue
    let spec := specCheck w
    let circ := circuitCheck ops w
    if spec == circ then agree := agree + 1
    else
      disagree := disagree + 1
      IO.println s!"DISAGREE on vector {id}: spec={spec} circuit={circ}"
    if spec then
      accepted := accepted + 1
      validWitnesses := validWitnesses.push w
  IO.println s!"vectors: {agree} agree, {disagree} disagree ({accepted} accepted by spec, {skipped} byte-format cases without a native witness)"
  -- single-field mutations of accepted witnesses
  let positions : List Nat :=
    (List.range 16) ++ [16, 17, 100, 271, 272, 300, 526, 527, 700, 781, 782, 900, 1036]
  let deltas : List Fp := [1, -1]
  let mut mAgree := 0
  let mut mDisagree := 0
  let mut mAccepted := 0
  for w in validWitnesses.toList.take (if args.contains "--quick" then 1 else 4) do
    for k in positions do
      for d in deltas do
        let w' := mutate w k d
        let spec := specCheck w'
        let circ := circuitCheck ops w'
        if spec == circ then mAgree := mAgree + 1
        else
          mDisagree := mDisagree + 1
          IO.println s!"DISAGREE on mutation pos={k} delta={d.val}: spec={spec} circuit={circ}"
        if spec then mAccepted := mAccepted + 1
  IO.println s!"mutations: {mAgree} agree, {mDisagree} disagree ({mAccepted} accepted by spec)"
  return (if rangesOK && disagree + mDisagree == 0 then 0 else 1)
