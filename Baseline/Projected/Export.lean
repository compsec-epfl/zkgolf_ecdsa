import Baseline.Projected.Check

/-! Concrete sparse matrix export for independent measurement/testing.
This exporter is executable tooling, not a formally verified backend. -/
namespace Baseline.Projected.Offset.Export
open Lean Baseline
abbrev LC := List (Nat × Fp)

def linear (scale : Fp) : E → Except String LC
  | .var v => pure [(v.index + 1, scale)]
  | .const x => pure [(0, scale*x)]
  | .add a b => return (← linear scale a) ++ (← linear scale b)
  | .mul a b =>
    if deg a == 0 then linear (scale * constVal a) b
    else if deg b == 0 then linear (scale * constVal b) a
    else throw "nonlinear factor"

/-- R1CS convention: column 0 is 1; circuit wire i is column i+1. -/
def row (e : E) : Except String (LC × LC × LC) := do
  let terms := Baseline.flat 1 e
  let mut a : LC := []
  let mut b : LC := []
  let mut c : LC := []
  let mut found := false
  for (scale,t) in terms do
    match t with
    | .mul x y =>
      if found then throw "more than one product in assertion"
      a ← linear scale x
      b ← linear 1 y
      found := true
    | _ => c := c ++ (← linear (-scale) t)
  return (a,b,c)

def lcJson (x : LC) : Json := toJson (x.map fun (i,c) => (i,toString c.val))
def rowJson (x : LC × LC × LC) : Json :=
  Json.arr #[lcJson x.1,lcJson x.2.1,lcJson x.2.2]

def exportTo (directory : System.FilePath) : IO Unit := do
  let operations := Circuit.operations (Baseline.Projected.Offset.main Baseline.Projected.Offset.Check.inputVar) 5
  let k := Challenge.CostR1CS.operationCount operations
  let ops := operations.toFlat
  let rows ← IO.ofExcept <| ops.filterMapM fun op => do
    match op with
    | .assert e => return some (rowJson (← row e))
    | .witness _ _ => return none
    | _ => throw "unexpected lookup or interaction"
  IO.FS.createDirAll directory
  let j := Json.mkObj [
    ("format",toJson "sparse-r1cs-v1"),
    ("field_prime",toJson (toString Challenge.Instances.ECDSA_P256_Digest.Interface.circuitPrime)),
    ("fixed_inputs",toJson 5),
    ("additional_allocations",toJson k.allocations),
    ("columns",toJson (6+k.allocations)),
    ("rows",toJson k.constraints),
    ("score",toJson (k.allocations+k.constraints)),
    ("input_order",toJson ["pk_x","pk_y","digest","r","s"]),
    ("constraints",Json.arr rows.toArray)]
  IO.FS.writeFile (directory / "matrices.json") j.compress
  let text ← IO.FS.readFile "vectors/cases.json"
  let tests ← IO.ofExcept do (← Lean.Json.parse text).getArr?
  for test in tests do
    let field (name : String) : IO ByteArray := IO.ofExcept do
      Baseline.Projected.Offset.Check.unhex (← (← test.getObjVal? name).getStr?)
    let some w := Baseline.Check.buildWitness (← field "pk") (← field "digest") (← field "signature")
      | continue
    if !Baseline.Check.specCheck w then continue
    let some h := Baseline.Projected.Offset.Check.searchH ops w 1040
      | throw (IO.userError "offset not found for accepted case")
    let hint := Baseline.Projected.Offset.Check.hintProvider
      (Baseline.Projected.Offset.Check.hintValues w (Baseline.Projected.Offset.affine (Baseline.Projected.Offset.mulG h)))
    let wires := FlatOperation.witgen hint ops (toElements (Baseline.Projected.Offset.Check.project w)).toArray
    let values := #["1"] ++ wires.map (fun x => toString x.val)
    IO.FS.writeFile (directory / "sample-witness.json") (toJson values).compress
    IO.println s!"exported {rows.length} rows, {k.allocations} additional variables, score {k.allocations+k.constraints}"
    return
  throw (IO.userError "no accepted sample")
end Baseline.Projected.Offset.Export
