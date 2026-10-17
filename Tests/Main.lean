import Tests.Oracle
import Lean
open Lean

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

def main : IO Unit := do
  let text ← IO.FS.readFile "vectors/cases.json"
  let tests ← IO.ofExcept do (← Json.parse text).getArr?
  let mut positives := 0
  for test in tests do
    let id ← IO.ofExcept do (← test.getObjVal? "id").getStr?
    let field (name : String) : IO ByteArray := IO.ofExcept do
      unhex (← (← test.getObjVal? name).getStr?)
    let pk ← field "pk"
    let digest ← field "digest"
    let signature ← field "signature"
    let expected ← IO.ofExcept do (← test.getObjVal? "expected").getBool?
    let actual := Tests.Oracle.verify pk digest signature
    unless actual == expected do throw (IO.userError s!"{id}: expected {expected}, got {actual}")
    if actual then positives := positives + 1
  IO.println s!"Longfellow circuit-path vector oracle: {tests.size} cases passed ({positives} valid)"
