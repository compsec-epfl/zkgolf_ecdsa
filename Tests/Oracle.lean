import Challenge.Specs.ECDSAP256

namespace Tests.Oracle
open Challenge.Specs.ECDSAP256

-- Serialization adapter for external test vectors only.
def fromBytes (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun a b => 256 * a + b.toNat) 0

/-- Test oracle for Longfellow's generated witness path. It uses the upstream
addition, doubling, selector table and circuit loop, including affine-table
exceptional cases. It is not an existential decision procedure or the trusted
relation. The authoritative Spec uses ValidEcdsaWitness directly. -/
def verify (publicKey digest signature : ByteArray) : Bool := Id.run do
  if publicKey.size != 64 || digest.size != 32 || signature.size != 64 then return false
  let x := fromBytes (publicKey.extract 0 32)
  let y := fromBytes (publicKey.extract 32 64)
  let r := fromBytes (signature.extract 0 32)
  let s := fromBytes (signature.extract 32 64)
  let e := fromBytes digest
  if !(x < p && y < p && 0 < r && r < n && 0 < s && s < n) then return false
  let pk : AffinePoint K := { X := x, Y := y }
  let g : AffinePoint K := { X := params.gx, Y := params.gy }
  let onCurve (q : AffinePoint K) := q.Y * q.Y == q.X * q.X * q.X + params.a * q.X + params.b
  if !onCurve pk || pk.X == 0 then return false
  let inv := ((s : ZMod n)⁻¹).val
  let pr := addE (bsmul (padBits (natToBits ((e * inv) % n)) 256) g.toProjective params)
    (bsmul (padBits (natToBits ((r * inv) % n)) 256) pk.toProjective params) params
  let R : AffinePoint K := { X := r, Y := pr.Y * pr.Z⁻¹ }
  if !onCurve R then return false
  let pairs := [(g, pk), (g, R), (pk, R)]
  let mut pre : List K := []
  for (a, b) in pairs do
    let q := addE a.toProjective b.toProjective params
    let ax := q.X * q.Z⁻¹
    let ay := q.Y * q.Z⁻¹
    if !(q.X == q.Z * ax && q.Y == q.Z * ay) then return false
    pre := pre ++ [ax, ay]
  let q := addE g.toProjective
    ({ X := pre.getD 4 0, Y := pre.getD 5 0 } : AffinePoint K).toProjective params
  let ax := q.X * q.Z⁻¹
  let ay := q.Y * q.Z⁻¹
  if !(q.X == q.Z * ax && q.Y == q.Z * ay) then return false
  pre := pre ++ [ax, ay]
  let bi := (List.range 256).map fun i =>
    (e / 2^(255-i)) % 2 + 2*((r / 2^(255-i)) % 2) + 4*(((n-s) / 2^(255-i)) % 2)
  let finalAcc := ecdsaPureLoopResult bi pk R.X R.Y pre params
  return finalAcc.X == 0 && finalAcc.Z == 0 &&
    (reconstructE bi : K) == (e : K) && (reconstructR bi : K) == R.X &&
    (reconstructS bi : K) != 0 && natR bi < n && natS bi < n

end Tests.Oracle
