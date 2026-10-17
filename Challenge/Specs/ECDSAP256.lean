import ECDSA.EcdsaCircuit
import ECDSA.Pratt

namespace Challenge.Specs.ECDSAP256

abbrev p : Nat := 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
abbrev n : Nat := 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
instance : Fact (Nat.Prime p) :=
  ⟨ECDSA.prime_115792089210356248762697446949407573530086143415290314195533631308867097853951⟩
abbrev K := ZMod p

def params : CurveParameters K := {
  a := -3
  b := 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
  gx := 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
  gy := 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
  kBits := 256 }

/-- Unsigned big-endian integer. -/
def fromBytes (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun a b => 256 * a + b.toNat) 0

/-- Byte envelope around Longfellow's circuit satisfiability relation.
The signature is bound to the circuit's r and negative-s selector streams.
The digest is a base-field input, exactly as in verify_signature3. -/
def Spec (publicKey digest signature : ByteArray) : Prop :=
  publicKey.size = 64 ∧ digest.size = 32 ∧ signature.size = 64 ∧
  let x := fromBytes (publicKey.extract 0 32)
  let y := fromBytes (publicKey.extract 32 64)
  let r := fromBytes (signature.extract 0 32)
  let s := fromBytes (signature.extract 32 64)
  x < p ∧ y < p ∧ 0 < r ∧ r < n ∧ 0 < s ∧ s < n ∧
  ∃ w : EcdsaWitness K,
    ValidEcdsaWitness w ({ X := (x : K), Y := (y : K) } : AffinePoint K)
      (fromBytes digest : K) n params ∧
    natR (w.bi.map val3) = r ∧ natS (w.bi.map val3) = n - s

end Challenge.Specs.ECDSAP256
