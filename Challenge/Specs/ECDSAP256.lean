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

/-- Pointwise Longfellow circuit relation over its native field inputs.
No byte decoding, signature envelope, or existential weakening is added. -/
def Spec (pkX pkY digest : K) (w : EcdsaWitness K) : Prop :=
  ValidEcdsaWitness w ({ X := pkX, Y := pkY } : AffinePoint K) digest n params

end Challenge.Specs.ECDSAP256
