import Challenge.Specs.ECDSAP256
import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving

namespace Challenge.Instances.ECDSA_P256_Digest.Interface

/-- Native statement inputs plus the original circuit's witness inputs.
The latter are private wires in a proof-system integration. Keeping them explicit
makes the challenge pointwise equivalent to the upstream verifier. -/
structure Input (F : Type) where
  pkX : F
  pkY : F
  digest : F
  rx : F
  ry : F
  rxInv : F
  sInv : F
  pkInv : F
  pre : Vector F 8
  bi : Vector F 256
  intX : Vector F 255
  intY : Vector F 255
  intZ : Vector F 255
  deriving ProvableStruct

abbrev Output : TypeMap := unit
abbrev circuitPrime : ℕ := Challenge.Specs.ECDSAP256.p

def witness (input : Input (F circuitPrime)) : EcdsaWitness (F circuitPrime) := {
  rx := input.rx, ry := input.ry, rx_inv := input.rxInv,
  s_inv := input.sInv, pk_inv := input.pkInv, pre := input.pre.toList,
  bi := input.bi.toList, int_x := input.intX.toList,
  int_y := input.intY.toList, int_z := input.intZ.toList }

/-- No byte-range, key-validity or witness-validity caller assumptions. -/
def Assumptions (_input : Input (F circuitPrime)) (_data : ProverData (F circuitPrime)) : Prop := True

def Spec (input : Input (F circuitPrime)) (_output : Output (F circuitPrime))
    (_data : ProverData (F circuitPrime)) : Prop :=
  Challenge.Specs.ECDSAP256.Spec input.pkX input.pkY input.digest (witness input)

def ProverAssumptions (input : Input (F circuitPrime)) (data : ProverData (F circuitPrime))
    (_hint : ProverHint (F circuitPrime)) : Prop := Spec input () data

def ProverSpec (_input : Input (F circuitPrime)) (_output : Output (F circuitPrime))
    (_hint : ProverHint (F circuitPrime)) : Prop := True

end Challenge.Instances.ECDSA_P256_Digest.Interface
