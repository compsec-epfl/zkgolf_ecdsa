import Challenge.Specs.ECDSAP256
import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving

namespace Challenge.Instances.ECDSA_P256_Digest.Interface

structure Input (F : Type) where
  publicKey : Vector F 64
  digest : Vector F 32
  signature : Vector F 64
  deriving ProvableStruct

abbrev Output : TypeMap := unit

abbrev circuitPrime : ℕ := Challenge.Specs.ECDSAP256.p
-- Primality is proved by the imported Longfellow Pratt certificate.

def IsBytes {n : Nat} (v : Vector (F circuitPrime) n) : Prop :=
  ∀ i : Fin n, v[i].val < 256

def bytes {n : Nat} (v : Vector (F circuitPrime) n) : ByteArray :=
  ⟨v.toArray.map (fun x => x.val.toUInt8)⟩

/-- Caller checks octet ranges only. Public-key validity, signature ranges and the ECDSA relation
must follow from the circuit. -/
def Assumptions (input : Input (F circuitPrime)) (_data : ProverData (F circuitPrime)) : Prop :=
  IsBytes input.publicKey ∧ IsBytes input.digest ∧ IsBytes input.signature

def Spec (input : Input (F circuitPrime)) (_output : Output (F circuitPrime))
    (_data : ProverData (F circuitPrime)) : Prop :=
  Challenge.Specs.ECDSAP256.Spec (bytes input.publicKey) (bytes input.digest) (bytes input.signature)

def ProverAssumptions (input : Input (F circuitPrime)) (data : ProverData (F circuitPrime))
    (_hint : ProverHint (F circuitPrime)) : Prop :=
  Assumptions input data ∧ Spec input () data

def ProverSpec (_input : Input (F circuitPrime)) (_output : Output (F circuitPrime))
    (_hint : ProverHint (F circuitPrime)) : Prop := True

end Challenge.Instances.ECDSA_P256_Digest.Interface
