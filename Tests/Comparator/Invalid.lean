import Challenge.Instances.ECDSA_P256_Digest.Interface
namespace ComparatorSmoke
open Challenge.Instances.ECDSA_P256_Digest.Interface
theorem relation (input : Input (F circuitPrime)) (data : ProverData (F circuitPrime)) :
    Spec input () data ↔ Challenge.Specs.ECDSAP256.Spec
      (bytes input.publicKey) (bytes input.digest) (bytes input.signature) := sorry
end ComparatorSmoke
