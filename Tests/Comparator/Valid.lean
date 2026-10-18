import Challenge.Instances.ECDSA_P256_Digest.Interface
namespace ComparatorSmoke
open Challenge.Instances.ECDSA_P256_Digest.Interface
theorem relation (input : Input (F circuitPrime)) (data : ProverData (F circuitPrime)) :
    Spec input () data ↔ ValidEcdsaWitness (witness input)
      ({ X := input.pkX, Y := input.pkY } : AffinePoint (F circuitPrime))
      input.digest Challenge.Specs.ECDSAP256.n Challenge.Specs.ECDSAP256.params := Iff.rfl
end ComparatorSmoke
