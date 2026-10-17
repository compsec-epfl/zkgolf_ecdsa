/- Trusted comparator template, NOT a solution.
The sorry placeholders mirror the upstream challenge format. Submitted proofs
must not depend on sorryAx; no baseline circuit or par is claimed here. -/
import Challenge.Specs.ECDSAP256
import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Challenge.Utils.CostR1CS
import Challenge.Utils.WitgenIR
import Challenge.Instances.ECDSA_P256_Digest.Interface
import Challenge.Instances.ECDSA_P256_Digest.Cost


/-!
Trusted challenge statements for the ECDSA P-256 supplied-digest instance.

This file is the trusted boundary: it owns the input/output type and the
statements the implementation must prove. The implementation may be arbitrary,
but its exported proofs must have exactly these types.
-/

namespace Solution.ECDSA_P256_Digest

open Challenge.Instances.ECDSA_P256_Digest.Interface

def main : Var Input (F circuitPrime) → Circuit (F circuitPrime) (Var Output (F circuitPrime)) := sorry

instance elaborated : ElaboratedCircuit (F circuitPrime) Input Output main := sorry

theorem soundness : GeneralFormalCircuit.Soundness (F circuitPrime) main Assumptions Spec := sorry
theorem completeness : GeneralFormalCircuit.Completeness (F circuitPrime) main ProverAssumptions ProverSpec := sorry

theorem mainCost : Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ := sorry
theorem isR1CS : Challenge.CostR1CS.isR1CS main := sorry
theorem witgenIsIR : Challenge.WitgenIR.witgenIsIR main := sorry

theorem computableWitness : ∀ n input,
  ProverEnvironment.OnlyAccessedBelow n (fun env : ProverEnvironment (F circuitPrime) => eval env input) →
  Circuit.ComputableWitnesses (main input) n := sorry

theorem requirementsChannelsLawful : ∀ input offset,
  ((main input).operations offset).RequirementsChannelsLawful
    elaborated.channelsWithGuarantees [] := sorry

def formalCircuit : GeneralFormalCircuit (F circuitPrime) Input Output :=
  {
    main := main
    requirementsChannelsLawful := requirementsChannelsLawful
    Assumptions := Assumptions
    Spec := Spec
    ProverAssumptions := ProverAssumptions
    ProverSpec := ProverSpec
    soundness := soundness
    completeness := completeness
  }

end Solution.ECDSA_P256_Digest
