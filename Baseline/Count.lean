import Baseline.Circuit

namespace Baseline
open Challenge.CostR1CS Challenge.Instances.ECDSA_P256_Digest.Interface

def inputVar : Var Input Fp := varFromOffset Input 0

/-- Number of fixed input field elements (3 statement + 1034 witness). -/
def numInputs : Nat := 1037

def baselineCount : Count := circuitCount (Baseline.main inputVar) numInputs

end Baseline
