import Baseline.Circuit
import Baseline.Projected.Algebra

namespace Baseline.Projected.P256Algebra
open Baseline

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem two_ne_zero : (2 : Fp) ≠ 0 := by
  norm_num [Fp, Challenge.Instances.ECDSA_P256_Digest.Interface.circuitPrime,
    Challenge.Specs.ECDSAP256.p]
  decide

theorem discriminant_ne_zero : 4*pa^3+27*pb^2 ≠ 0 := by
  norm_num [pa, pb, Challenge.Specs.ECDSAP256.params, Fp,
    Challenge.Instances.ECDSA_P256_Digest.Interface.circuitPrime,
    Challenge.Specs.ECDSAP256.p]
  decide

end Baseline.Projected.P256Algebra
