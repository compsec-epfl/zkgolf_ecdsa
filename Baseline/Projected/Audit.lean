import Baseline.Projected.P256Bridge
import Baseline.Projected.P256Algebra
import Baseline.Projected.ProjectiveBridge
import Baseline.Projected.OffsetExistence

/-! Audit the actual proof dependencies. These should contain only Lean's
standard axioms, never `sorryAx` or a bespoke cryptographic assumption. -/
#print axioms RepresentationBridge.P256.p256_boundLF_iff_representation_independent
#print axioms Baseline.Projected.AffineBridge.affine_add_eq_longfellow
#print axioms Baseline.Projected.AffineBridge.affine_double_eq_longfellow
#print axioms Baseline.Projected.AffineBridge.elm_eq_longfellow
#print axioms Baseline.Projected.Algebra.elm_second_denominator_ne
#print axioms Baseline.Projected.Algebra.double_denominator_ne
#print axioms Baseline.Projected.P256Algebra.discriminant_ne_zero
#print axioms RepresentationBridge.OffsetExistence.exists_avoiding_injective_equations
