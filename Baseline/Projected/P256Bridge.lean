import Baseline.Projected.RepresentationIndependent
import Challenge.Specs.ECDSAP256
import ECDSA.P256NoRoot

namespace RepresentationBridge.P256
open Challenge.Specs.ECDSAP256

instance : NeZero (2 : K) := ⟨by decide⟩
instance : NeZero (3 : K) := ⟨by decide⟩
instance : NeZero (4 : K) := ⟨by decide⟩
instance : NeZero (5 : K) := ⟨by decide⟩
instance : NeZero (6 : K) := ⟨by decide⟩
instance : NeZero (7 : K) := ⟨by decide⟩

instance : (params.toMathlib).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  decide

/-- Specialization of Google's checked no-root certificate, preserving its proof. -/
instance : CurveHasNoPointsOfOrder2 params where
  no_roots x := by
    have ha : ((ECDSA.aa : ℕ) : ZMod ECDSA.pp) = -3 := by
      have haa : (ECDSA.aa : ℕ) = ECDSA.pp - 3 := by norm_num [ECDSA.aa, ECDSA.pp]
      rw [haa, Nat.cast_sub (by norm_num [ECDSA.pp]), ZMod.natCast_self]
      push_cast
      ring
    have hb : ((ECDSA.bb : ℕ) : ZMod ECDSA.pp) =
        (0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B : ZMod ECDSA.pp) := by
      norm_cast
    have h := ECDSA.p256_cubic_no_root x
    intro hc
    simp only [params] at hc
    refine h ?_
    rw [ha, hb]
    exact hc

lemma generator_on_curve : ProjectivePoint.IsOnCurve
    ({ X := params.gx, Y := params.gy } : AffinePoint K).toProjective params := by
  apply affine_to_projective_on_curve
  unfold AffinePoint.IsOnCurve
  decide

/-- The projected source-witness relation is equivalent to the natural-scalar,
representation-independent relation on the challenge's exact P-256 parameters.
No per-signature hypotheses and no unproved subgroup/cardinality assumptions. -/
theorem p256_boundLF_iff_representation_independent (pk : AffinePoint K)
    (digest : K) (r s : Nat) :
    BoundLF pk digest r s n params ↔ RepresentationIndependentLF pk digest r s n params :=
  boundLF_iff_representation_independent pk digest r s n params generator_on_curve (by decide)

end RepresentationBridge.P256
#print axioms RepresentationBridge.P256.p256_boundLF_iff_representation_independent
