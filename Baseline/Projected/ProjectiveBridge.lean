import Baseline.Projected.AffineBridge

namespace Baseline.Projected.AffineBridge
open WeierstrassCurve
variable {F : Type} [Field F] [DecidableEq F]

def liftAffine (x y : F) : ProjectivePoint F := ⟨x,y,1⟩

lemma liftAffine_onCurve (params : CurveParameters F) (x y : F)
    (h : y^2=x^3+params.a*x+params.b) : (liftAffine x y).IsOnCurve params := by
  constructor
  · dsimp [ProjectivePoint.SatisfiesCurveEquation, liftAffine]
    linear_combination h
  · intro hz
    have h := congrArg ProjectivePoint.Z hz
    exact one_ne_zero h

lemma liftAffine_fromAffine (params : CurveParameters F) [params.toMathlib.IsElliptic]
    (x y : F) (h : y^2=x^3+params.a*x+params.b) :
    (liftAffine x y).toMathlibPoint params (liftAffine_onCurve params x y h) =
      (Affine.Point.some x y (short_nonsingular params x y h)).toProjective := by
  rfl

lemma affine_add_projective_group
    (params : CurveParameters F) [params.toMathlib.IsElliptic]
    (xA yA xB yB xR yR l : F)
    (hA : yA^2=xA^3+params.a*xA+params.b)
    (hB : yB^2=xB^3+params.a*xB+params.b)
    (hDx : xB-xA ≠ 0)
    (h₁ : l*(xB-xA)=yB-yA)
    (h₂ : l*l=xA+xB+xR)
    (h₃ : l*(xA-xR)=yA+yR) :
    let hR := Algebra.affine_add_onCurve params.a params.b xA yA xB yB xR yR l hA hB hDx h₁ h₂ h₃
    (liftAffine xR yR).toMathlibPoint params (liftAffine_onCurve params xR yR hR) =
      (liftAffine xA yA).toMathlibPoint params (liftAffine_onCurve params xA yA hA) +
      (liftAffine xB yB).toMathlibPoint params (liftAffine_onCurve params xB yB hB) := by
  classical
  dsimp only
  have hR := Algebra.affine_add_onCurve params.a params.b xA yA xB yB xR yR l hA hB hDx h₁ h₂ h₃
  have hh := affine_add_eq_group params xA yA xB yB xR yR l
    (short_nonsingular params xA yA hA) (short_nonsingular params xB yB hB)
    (short_nonsingular params xR yR hR) hDx h₁ h₂ h₃
  have hm := congrArg (Projective.Point.toAffineAddEquiv params.toMathlib.toProjective).symm hh
  rw [map_add] at hm
  exact hm

lemma affine_add_eq_longfellow
    (params : CurveParameters F) [params.toMathlib.IsElliptic]
    [CurveHasNoPointsOfOrder2 params] [NeZero (2:F)] [NeZero (3:F)]
    (xA yA xB yB xR yR l : F)
    (hA : yA^2=xA^3+params.a*xA+params.b)
    (hB : yB^2=xB^3+params.a*xB+params.b)
    (hDx : xB-xA ≠ 0)
    (h₁ : l*(xB-xA)=yB-yA)
    (h₂ : l*l=xA+xB+xR)
    (h₃ : l*(xA-xR)=yA+yR) :
    ProjectiveEquiv (liftAffine xR yR)
      (addE (liftAffine xA yA) (liftAffine xB yB) params) := by
  have hpa := liftAffine_onCurve params xA yA hA
  have hpb := liftAffine_onCurve params xB yB hB
  have hpr := liftAffine_onCurve params xR yR
    (Algebra.affine_add_onCurve params.a params.b xA yA xB yB xR yR l hA hB hDx h₁ h₂ h₃)
  apply (toMathlibPoint_eq_iff_ProjectiveEquiv _ _ params hpr (addE_on_curve _ _ params hpa hpb)).mp
  rw [toMathlibPoint_add]
  exact affine_add_projective_group params xA yA xB yB xR yR l hA hB hDx h₁ h₂ h₃

lemma elm_eq_longfellow
    (params : CurveParameters F) [params.toMathlib.IsElliptic]
    [CurveHasNoPointsOfOrder2 params] [NeZero (2:F)] [NeZero (3:F)]
    (xA yA xB yB xU xS yS l₁ l₂ : F)
    (hDisc : 4*params.a^3+27*params.b^2 ≠ 0)
    (hA : yA^2=xA^3+params.a*xA+params.b)
    (hB : yB^2=xB^3+params.a*xB+params.b)
    (hDx : xB-xA ≠ 0)
    (h₁ : l₁*(xB-xA)=yB-yA)
    (h₂ : l₁*l₁=xA+xB+xU)
    (h₃ : (l₁+l₂)*(xA-xU)=2*yA)
    (h₄ : l₂*l₂=xA+xU+xS)
    (h₅ : l₂*(xA-xS)=yS+yA) :
    ProjectiveEquiv (liftAffine xS yS)
      (addE (doubleE (liftAffine xA yA) params) (liftAffine xB yB) params) := by
  classical
  have hTwo : (2:F) ≠ 0 := NeZero.ne _
  have hS := Algebra.elm_output_onCurve params.a params.b xA yA xB yB xU xS yS l₁ l₂
    hTwo hDisc hA hB hDx h₁ h₂ h₃ h₄ h₅
  have hpa := liftAffine_onCurve params xA yA hA
  have hpb := liftAffine_onCurve params xB yB hB
  have hps := liftAffine_onCurve params xS yS hS
  apply (toMathlibPoint_eq_iff_ProjectiveEquiv _ _ params hps
    (addE_on_curve _ _ params (doubleE_on_curve _ params hpa) hpb)).mp
  rw [toMathlibPoint_add (doubleE (liftAffine xA yA) params) (liftAffine xB yB) params
    (doubleE_on_curve _ params hpa) hpb, toMathlibPoint_double _ params hpa]
  have hh := elm_eq_group params xA yA xB yB xU xS yS l₁ l₂
    hTwo hDisc hA hB hDx h₁ h₂ h₃ h₄ h₅
  have hm := congrArg (Projective.Point.toAffineAddEquiv params.toMathlib.toProjective).symm hh
  rw [map_add, map_nsmul] at hm
  exact hm

lemma affine_double_eq_longfellow
    (params : CurveParameters F) [params.toMathlib.IsElliptic]
    [CurveHasNoPointsOfOrder2 params] [NeZero (2:F)] [NeZero (3:F)]
    (x y xR yR l : F)
    (hDisc : 4*params.a^3+27*params.b^2 ≠ 0)
    (hA : y^2=x^3+params.a*x+params.b)
    (h₁ : (2*y)*l=3*x^2+params.a)
    (h₂ : l*l=2*x+xR)
    (h₃ : l*(x-xR)=y+yR) :
    ProjectiveEquiv (liftAffine xR yR) (doubleE (liftAffine x y) params) := by
  classical
  have hR := Algebra.affine_double_onCurve params.a params.b x y xR yR l hA h₁ h₂ h₃
  have hy := Algebra.double_denominator_ne params.a params.b x y l (NeZero.ne _) hDisc hA h₁
  have hpa := liftAffine_onCurve params x y hA
  have hpr := liftAffine_onCurve params xR yR hR
  apply (toMathlibPoint_eq_iff_ProjectiveEquiv _ _ params hpr (doubleE_on_curve _ params hpa)).mp
  rw [toMathlibPoint_double _ params hpa]
  have hh := affine_double_eq_group params x y xR yR l
    (short_nonsingular params x y hA) (short_nonsingular params xR yR hR) hy h₁ h₂ h₃
  have hm := congrArg (Projective.Point.toAffineAddEquiv params.toMathlib.toProjective).symm hh
  rw [map_nsmul] at hm
  exact hm

end Baseline.Projected.AffineBridge
