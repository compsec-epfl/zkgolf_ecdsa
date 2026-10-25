import ECDSA.ECBridge
import Baseline.Projected.Algebra

/-! Correspondence between guarded affine R1CS equations and Mathlib's actual
elliptic-curve group law. This is a component proof, not the complete circuit proof. -/
namespace Baseline.Projected.AffineBridge

open WeierstrassCurve
variable {F : Type} [Field F] [DecidableEq F]

abbrev W (params : CurveParameters F) := params.toMathlib.toAffine

lemma affine_add_eq_group
    (params : CurveParameters F) (xA yA xB yB xR yR l : F)
    (hA : (W params).Nonsingular xA yA)
    (hB : (W params).Nonsingular xB yB)
    (hR : (W params).Nonsingular xR yR)
    (hDx : xB-xA ≠ 0)
    (h₁ : l*(xB-xA) = yB-yA)
    (h₂ : l*l = xA+xB+xR)
    (h₃ : l*(xA-xR) = yA+yR) :
    Affine.Point.some xR yR hR =
      Affine.Point.some xA yA hA + Affine.Point.some xB yB hB := by
  classical
  have hx : xA ≠ xB := by
    intro h
    apply hDx
    rw [h, sub_self]
  have hs : (W params).slope xA xB yA yB = l := by
    rw [Affine.slope_of_X_ne hx]
    apply (div_eq_iff (sub_ne_zero.mpr hx)).mpr
    linear_combination h₁
  have hX : (W params).addX xA xB l = xR := by
    dsimp [Affine.addX, W, CurveParameters.toMathlib]
    linear_combination h₂
  have hY : (W params).addY xA xB yA l = yR := by
    simp only [Affine.addY, Affine.negAddY, hX]
    dsimp [Affine.negY, W, CurveParameters.toMathlib]
    linear_combination h₃
  rw [Affine.Point.add_of_X_ne hx, Affine.Point.some.injEq]
  constructor
  · rw [hs]; exact hX.symm
  · rw [hs]; exact hY.symm

lemma affine_double_eq_group
    (params : CurveParameters F) (x y xR yR l : F)
    (hA : (W params).Nonsingular x y)
    (hR : (W params).Nonsingular xR yR)
    (hy : 2*y ≠ 0)
    (h₁ : (2*y)*l = 3*x^2+params.a)
    (h₂ : l*l = 2*x+xR)
    (h₃ : l*(x-xR) = y+yR) :
    Affine.Point.some xR yR hR = 2 • (Affine.Point.some x y hA) := by
  classical
  have hy' : y ≠ (W params).negY x y := by
    intro h
    dsimp [W, Affine.negY, CurveParameters.toMathlib] at h
    apply hy
    linear_combination h
  have hs : (W params).slope x x y y = l := by
    rw [Affine.slope_of_Y_ne rfl hy']
    dsimp [W, Affine.negY, CurveParameters.toMathlib]
    have hh : y-(-y-0*x-0) = 2*y := by ring
    rw [hh]
    apply (div_eq_iff hy).mpr
    linear_combination -h₁
  have hX : (W params).addX x x l = xR := by
    dsimp [Affine.addX, W, CurveParameters.toMathlib]
    linear_combination h₂
  have hY : (W params).addY x x y l = yR := by
    simp only [Affine.addY, Affine.negAddY, hX]
    dsimp [Affine.negY, W, CurveParameters.toMathlib]
    linear_combination h₃
  rw [two_nsmul, Affine.Point.add_self_of_Y_ne hy', Affine.Point.some.injEq]
  constructor
  · rw [hs]; exact hX.symm
  · rw [hs]; exact hY.symm

lemma short_nonsingular
    (params : CurveParameters F) [params.toMathlib.IsElliptic]
    (x y : F) (h : y^2=x^3+params.a*x+params.b) :
    (W params).Nonsingular x y := by
  apply Affine.equation_iff_nonsingular.mp
  rw [Affine.equation_iff]
  dsimp [W, CurveParameters.toMathlib]
  linear_combination h

lemma elm_eq_group
    (params : CurveParameters F) [params.toMathlib.IsElliptic]
    (xA yA xB yB xU xS yS l₁ l₂ : F)
    (hTwo : (2 : F) ≠ 0)
    (hDisc : 4*params.a^3+27*params.b^2 ≠ 0)
    (hA : yA^2=xA^3+params.a*xA+params.b)
    (hB : yB^2=xB^3+params.a*xB+params.b)
    (hDx : xB-xA ≠ 0)
    (h₁ : l₁*(xB-xA)=yB-yA)
    (h₂ : l₁*l₁=xA+xB+xU)
    (h₃ : (l₁+l₂)*(xA-xU)=2*yA)
    (h₄ : l₂*l₂=xA+xU+xS)
    (h₅ : l₂*(xA-xS)=yS+yA) :
    let hS := Algebra.elm_output_onCurve params.a params.b xA yA xB yB xU xS yS l₁ l₂
      hTwo hDisc hA hB hDx h₁ h₂ h₃ h₄ h₅
    Affine.Point.some xS yS (short_nonsingular params xS yS hS) =
      2 • Affine.Point.some xA yA (short_nonsingular params xA yA hA) +
        Affine.Point.some xB yB (short_nonsingular params xB yB hB) := by
  dsimp only
  let yU := Algebra.elmMiddleY xA yA xU l₁
  have hYU : l₁*(xA-xU)=yA+yU := by simp [yU, Algebra.elmMiddleY]
  have hU := Algebra.affine_add_onCurve params.a params.b xA yA xB yB xU yU l₁ hA hB hDx h₁ h₂ hYU
  have hD2 := Algebra.elm_second_denominator_ne params.a params.b xA yA xB yB xU l₁ l₂
    hTwo hDisc hA hB hDx h₁ h₂ h₃
  have hD2' : xU-xA ≠ 0 := by
    intro h
    apply hD2
    linear_combination -h
  have hSlope := Algebra.elm_second_slope xA yA xU l₁ l₂ h₃
  have hSlope' : l₂*(xU-xA)=yU-yA := by
    dsimp [yU]
    linear_combination -hSlope
  have huGroup := affine_add_eq_group params xA yA xB yB xU yU l₁
    (short_nonsingular params xA yA hA) (short_nonsingular params xB yB hB)
    (short_nonsingular params xU yU hU) hDx h₁ h₂ hYU
  have hsGroup := affine_add_eq_group params xA yA xU yU xS yS l₂
    (short_nonsingular params xA yA hA) (short_nonsingular params xU yU hU)
    (short_nonsingular params xS yS (Algebra.elm_output_onCurve params.a params.b xA yA xB yB xU xS yS l₁ l₂
      hTwo hDisc hA hB hDx h₁ h₂ h₃ h₄ h₅)) hD2' hSlope' h₄ (by linear_combination h₅)
  rw [hsGroup, huGroup, two_nsmul]
  abel

end Baseline.Projected.AffineBridge
