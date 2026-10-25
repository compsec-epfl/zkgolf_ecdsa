import ECDSA.EcdsaCircuit

/-!
Local field-algebra lemmas for the experimental offset circuit.
These prove preservation of the affine curve equation and redundancy of selected
inverse guards. They do not prove the complete Clean circuit contract or its
correspondence with Longfellow's projective group operation.
-/

namespace Baseline.Projected.Algebra

section ELM
variable {F : Type} [Field F]

/-- Reconstruct the omitted middle y-coordinate in double-and-add. -/
def elmMiddleY (xA yA xU l₁ : F) : F := l₁ * (xA - xU) - yA

lemma elm_second_slope (xA yA xU l₁ l₂ : F)
    (h : (l₁ + l₂) * (xA - xU) = 2 * yA) :
    l₂ * (xA - xU) = yA - elmMiddleY xA yA xU l₁ := by
  dsimp [elmMiddleY]
  linear_combination h

/-- Five ELM rows imply all six ordinary chord-addition rows, with the middle
    y-coordinate supplied by a linear combination of one product.  Curve group
    interpretation additionally needs distinct-x hypotheses at both additions. -/
lemma elm_two_additions (xA yA xB yB xU xS yS l₁ l₂ : F)
    (h₁ : l₁ * (xB - xA) = yB - yA)
    (h₂ : l₁ * l₁ = xA + xB + xU)
    (h₃ : (l₁ + l₂) * (xA - xU) = 2 * yA)
    (h₄ : l₂ * l₂ = xA + xU + xS)
    (h₅ : l₂ * (xA - xS) = yS + yA) :
    let yU := elmMiddleY xA yA xU l₁
    (l₁ * (xB - xA) = yB - yA ∧
      l₁ * l₁ = xA + xB + xU ∧
      l₁ * (xA - xU) = yU + yA) ∧
    (l₂ * (xA - xU) = yA - yU ∧
      l₂ * l₂ = xU + xA + xS ∧
      l₂ * (xA - xS) = yS + yA) := by
  dsimp
  refine ⟨⟨h₁, h₂, ?_⟩, ⟨elm_second_slope xA yA xU l₁ l₂ h₃, ?_, h₅⟩⟩
  · simp [elmMiddleY]
  · linear_combination h₄

lemma alternating_offset_step {G : Type} [AddCommGroup G]
    (C T H : G) :
    (C + H) + (C + H) + (T - (3 : ℤ) • H) =
      (C + C + T) - H := by
  simp only [show (3 : ℤ) = 1 + 1 + 1 by decide, add_zsmul, one_zsmul]
  abel

end ELM

section
variable {F : Type} [Field F]

/-- The second ELM denominator cannot vanish on a nonsingular short Weierstrass
curve if the first addition is a checked ordinary addition. -/
theorem elm_second_denominator_ne
    (a b xA yA xB yB xU l₁ l₂ : F)
    (hTwo : (2 : F) ≠ 0)
    (hDisc : 4*a^3 + 27*b^2 ≠ 0)
    (hA : yA^2 = xA^3 + a*xA + b)
    (hB : yB^2 = xB^3 + a*xB + b)
    (hDx : xB-xA ≠ 0)
    (h₁ : l₁*(xB-xA) = yB-yA)
    (h₂ : l₁*l₁ = xA+xB+xU)
    (h₃ : (l₁+l₂)*(xA-xU) = 2*yA) :
    xA-xU ≠ 0 := by
  intro hZero
  have hx : xU = xA := by linear_combination -hZero
  subst xU
  have hy : yA = 0 := by
    have h : 2*yA = 0 := by simpa using h₃.symm
    exact (mul_eq_zero.mp h).resolve_left hTwo
  subst yA
  have hD : (xB-xA) * (3*xA^2+a) = 0 := by
    linear_combination -(l₁*(xB-xA)+yB)*h₁ + (xB-xA)^2*h₂ - hB + hA
  have hDeriv : 3*xA^2+a = 0 := (mul_eq_zero.mp hD).resolve_left hDx
  have ha : a = -3*xA^2 := by linear_combination hDeriv
  have hb : b = 2*xA^3 := by linear_combination -hA - xA*hDeriv
  apply hDisc
  rw [ha, hb]
  ring
end

section
variable {F : Type} [Field F]

theorem affine_add_onCurve
    (a b xA yA xB yB xR yR l : F)
    (hA : yA^2 = xA^3+a*xA+b)
    (hB : yB^2 = xB^3+a*xB+b)
    (hDx : xB-xA ≠ 0)
    (h₁ : l*(xB-xA) = yB-yA)
    (h₂ : l*l = xA+xB+xR)
    (h₃ : l*(xA-xR) = yA+yR) :
    yR^2 = xR^3+a*xR+b := by
  have hT : (xB-xA)*(l^2*(xB-xA)+2*l*yA-xB^2-xA*xB-xA^2-a) = 0 := by
    linear_combination (l*(xB-xA)+yB+yA)*h₁ + hB - hA
  have hReduced : l^2*(xB-xA)+2*l*yA-xB^2-xA*xB-xA^2-a = 0 :=
    (mul_eq_zero.mp hT).resolve_left hDx
  linear_combination hA + (xR-xA)*hReduced + (xR-xA)*(xR-xB)*h₂ -
    (l*(xA-xR)-yA+yR)*h₃

theorem double_denominator_ne
    (a b x y l : F)
    (hTwo : (2 : F) ≠ 0)
    (hDisc : 4*a^3+27*b^2 ≠ 0)
    (hCurve : y^2 = x^3+a*x+b)
    (hSlope : (2*y)*l = 3*x^2+a) :
    2*y ≠ 0 := by
  intro hz
  have hy : y = 0 := (mul_eq_zero.mp hz).resolve_left hTwo
  subst y
  have hDeriv : 3*x^2+a = 0 := by simpa using hSlope.symm
  have ha : a = -3*x^2 := by linear_combination hDeriv
  have hb : b = 2*x^3 := by linear_combination -hCurve - x*hDeriv
  apply hDisc
  rw [ha, hb]
  ring

theorem elm_output_onCurve
    (a b xA yA xB yB xU xS yS l₁ l₂ : F)
    (hTwo : (2 : F) ≠ 0)
    (hDisc : 4*a^3+27*b^2 ≠ 0)
    (hA : yA^2 = xA^3+a*xA+b)
    (hB : yB^2 = xB^3+a*xB+b)
    (hDx : xB-xA ≠ 0)
    (h₁ : l₁*(xB-xA) = yB-yA)
    (h₂ : l₁*l₁ = xA+xB+xU)
    (h₃ : (l₁+l₂)*(xA-xU) = 2*yA)
    (h₄ : l₂*l₂ = xA+xU+xS)
    (h₅ : l₂*(xA-xS) = yS+yA) :
    yS^2 = xS^3+a*xS+b := by
  let yU := elmMiddleY xA yA xU l₁
  have hm : l₁*(xA-xU) = yA+yU := by simp [yU, elmMiddleY]
  have hU := affine_add_onCurve a b xA yA xB yB xU yU l₁ hA hB hDx h₁ h₂ hm
  have hd := elm_second_denominator_ne a b xA yA xB yB xU l₁ l₂
    hTwo hDisc hA hB hDx h₁ h₂ h₃
  have hSlope := elm_second_slope xA yA xU l₁ l₂ h₃
  have hSlope' : l₂*(xU-xA) = yU-yA := by
    dsimp [yU]
    linear_combination -hSlope
  have hd' : xU-xA ≠ 0 := by
    intro h
    apply hd
    linear_combination -h
  apply affine_add_onCurve a b xA yA xU yU xS yS l₂ hA hU hd' hSlope' h₄
  linear_combination h₅


theorem affine_double_onCurve
    (a b x y xR yR l : F)
    (hCurve : y^2 = x^3+a*x+b)
    (hSlope : (2*y)*l = 3*x^2+a)
    (hX : l*l = 2*x+xR)
    (hY : l*(x-xR) = y+yR) :
    yR^2 = xR^3+a*xR+b := by
  linear_combination hCurve + (xR-x)*hSlope + (xR-x)^2*hX -
    (l*(x-xR)-y+yR)*hY

/-- A unified affine addition gadget supports ordinary addition and doubling.
    The second slope equation eliminates the arbitrary-slope hole at equal inputs. -/
theorem unified_affine_add_onCurve
    (a b xA yA xB yB xR yR l : F)
    (hA : yA^2 = xA^3+a*xA+b)
    (hB : yB^2 = xB^3+a*xB+b)
    (h₁ : l*(xB-xA) = yB-yA)
    (h₂ : l*(yA+yB) = xA^2+xA*xB+xB^2+a)
    (h₃ : l*l = xA+xB+xR)
    (h₄ : l*(xA-xR) = yA+yR) :
    yR^2 = xR^3+a*xR+b := by
  by_cases hd : xB-xA = 0
  · have hx : xB = xA := sub_eq_zero.mp hd
    subst xB
    have hy : yB = yA := by linear_combination -h₁
    subst yB
    apply affine_double_onCurve a b xA yA xR yR l hA
    · linear_combination h₂
    · linear_combination h₃
    · exact h₄
  · exact affine_add_onCurve a b xA yA xB yB xR yR l hA hB hd h₁ h₃ h₄

end
end Baseline.Projected.Algebra
