import Challenge.Specs.ECDSAP256

namespace Tests.Regressions
open Challenge.Specs.ECDSAP256

def nG := bsmul (padBits (natToBits n) 256)
  ({ X := params.gx, Y := params.gy } : AffinePoint K).toProjective params

-- The standard generator is a valid subgroup key even though nG is not the
-- canonical coordinate triple. These checks exercise the PR #215 regression.
#guard nG.X = 0
#guard nG.Z = 0
#guard nG.Y ≠ 0
#guard nG.Y ≠ 1
#guard nG ≠ infinityPoint
#guard nG = nG.Y • (infinityPoint : ProjectivePoint K)

-- Historical PR regression; StandardEcdsaVerify is not challenge acceptance.
example (pk : AffinePoint K) (e r s : Nat)
    (h : StandardEcdsaVerify pk e r s n params) :
    ProjectiveEquiv (bsmul (padBits (natToBits n) 256)
      pk.toProjective params) infinityPoint := h.2.1

-- The circuit requires an affine representative for G + PK. For PK = -G,
-- the nonzero Y at Z=0 prevents its affine equality assertions from holding.
def gMinusG := addE
  ({ X := params.gx, Y := params.gy } : AffinePoint K).toProjective
  ({ X := params.gx, Y := -params.gy } : AffinePoint K).toProjective params
#guard gMinusG.Z = 0
#guard gMinusG.Y ≠ 0

example (q : ProjectivePoint K) (x y : K) (hz : q.Z = 0) (hy : q.Y ≠ 0) :
    ¬ IsPointEquality q x y := by
  intro h
  apply hy
  simpa [hz] using h.2

end Tests.Regressions
