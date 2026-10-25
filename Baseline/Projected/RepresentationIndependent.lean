/-
# Copyright 2026 Google LLC.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
-/

import Baseline.Projected.NaturalBoundLF

namespace RepresentationBridge
variable {F : Type} [Field F] [NeZero (2 : F)] [NeZero (3 : F)]
  [NeZero (4 : F)] [NeZero (5 : F)] [NeZero (6 : F)] [NeZero (7 : F)]

def OriginalFiniteSums (pk : AffinePoint F) (rx ry : F)
    (params : CurveParameters F) : Prop :=
  let G := ({ X := params.gx, Y := params.gy } : AffinePoint F).toProjective
  let R := ({ X := rx, Y := ry } : AffinePoint F).toProjective
  let RQ := addE R pk.toProjective params
  (addE G pk.toProjective params).Z ≠ 0 ∧
  (addE R G params).Z ≠ 0 ∧ RQ.Z ≠ 0 ∧
  (addE G ({ X := RQ.X * RQ.Z⁻¹, Y := RQ.Y * RQ.Z⁻¹ } : AffinePoint F).toProjective params).Z ≠ 0

lemma pre_implies_finite_sums (pk : AffinePoint F) (rx ry : F) (pre : List F)
    (params : CurveParameters F)
    [h_ell : (params.toMathlib).IsElliptic] [CurveHasNoPointsOfOrder2 params]
    (h_G_on : ProjectivePoint.IsOnCurve
      ({ X := params.gx, Y := params.gy } : AffinePoint F).toProjective params)
    (h_on_pk : pk.IsOnCurve params)
    (h_on_r : AffinePoint.IsOnCurve { X := rx, Y := ry } params)
    (hpre : ValidPreComputationExact pk rx ry pre params) :
    OriginalFiniteSums pk rx ry params := by
  rcases hpre with ⟨h_pre_len, h_gpk_eq, h_gr_eq, h_rpk_eq, h_grpk_eq⟩
  have h_PK_proj_on : ProjectivePoint.IsOnCurve pk.toProjective params :=
    affine_to_projective_on_curve pk params h_on_pk
  have h_R_proj_on : ProjectivePoint.IsOnCurve
      ({ X := rx, Y := ry } : AffinePoint F).toProjective params :=
    affine_to_projective_on_curve _ params h_on_r
  -- Inline proofs for Z-coordinate exceptional bounds
  have h_GPK_on : ProjectivePoint.IsOnCurve (addE ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective pk.toProjective params) params :=
    addE_on_curve ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective pk.toProjective params h_G_on h_PK_proj_on
  have h_GPK_Z : (addE ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective pk.toProjective params).Z ≠ 0 :=
    z_ne_zero_of_point_equality_and_on_curve (addE ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective pk.toProjective params) (pre.getD 0 0) (pre.getD 1 0) params h_GPK_on h_gpk_eq

  have h_GR_on : ProjectivePoint.IsOnCurve (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params) params :=
    addE_on_curve ({ X := rx, Y := ry : AffinePoint F }).toProjective ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params h_R_proj_on h_G_on
  have h_GR_Z : (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params).Z ≠ 0 :=
    z_ne_zero_of_point_equality_and_on_curve (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params) (pre.getD 2 0) (pre.getD 3 0) params h_GR_on h_gr_eq

  have h_RPK_on : ProjectivePoint.IsOnCurve (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params) params :=
    addE_on_curve ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params h_R_proj_on h_PK_proj_on
  have h_RPK_Z : (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params).Z ≠ 0 :=
    z_ne_zero_of_point_equality_and_on_curve (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params) (pre.getD 4 0) (pre.getD 5 0) params h_RPK_on h_rpk_eq

  have h_RPK_proj_on : ProjectivePoint.IsOnCurve ({ X := pre.getD 4 0, Y := pre.getD 5 0 : AffinePoint F }).toProjective params :=
    projective_point_on_curve_of_point_equality (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params) (pre.getD 4 0) (pre.getD 5 0) params h_RPK_on h_RPK_Z h_rpk_eq
  have h_GRPK_on : ProjectivePoint.IsOnCurve (addE ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective ({ X := pre.getD 4 0, Y := pre.getD 5 0 : AffinePoint F }).toProjective params) params :=
    addE_on_curve ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective ({ X := pre.getD 4 0, Y := pre.getD 5 0 : AffinePoint F }).toProjective params h_G_on h_RPK_proj_on
  have h_GRPK_Z : (addE ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective { X := (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params).X * (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params).Z⁻¹, Y := (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params).Y * (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params).Z⁻¹, Z := 1 } params).Z ≠ 0 := by
    have h_pt_eq : { X := (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params).X * (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params).Z⁻¹, Y := (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params).Y * (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params).Z⁻¹, Z := 1 } =
                   ({ X := pre.getD 4 0, Y := pre.getD 5 0 : AffinePoint F }).toProjective := by
      ext
      · dsimp
        have hx := h_rpk_eq.1
        rw [hx]
        rw [mul_comm (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params).Z, mul_assoc, mul_inv_cancel₀ h_RPK_Z, mul_one]
      · dsimp
        have hy := h_rpk_eq.2
        rw [hy]
        rw [mul_comm (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params).Z, mul_assoc, mul_inv_cancel₀ h_RPK_Z, mul_one]
      · rfl
    rw [h_pt_eq]
    exact z_ne_zero_of_point_equality_and_on_curve (addE ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective ({ X := pre.getD 4 0, Y := pre.getD 5 0 : AffinePoint F }).toProjective params) (pre.getD 6 0) (pre.getD 7 0) params h_GRPK_on h_grpk_eq

  exact ⟨h_GPK_Z, h_GR_Z, h_RPK_Z, h_GRPK_Z⟩

lemma finite_sums_implies_pre (pk : AffinePoint F) (rx ry : F)
    (params : CurveParameters F) (h : OriginalFiniteSums pk rx ry params) :
    ∃ pre, ValidPreComputationExact pk rx ry pre params := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨pre, _, hp⟩ := exists_pre_computation pk rx ry params h1 h2 h3 h4
  exact ⟨pre, hp⟩

/-- Signature-bound acceptance expressed solely using scalar values, the
signature point, the group equation, and Longfellow's four finite-sum exclusions.
No source bits, inverse witnesses, tables, or loop coordinates occur here. -/
def RepresentationIndependentLF (pk : AffinePoint F) (e : F) (r s order : Nat)
    (params : CurveParameters F) : Prop :=
  ∃ (E t : Nat) (ry : F),
    E < 2^params.kBits ∧ (E : F) = e ∧
    r < order ∧ t < order ∧ order - t = s ∧
    pk.IsOnCurve params ∧ AffinePoint.IsOnCurve { X := (r : F), Y := ry } params ∧
    (r : F) ≠ 0 ∧ (t : F) ≠ 0 ∧ pk.X ≠ 0 ∧
    OriginalFiniteSums pk (r : F) ry params ∧
    (ScalarCombination pk E r t ry params).X = 0 ∧
    (ScalarCombination pk E r t ry params).Z = 0

lemma natural_iff_representation_independent (pk : AffinePoint F) (e : F) (r s order : Nat)
    (params : CurveParameters F)
    [h_ell : (params.toMathlib).IsElliptic] [CurveHasNoPointsOfOrder2 params]
    (h_G_on : ProjectivePoint.IsOnCurve
      ({ X := params.gx, Y := params.gy } : AffinePoint F).toProjective params) :
    NaturalBoundLF pk e r s order params ↔ RepresentationIndependentLF pk e r s order params := by
  constructor
  · rintro ⟨E, t, ry, pre, hE, he, hr, ht, hs, hpk, hR, hrnz, htnz, hpkz, hpre, hx, hz⟩
    exact ⟨E, t, ry, hE, he, hr, ht, hs, hpk, hR, hrnz, htnz, hpkz,
      pre_implies_finite_sums pk (r : F) ry pre params h_G_on hpk hR hpre, hx, hz⟩
  · rintro ⟨E, t, ry, hE, he, hr, ht, hs, hpk, hR, hrnz, htnz, hpkz, hfinite, hx, hz⟩
    obtain ⟨pre, hp⟩ := finite_sums_implies_pre pk (r : F) ry params hfinite
    exact ⟨E, t, ry, pre, hE, he, hr, ht, hs, hpk, hR, hrnz, htnz, hpkz, hp, hx, hz⟩

/-- Exact equivalence. The only extra hypotheses concern curve arithmetic and
parameter bounds, not the particular signature or supplied digest lift. -/
theorem boundLF_iff_representation_independent (pk : AffinePoint F) (e : F) (r s order : Nat)
    (params : CurveParameters F)
    [h_ell : (params.toMathlib).IsElliptic] [CurveHasNoPointsOfOrder2 params]
    (h_G_on : ProjectivePoint.IsOnCurve
      ({ X := params.gx, Y := params.gy } : AffinePoint F).toProjective params)
    (horder : order < 2^params.kBits) :
    BoundLF pk e r s order params ↔ RepresentationIndependentLF pk e r s order params :=
  (boundLF_iff_natural pk e r s order params h_G_on horder).trans
    (natural_iff_representation_independent pk e r s order params h_G_on)

end RepresentationBridge
#print axioms RepresentationBridge.boundLF_iff_representation_independent
