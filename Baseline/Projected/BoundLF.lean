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

import ECDSA.Ecdsa

/-!
An existential projection of the original Longfellow relation, binding the signature.
This is NOT a change to the existing pointwise challenge.
CoreChecks retains the exact scalar encoding, field-digest equality, curves,
inverses, ranges, and original affine-precomputation restrictions.  All witness
fields are existential here; intermediate loop coordinates do not occur in the
right-hand group relation.
-/
set_option linter.unusedSectionVars false

namespace RepresentationBridge

variable {F : Type} [Field F] [NeZero (2 : F)] [NeZero (3 : F)]
  [NeZero (4 : F)] [NeZero (5 : F)] [NeZero (6 : F)] [NeZero (7 : F)]

def BoundLF (pk : AffinePoint F) (e : F) (r s order : Nat)
    (params : CurveParameters F) : Prop :=
  ∃ w : EcdsaWitness F, ValidEcdsaWitness w pk e order params ∧
    natR (w.bi.map val3) = r ∧ order - natS (w.bi.map val3) = s

def CoreChecks (w : EcdsaWitness F) (pk : AffinePoint F) (e : F)
    (order : Nat) (params : CurveParameters F) : Prop :=
  w.bi.length = params.kBits ∧
  (∀ v ∈ w.bi, v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7) ∧
  ValidPreComputationExact pk w.rx w.ry w.pre params ∧
  reconstructE (w.bi.map val3) = e ∧
  reconstructR (w.bi.map val3) = w.rx ∧
  pk.IsOnCurve params ∧
  AffinePoint.IsOnCurve { X := w.rx, Y := w.ry } params ∧
  w.rx * w.rx_inv = 1 ∧
  reconstructS (w.bi.map val3) * w.s_inv = 1 ∧
  pk.X * w.pk_inv = 1 ∧
  natR (w.bi.map val3) < order ∧
  natS (w.bi.map val3) < order

noncomputable def LinearCombination (w : EcdsaWitness F) (pk : AffinePoint F)
    (params : CurveParameters F) : ProjectivePoint F :=
  let bi := w.bi.map val3
  let eG := bsmul (padBits (natToBits (natE bi)) params.kBits)
    ({ X := params.gx, Y := params.gy } : AffinePoint F).toProjective params
  let rQ := bsmul (padBits (natToBits (natR bi)) params.kBits) pk.toProjective params
  let sR := bsmul (padBits (natToBits (natS bi)) params.kBits)
    ({ X := w.rx, Y := w.ry } : AffinePoint F).toProjective params
  addE (addE eG rQ params) sR params

def BoundGroupLF (pk : AffinePoint F) (e : F) (r s order : Nat)
    (params : CurveParameters F) : Prop :=
  ∃ w : EcdsaWitness F, CoreChecks w pk e order params ∧
    (LinearCombination w pk params).X = 0 ∧
    (LinearCombination w pk params).Z = 0 ∧
    natR (w.bi.map val3) = r ∧ order - natS (w.bi.map val3) = s

lemma valid_core (w : EcdsaWitness F) (pk : AffinePoint F) (e : F)
    (order : Nat) (params : CurveParameters F)
    (h : ValidEcdsaWitness w pk e order params) : CoreChecks w pk e order params := by
  rcases h with ⟨hlen, _, _, _, _, hbi, hpre, _, _, _, he, hr, hpk, hR, hri, hsi, hpki, hrlt, hslt⟩
  exact ⟨hlen, hbi, hpre, he, hr, hpk, hR, hri, hsi, hpki, hrlt, hslt⟩

/-- Projective equivalence preserves the exact final X=Z=0 test. -/
lemma projective_infinity_test_iff (P Q : ProjectivePoint F)
    (h : ProjectiveEquiv P Q) : (P.X = 0 ∧ P.Z = 0) ↔ (Q.X = 0 ∧ Q.Z = 0) := by
  rcases h with ⟨c, hc, rfl⟩
  change (c * Q.X = 0 ∧ c * Q.Z = 0) ↔ (Q.X = 0 ∧ Q.Z = 0)
  simp [hc]

lemma core_loop_group_iff (w : EcdsaWitness F) (pk : AffinePoint F) (e : F)
    (order : Nat) (params : CurveParameters F)
    [h_ell : (params.toMathlib).IsElliptic] [CurveHasNoPointsOfOrder2 params]
    (h_G_on : ProjectivePoint.IsOnCurve
      ({ X := params.gx, Y := params.gy } : AffinePoint F).toProjective params)
    (h : CoreChecks w pk e order params) :
    ((ecdsaPureLoopResult (w.bi.map val3) pk w.rx w.ry w.pre params).X = 0 ∧
     (ecdsaPureLoopResult (w.bi.map val3) pk w.rx w.ry w.pre params).Z = 0) ↔
    ((LinearCombination w pk params).X = 0 ∧ (LinearCombination w pk params).Z = 0) := by
  rcases h with ⟨hlen, hbi, hpre, _, _, h_on_pk, h_on_r, _⟩
  have h_pre_copy := hpre
  rcases hpre with ⟨h_pre_len, h_gpk_eq, h_gr_eq, h_rpk_eq, h_grpk_eq⟩
  have h_PK_proj_on : ProjectivePoint.IsOnCurve pk.toProjective params :=
    affine_to_projective_on_curve pk params h_on_pk
  have h_R_proj_on : ProjectivePoint.IsOnCurve
      ({ X := w.rx, Y := w.ry } : AffinePoint F).toProjective params :=
    affine_to_projective_on_curve _ params h_on_r
  -- Inline proofs for Z-coordinate exceptional bounds
  have h_GPK_on : ProjectivePoint.IsOnCurve (addE ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective pk.toProjective params) params :=
    addE_on_curve ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective pk.toProjective params h_G_on h_PK_proj_on
  have h_GPK_Z : (addE ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective pk.toProjective params).Z ≠ 0 :=
    z_ne_zero_of_point_equality_and_on_curve (addE ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective pk.toProjective params) (w.pre.getD 0 0) (w.pre.getD 1 0) params h_GPK_on h_gpk_eq

  have h_GR_on : ProjectivePoint.IsOnCurve (addE ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params) params :=
    addE_on_curve ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params h_R_proj_on h_G_on
  have h_GR_Z : (addE ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params).Z ≠ 0 :=
    z_ne_zero_of_point_equality_and_on_curve (addE ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params) (w.pre.getD 2 0) (w.pre.getD 3 0) params h_GR_on h_gr_eq

  have h_RPK_on : ProjectivePoint.IsOnCurve (addE ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective pk.toProjective params) params :=
    addE_on_curve ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective pk.toProjective params h_R_proj_on h_PK_proj_on
  have h_RPK_Z : (addE ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective pk.toProjective params).Z ≠ 0 :=
    z_ne_zero_of_point_equality_and_on_curve (addE ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective pk.toProjective params) (w.pre.getD 4 0) (w.pre.getD 5 0) params h_RPK_on h_rpk_eq

  have h_RPK_proj_on : ProjectivePoint.IsOnCurve ({ X := w.pre.getD 4 0, Y := w.pre.getD 5 0 : AffinePoint F }).toProjective params :=
    projective_point_on_curve_of_point_equality (addE ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective pk.toProjective params) (w.pre.getD 4 0) (w.pre.getD 5 0) params h_RPK_on h_RPK_Z h_rpk_eq
  have h_GRPK_on : ProjectivePoint.IsOnCurve (addE ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective ({ X := w.pre.getD 4 0, Y := w.pre.getD 5 0 : AffinePoint F }).toProjective params) params :=
    addE_on_curve ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective ({ X := w.pre.getD 4 0, Y := w.pre.getD 5 0 : AffinePoint F }).toProjective params h_G_on h_RPK_proj_on
  have h_GRPK_Z : (addE ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective { X := (addE ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective pk.toProjective params).X * (addE ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective pk.toProjective params).Z⁻¹, Y := (addE ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective pk.toProjective params).Y * (addE ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective pk.toProjective params).Z⁻¹, Z := 1 } params).Z ≠ 0 := by
    have h_pt_eq : { X := (addE ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective pk.toProjective params).X * (addE ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective pk.toProjective params).Z⁻¹, Y := (addE ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective pk.toProjective params).Y * (addE ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective pk.toProjective params).Z⁻¹, Z := 1 } =
                   ({ X := w.pre.getD 4 0, Y := w.pre.getD 5 0 : AffinePoint F }).toProjective := by
      ext
      · dsimp
        have hx := h_rpk_eq.1
        rw [hx]
        rw [mul_comm (addE ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective pk.toProjective params).Z, mul_assoc, mul_inv_cancel₀ h_RPK_Z, mul_one]
      · dsimp
        have hy := h_rpk_eq.2
        rw [hy]
        rw [mul_comm (addE ({ X := w.rx, Y := w.ry : AffinePoint F }).toProjective pk.toProjective params).Z, mul_assoc, mul_inv_cancel₀ h_RPK_Z, mul_one]
      · rfl
    rw [h_pt_eq]
    exact z_ne_zero_of_point_equality_and_on_curve (addE ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective ({ X := w.pre.getD 4 0, Y := w.pre.getD 5 0 : AffinePoint F }).toProjective params) (w.pre.getD 6 0) (w.pre.getD 7 0) params h_GRPK_on h_grpk_eq

  have h_natlen : (w.bi.map val3).length = params.kBits := by simpa using hlen
  have h_bounds := map_val3_bounds w.bi hbi
  have hcomb := loop_result_eq_linear_combination (w.bi.map val3) pk w.rx w.ry w.pre
    params h_natlen h_bounds h_pre_copy h_GPK_Z h_GR_Z h_RPK_Z h_GRPK_Z
    h_G_on.Y_ne_zero h_PK_proj_on.Y_ne_zero h_R_proj_on.Y_ne_zero
    h_G_on h_PK_proj_on h_R_proj_on
  exact projective_infinity_test_iff _ _ hcomb

lemma valid_pure_infinity (w : EcdsaWitness F) (pk : AffinePoint F) (e : F)
    (order : Nat) (params : CurveParameters F)
    (h : ValidEcdsaWitness w pk e order params) :
    (ecdsaPureLoopResult (w.bi.map val3) pk w.rx w.ry w.pre params).X = 0 ∧
    (ecdsaPureLoopResult (w.bi.map val3) pk w.rx w.ry w.pre params).Z = 0 := by
  rcases h with ⟨_, _, _, _, _, hbi, _, hloop, hx, hz, _⟩
  have hbounds := map_val3_bounds w.bi hbi
  have hcast := EcdsaLoopConstraintsF_cast_eq (w.bi.map val3) hbounds infinityPoint true
    w.int_x w.int_y w.int_z pk w.rx w.ry w.pre params
  rw [cast_val3_eq w.bi hbi] at hcast
  have hnat := hcast.mp hloop
  have hres := ecdsaLoopResultF_cast_eq (w.bi.map val3) hbounds infinityPoint true
    w.int_x w.int_y w.int_z pk w.rx w.ry w.pre params
  rw [cast_val3_eq w.bi hbi] at hres
  have hpure := ecdsaLoopResult_eq_ecdsaPureLoopResult infinityPoint true (w.bi.map val3)
    w.int_x w.int_y w.int_z pk w.rx w.ry w.pre params hnat
  have heq : ecdsaLoopResultF infinityPoint true w.bi w.int_x w.int_y w.int_z
      pk w.rx w.ry w.pre params =
      ecdsaPureLoopResult (w.bi.map val3) pk w.rx w.ry w.pre params :=
    hres.trans hpure
  rw [← heq]
  exact ⟨hx, hz⟩

lemma core_pure_construct (w : EcdsaWitness F) (pk : AffinePoint F) (e : F)
    (order : Nat) (params : CurveParameters F)
    (h : CoreChecks w pk e order params)
    (hinf : (ecdsaPureLoopResult (w.bi.map val3) pk w.rx w.ry w.pre params).X = 0 ∧
      (ecdsaPureLoopResult (w.bi.map val3) pk w.rx w.ry w.pre params).Z = 0) :
    ∃ w' : EcdsaWitness F, ValidEcdsaWitness w' pk e order params ∧ w'.bi = w.bi := by
  rcases h with ⟨hlen, hbi, hpre, he, hr, hpk, hR, hri, hsi, hpki, hrlt, hslt⟩
  have hbounds := map_val3_bounds w.bi hbi
  have h_natlen : (w.bi.map val3).length = params.kBits := by simpa using hlen
  obtain ⟨ix, iy, iz, hix, hiy, hiz, hloop⟩ :=
    exists_loop_witness (w.bi.map val3) pk w.rx w.ry w.pre params h_natlen
  have hcast := EcdsaLoopConstraintsF_cast_eq (w.bi.map val3) hbounds infinityPoint true
    ix iy iz pk w.rx w.ry w.pre params
  rw [cast_val3_eq w.bi hbi] at hcast
  have hloopF := hcast.mpr hloop
  have hres := ecdsaLoopResultF_cast_eq (w.bi.map val3) hbounds infinityPoint true
    ix iy iz pk w.rx w.ry w.pre params
  rw [cast_val3_eq w.bi hbi] at hres
  have hpure := ecdsaLoopResult_eq_ecdsaPureLoopResult infinityPoint true (w.bi.map val3)
    ix iy iz pk w.rx w.ry w.pre params hloop
  have heq : ecdsaLoopResultF infinityPoint true w.bi ix iy iz pk w.rx w.ry w.pre params =
      ecdsaPureLoopResult (w.bi.map val3) pk w.rx w.ry w.pre params :=
    hres.trans hpure
  have hfinal : (ecdsaLoopResultF infinityPoint true w.bi ix iy iz pk w.rx w.ry w.pre params).X = 0 ∧
      (ecdsaLoopResultF infinityPoint true w.bi ix iy iz pk w.rx w.ry w.pre params).Z = 0 := by
    rw [heq]
    exact hinf
  let w' : EcdsaWitness F := { w with int_x := ix, int_y := iy, int_z := iz }
  refine ⟨w', ?_, rfl⟩
  exact ⟨hlen, hix, hiy, hiz, hpre.1, hbi, hpre, hloopF,
    hfinal.1, hfinal.2, he, hr, hpk, hR, hri, hsi, hpki, hrlt, hslt⟩

/-- Exact equivalence to the original existential witness projection.  It fixes
both signature components and the supplied field digest, while removing the
specific intermediate-coordinate representation from the mathematical relation.
No subgroup-order assumption or canonical-digest assumption is introduced. -/
theorem boundLF_iff_group (pk : AffinePoint F) (e : F) (r s order : Nat)
    (params : CurveParameters F)
    [h_ell : (params.toMathlib).IsElliptic] [CurveHasNoPointsOfOrder2 params]
    (h_G_on : ProjectivePoint.IsOnCurve
      ({ X := params.gx, Y := params.gy } : AffinePoint F).toProjective params) :
    BoundLF pk e r s order params ↔ BoundGroupLF pk e r s order params := by
  constructor
  · rintro ⟨w, hw, hr, hs⟩
    have hc := valid_core w pk e order params hw
    have hg := (core_loop_group_iff w pk e order params h_G_on hc).mp
      (valid_pure_infinity w pk e order params hw)
    exact ⟨w, hc, hg.1, hg.2, hr, hs⟩
  · rintro ⟨w, hc, hx, hz, hr, hs⟩
    have hp := (core_loop_group_iff w pk e order params h_G_on hc).mpr ⟨hx, hz⟩
    obtain ⟨w', hw', hbi⟩ := core_pure_construct w pk e order params hc hp
    refine ⟨w', hw', ?_, ?_⟩
    · simpa [hbi] using hr
    · simpa [hbi] using hs

end RepresentationBridge

#print axioms RepresentationBridge.boundLF_iff_group
