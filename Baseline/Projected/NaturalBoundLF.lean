import Baseline.Projected.BoundLF

namespace RepresentationBridge
variable {F : Type} [Field F] [NeZero (2 : F)] [NeZero (3 : F)]
  [NeZero (4 : F)] [NeZero (5 : F)] [NeZero (6 : F)] [NeZero (7 : F)]

lemma natReconstruct_lt_pow (bi : List Nat) (mux : Nat → Nat) (hmux : ∀ v, mux v < 2) :
    natReconstruct bi mux < 2 ^ bi.length := by
  induction bi with
  | nil => simp [natReconstruct]
  | cons v vs ih =>
    rw [natReconstruct_cons, List.length_cons, Nat.pow_succ]
    have hm : mux v = 0 ∨ mux v = 1 := by have := hmux v; omega
    rcases hm with hm | hm <;> simp only [hm, zero_mul, zero_add, one_mul] <;> omega

def ScalarCombination (pk : AffinePoint F) (E r t : Nat) (ry : F)
    (params : CurveParameters F) : ProjectivePoint F :=
  let eG := bsmul (padBits (natToBits E) params.kBits)
    ({ X := params.gx, Y := params.gy } : AffinePoint F).toProjective params
  let rQ := bsmul (padBits (natToBits r) params.kBits) pk.toProjective params
  let tR := bsmul (padBits (natToBits t) params.kBits)
    ({ X := (r : F), Y := ry } : AffinePoint F).toProjective params
  addE (addE eG rQ params) tR params

/-- The same acceptance relation with natural scalars and arbitrary internal
representation. E is a 256-bit lift of the supplied field digest, not necessarily
its canonical representative. The precomputation table remains existential: its
existence expresses precisely the original four finite-sum restrictions. -/
def NaturalBoundLF (pk : AffinePoint F) (e : F) (r s order : Nat)
    (params : CurveParameters F) : Prop :=
  ∃ (E t : Nat) (ry : F) (pre : List F),
    E < 2^params.kBits ∧ (E : F) = e ∧
    r < order ∧ t < order ∧ order - t = s ∧
    pk.IsOnCurve params ∧ AffinePoint.IsOnCurve { X := (r : F), Y := ry } params ∧
    (r : F) ≠ 0 ∧ (t : F) ≠ 0 ∧ pk.X ≠ 0 ∧
    ValidPreComputationExact pk (r : F) ry pre params ∧
    (ScalarCombination pk E r t ry params).X = 0 ∧
    (ScalarCombination pk E r t ry params).Z = 0

lemma boundGroup_iff_natural (pk : AffinePoint F) (e : F) (r s order : Nat)
    (params : CurveParameters F) (horder : order < 2^params.kBits) :
    BoundGroupLF pk e r s order params ↔ NaturalBoundLF pk e r s order params := by
  constructor
  · rintro ⟨w, hc, hx, hz, hr, hs⟩
    rcases hc with ⟨hlen, hbi, hpre, he, hrecR, hpk, hR, hri, hsi, hpki, hrlt, htlt⟩
    have hrx : w.rx = (r : F) := by
      rw [reconstructR_eq_natR, hr] at hrecR
      exact hrecR.symm
    have he_nat : (natE (w.bi.map val3) : F) = e := by
      rwa [reconstructE_eq_natE] at he
    have hri_ne : (r : F) ≠ 0 := by
      rw [hrx] at hri
      exact left_ne_zero_of_mul_eq_one hri
    have hti_ne : (natS (w.bi.map val3) : F) ≠ 0 := by
      rw [reconstructS_eq_natS] at hsi
      exact left_ne_zero_of_mul_eq_one hsi
    have hpki_ne : pk.X ≠ 0 := left_ne_zero_of_mul_eq_one hpki
    have hE_bound : natE (w.bi.map val3) < 2^params.kBits := by
      have hb := natReconstruct_lt_pow (w.bi.map val3) muxE (fun v => Nat.mod_lt v (by decide))
      simpa only [natE, List.length_map, hlen] using hb
    have hcomb : LinearCombination w pk params =
        ScalarCombination pk (natE (w.bi.map val3)) r (natS (w.bi.map val3)) w.ry params := by
      simp only [LinearCombination, ScalarCombination, hr, hrx]
    refine ⟨natE (w.bi.map val3), natS (w.bi.map val3), w.ry, w.pre,
      hE_bound, he_nat, ?_, htlt, hs, hpk, ?_, hri_ne, hti_ne, hpki_ne, ?_, ?_, ?_⟩
    · simpa [hr] using hrlt
    · simpa [hrx] using hR
    · simpa [hrx] using hpre
    · simpa [hcomb] using hx
    · simpa [hcomb] using hz
  · rintro ⟨E, t, ry, pre, hE, he, hr, ht, hs, hpk, hR, hrnz, htnz, hpkz, hpre, hx, hz⟩
    obtain ⟨bi, hlen, hbi, heq, hrq, htq⟩ := exists_bi E r t hE (hr.trans horder) (ht.trans horder)
    let w : EcdsaWitness F := {
      rx := (r : F), ry := ry, pre := pre, rx_inv := (r : F)⁻¹,
      s_inv := (t : F)⁻¹, pk_inv := pk.X⁻¹,
      bi := bi.map (fun (x : Nat) => (x : F)), int_x := [], int_y := [], int_z := [] }
    have hwbi : w.bi.map val3 = bi := map_val3_cast_eq bi hbi
    have hc : CoreChecks w pk e order params := by
      refine ⟨?_, ?_, hpre, ?_, ?_, hpk, hR, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [w] using hlen
      · exact map_cast_bounds bi hbi
      · rw [hwbi, reconstructE_eq_natE, heq]
        exact he
      · rw [hwbi, reconstructR_eq_natR, hrq]
      · exact mul_inv_cancel₀ hrnz
      · rw [hwbi, reconstructS_eq_natS, htq]
        exact mul_inv_cancel₀ htnz
      · exact mul_inv_cancel₀ hpkz
      · rw [hwbi, hrq]
        exact hr
      · rw [hwbi, htq]
        exact ht
    have hcomb : LinearCombination w pk params = ScalarCombination pk E r t ry params := by
      simp only [LinearCombination, hwbi, heq, hrq, htq, ScalarCombination, w]
    refine ⟨w, hc, ?_, ?_, ?_, ?_⟩
    · simpa [hcomb] using hx
    · simpa [hcomb] using hz
    · rw [hwbi, hrq]
    · rw [hwbi, htq]
      exact hs

theorem boundLF_iff_natural (pk : AffinePoint F) (e : F) (r s order : Nat)
    (params : CurveParameters F)
    [h_ell : (params.toMathlib).IsElliptic] [CurveHasNoPointsOfOrder2 params]
    (h_G_on : ProjectivePoint.IsOnCurve
      ({ X := params.gx, Y := params.gy } : AffinePoint F).toProjective params)
    (horder : order < 2^params.kBits) :
    BoundLF pk e r s order params ↔ NaturalBoundLF pk e r s order params :=
  (boundLF_iff_group pk e r s order params h_G_on).trans
    (boundGroup_iff_natural pk e r s order params horder)

end RepresentationBridge
#print axioms RepresentationBridge.boundLF_iff_natural
