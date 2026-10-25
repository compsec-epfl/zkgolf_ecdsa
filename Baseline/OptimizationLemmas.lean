import Baseline.Optimized

/-! Algebraic identities used by the optimized lowering. These do not constitute
an end-to-end soundness/completeness proof for the circuit. -/
namespace Optimized

/-- Exact coordinates, including the scaling: no curve assumption is needed. -/
theorem add_infinity_exact {K : Type} [Field K] (x y z : K)
    (params : CurveParameters K) :
    _root_.addE (infinityPoint : ProjectivePoint K)
      ({ X := x, Y := y, Z := z } : ProjectivePoint K) params =
      ({ X := x * y, Y := y * y, Z := y * z } : ProjectivePoint K) := by
  ext <;> simp [addE, infinityPoint] <;> ring

/-- A quotient constraint implements exactly the required zero implication. -/
theorem quotient_gate {K : Type} [Field K] (missing sum : K) :
    (∃ q, missing * q = sum) ↔ (missing = 0 → sum = 0) := by
  constructor
  · rintro ⟨q, h⟩ hm
    simpa [hm] using h.symm
  · intro h
    by_cases hm : missing = 0
    · exact ⟨0, by simp [h hm]⟩
    · exact ⟨sum / missing, by field_simp⟩

/-- Bit-level meaning of the comparator: deactivate at a missing bound-one;
reject an input-one at a bound-zero only while still active. -/
def gatedBits : Bool → List (Bool × Bool) → Prop
  | _, [] => True
  | active, (a, true) :: xs => gatedBits (active && a) xs
  | active, (a, false) :: xs => (active = true → a = false) ∧ gatedBits active xs

def lexLE : List (Bool × Bool) → Prop
  | [] => True
  | (false, true) :: _ => True
  | (true, false) :: _ => False
  | _ :: xs => lexLE xs

/-- The gated-bit strategy is exactly unsigned lexicographic ≤, including equality. -/
theorem gatedBits_correct (xs : List (Bool × Bool)) (active : Bool) :
    gatedBits active xs ↔ active = false ∨ lexLE xs := by
  induction xs generalizing active with
  | nil => simp [gatedBits, lexLE]
  | cons ab xs ih =>
    rcases ab with ⟨a, b⟩
    cases a <;> cases b <;> cases active <;> simp [gatedBits, lexLE, ih]

end Optimized
