import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
Local group identities and the finite-exception existence lemma for the
alternating-offset ELM design. These results are generic and kernel checked.
They do not instantiate the candidate-offset injection conditions on P-256,
nor prove the full circuit's soundness/completeness.
-/
namespace RepresentationBridge.OffsetExistence

section ElmOffsetAlgebra
variable {A : Type} [AddCommGroup A]

-- q denotes the signed offset cH, so the sign can alternate freely.
theorem elm_offset_step_invariant (c q t : A) :
    2 • (c + q) + (t - 3 • q) = (2 • c + t) - q := by abel

theorem elm_first_same_collision (c q t : A) :
    c + q = t - 3 • q ↔ 4 • q = t - c := by
  constructor
  · intro heq
    calc
      4 • q = (t - c) + ((c + q) - (t - 3 • q)) := by abel
      _ = t - c := by rw [heq, sub_self, add_zero]
  · intro heq
    calc
      c + q = (t - 3 • q) + (4 • q - (t - c)) := by abel
      _ = t - 3 • q := by rw [heq, sub_self, add_zero]

theorem elm_first_opposite_collision (c q t : A) :
    c + q = -(t - 3 • q) ↔ 2 • q = c + t := by
  constructor
  · intro heq
    calc
      2 • q = (c + t) + (-(t - 3 • q) - (c + q)) := by abel
      _ = c + t := by rw [heq, sub_self, add_zero]
  · intro heq
    calc
      c + q = -(t - 3 • q) + ((c + t) - 2 • q) := by abel
      _ = -(t - 3 • q) := by rw [heq, sub_self, add_zero]

theorem elm_second_same_collision (a b : A) :
    a + b = a ↔ b = 0 := by simp

theorem elm_second_opposite_collision (a b : A) :
    a + b = -a ↔ 2 • a + b = 0 := by
  constructor
  · intro heq
    calc
      2 • a + b = a + (a + b) := by abel
      _ = 0 := by rw [heq]; simp
  · intro heq
    calc
      a + b = -a + (2 • a + b) := by abel
      _ = -a := by rw [heq, add_zero]

end ElmOffsetAlgebra

/-- Each injective equation f_i(c)=target_i can exclude at most one candidate.
For the alternating ELM + 128-window fixed-base plan use m=1039 and at least
1040 candidates; maps f_i are multiplication by ±1, ±2, ±3 or ±4.
The theorem does not claim these maps have yet been instantiated for P-256. -/
theorem exists_avoiding_injective_equations
    {C A : Type} [Fintype C] {m : Nat}
    (f : Fin m → C → A) (hf : ∀ i, Function.Injective (f i))
    (target : Fin m → A) (hcard : m < Fintype.card C) :
    ∃ c, ∀ i, f i c ≠ target i := by
  classical
  let bad (i : Fin m) : Finset C := Finset.univ.filter (fun c => f i c = target i)
  have hi : ∀ i, (bad i).card ≤ 1 := by
    intro i
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact hf i ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  have hb : (Finset.univ.biUnion bad).card ≤ m := by
    calc
      _ ≤ ∑ i : Fin m, (bad i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin m, 1 := Finset.sum_le_sum (fun i _ => hi i)
      _ = m := by simp
  have hex : ∃ c, c ∉ Finset.univ.biUnion bad := by
    by_contra hh
    push Not at hh
    have heq : Finset.univ.biUnion bad = Finset.univ := Finset.eq_univ_of_forall hh
    rw [heq, Finset.card_univ] at hb
    omega
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, ?_⟩
  intro i heq
  apply hc
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩⟩

end RepresentationBridge.OffsetExistence

#print axioms RepresentationBridge.OffsetExistence.elm_offset_step_invariant
#print axioms RepresentationBridge.OffsetExistence.elm_first_same_collision
#print axioms RepresentationBridge.OffsetExistence.elm_first_opposite_collision
#print axioms RepresentationBridge.OffsetExistence.elm_second_same_collision
#print axioms RepresentationBridge.OffsetExistence.elm_second_opposite_collision
#print axioms RepresentationBridge.OffsetExistence.exists_avoiding_injective_equations
