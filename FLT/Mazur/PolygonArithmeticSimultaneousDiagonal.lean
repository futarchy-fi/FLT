/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousIterationStability

/-!
# A diagonal simultaneous state with correction count depending on arithmetic order

At quotient m use m further measured corrections. Finite stabilization makes
these different correction counts compatible with the original quotients.
Every resulting edge is normalized at its own arithmetic layer.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticSimultaneous
open PolygonArithmeticStages
variable {R : Type*} [CommRing R] {π : R}
  (B : (m : ℕ) → (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])
  (hB : CompatibleEquiv B) (hb : ReciprocalBase B)
  (S : State R π) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized B r₀)
local notation "I" => S.iterate B hB hb hS ha r₀ hr₀

/-- Choose the finite measured correction count m on arithmetic quotient m. -/
def State.diagonal : State R π where
  initial m := (I m).initial m
  last m := (I m).last m
  terminal m := (I m).terminal m
  initialEquiv m := (I m).initialEquiv m
  closingEquiv m := (I m).closingEquiv m

local notation "D" => S.diagonal B hB hb hS ha r₀ hr₀

/-- The diagonal retains the exact original adjacent arithmetic quotient maps. -/
theorem State.diagonal_compatible : (D).Compatible := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m b
    change restriction R π m ((I (m + 1)).initial (m + 1) b) = (I m).initial m b
    rw [(S.iterate_compatible B hB hb hS ha r₀ hr₀ (m + 1)).1 m b]
    exact S.iterate_initial_stable B hB hb hS ha r₀ hr₀ (by omega) (by omega) b
  · intro m b
    change restriction R π m ((I (m + 1)).last (m + 1) b) = (I m).last m b
    rw [(S.iterate_compatible B hB hb hS ha r₀ hr₀ (m + 1)).2.1 m b]
    exact S.iterate_last_stable B hB hb hS ha r₀ hr₀ (by omega) (by omega) b
  · intro m
    change restriction R π m ((I (m + 1)).terminal (m + 1)) = (I m).terminal m
    rw [(S.iterate_compatible B hB hb hS ha r₀ hr₀ (m + 1)).2.2.1 m]
    exact S.iterate_terminal_stable B hB hb hS ha r₀ hr₀ (by omega) (by omega)
  · intro b m
    change _ = ((I m).initialEquiv m b).toRingHom.comp _
    rw [← S.iterate_initialEquiv_stable B hB hb hS ha r₀ hr₀
      (Nat.le_succ m) (by omega) b]
    exact (S.iterate_compatible B hB hb hS ha r₀ hr₀ (m + 1)).2.2.2.1 b m
  · intro b m
    change _ = ((I m).closingEquiv m b).toRingHom.comp _
    rw [← S.iterate_closingEquiv_stable B hB hb hS ha r₀ hr₀
      (Nat.le_succ m) (by omega) b]
    exact (S.iterate_compatible B hB hb hS ha r₀ hr₀ (m + 1)).2.2.2.2 b m

/-- The original annihilators hold for the diagonal's actual accumulated smoothings. -/
theorem State.diagonal_annihilated : (D).Annihilated :=
  ⟨fun m b ↦ (S.iterate_annihilated B hB hb hS ha r₀ hr₀ m).1 m b,
    (fun m b ↦ (S.iterate_annihilated B hB hb hS ha r₀ hr₀ m).2.1 m b),
    fun m ↦ (S.iterate_annihilated B hB hb hS ha r₀ hr₀ m).2.2 m⟩

/-- Both complete diagonal edges are normalized at every arithmetic order. -/
theorem State.diagonal_normalized (m : ℕ) : (D).Normalized B m :=
  S.iterate_normalized_le B hB hb hS ha r₀ hr₀ m m (by omega)

end FLT.Mazur.PolygonArithmeticSimultaneous
