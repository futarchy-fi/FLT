/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainIterationStability

/-!
# A diagonal retained-chain state at every arithmetic order

At quotient m use m further measured corrections. Finite stabilization makes
these different correction counts compatible with the original quotients.
Every resulting edge is normalized at its own arithmetic layer.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticRetainedChain
open PolygonArithmeticStages PolygonArithmeticSimultaneous
variable {R : Type*} [CommRing R] {π : R} {n : ℕ}
  (B : (m : ℕ) → (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])
  (hB : CompatibleEquiv B) (hb : ReciprocalBase B)
  (S : State R π n) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized B r₀)
local notation "I" => S.iterate B hB hb hS ha r₀ hr₀

/-- Choose the finite measured correction count m on arithmetic quotient m. -/
def State.diagonal : State R π n where
  initial m := (I m).initial m
  retained m := (I m).retained m
  terminal m := (I m).terminal m
  edgeEquiv e m := (I m).edgeEquiv e m

local notation "D" => S.diagonal B hB hb hS ha r₀ hr₀

/-- The diagonal retains the exact original adjacent arithmetic quotient maps. -/
theorem State.diagonal_compatible : (D).Compatible := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m b
    change restriction R π m ((I (m + 1)).initial (m + 1) b) = (I m).initial m b
    rw [(S.iterate_compatible B hB hb hS ha r₀ hr₀ (m + 1)).1 m b]
    exact S.iterate_initial_stable B hB hb hS ha r₀ hr₀ (by omega) (by omega) b
  · intro m i b
    change restriction R π m ((I (m + 1)).retained (m + 1) i b) = (I m).retained m i b
    rw [(S.iterate_compatible B hB hb hS ha r₀ hr₀ (m + 1)).2.1 m i b]
    exact S.iterate_retained_stable B hB hb hS ha r₀ hr₀ (by omega) (by omega) i b
  · intro m
    change restriction R π m ((I (m + 1)).terminal (m + 1)) = (I m).terminal m
    rw [(S.iterate_compatible B hB hb hS ha r₀ hr₀ (m + 1)).2.2.1 m]
    exact S.iterate_terminal_stable B hB hb hS ha r₀ hr₀ (by omega) (by omega)
  · intro e b m
    change _ = ((I m).edgeEquiv e m b).toRingHom.comp _
    rw [← S.iterate_edgeEquiv_stable B hB hb hS ha r₀ hr₀
      (Nat.le_succ m) (by omega) e b]
    exact (S.iterate_compatible B hB hb hS ha r₀ hr₀ (m + 1)).2.2.2 e b m

/-- The original annihilators hold for the diagonal's actual accumulated smoothings. -/
theorem State.diagonal_annihilated : (D).Annihilated :=
  ⟨fun m b ↦ (S.iterate_annihilated B hB hb hS ha r₀ hr₀ m).1 m b,
    (fun m i b ↦ (S.iterate_annihilated B hB hb hS ha r₀ hr₀ m).2.1 m i b),
    fun m ↦ (S.iterate_annihilated B hB hb hS ha r₀ hr₀ m).2.2 m⟩

/-- All complete diagonal edges are normalized at every arithmetic order. -/
theorem State.diagonal_normalized (m : ℕ) : (D).Normalized B m :=
  S.iterate_normalized_le B hB hb hS ha r₀ hr₀ m m (by omega)

end FLT.Mazur.PolygonArithmeticRetainedChain
