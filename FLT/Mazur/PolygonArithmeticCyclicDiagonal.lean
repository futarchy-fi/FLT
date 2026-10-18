/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCyclicStability

/-!
# A compatible cyclic state with every edge standard at every order

Use m measured corrections at arithmetic order m. Stabilization proves that
the varying correction counts keep the original coefficient quotient maps.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonArithmeticCyclic
open PolygonArithmeticStages
variable {R : Type*} [CommRing R] {π : R} {ι : Type*}
  (σ : Equiv.Perm ι) (S : State R π ι) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized r₀)
local notation "I" => S.iterate σ hS ha r₀ hr₀

/-- Choose the attained finite correction separately at each arithmetic order. -/
def State.diagonal : State R π ι where
  parameter m := (I m).parameter m
  edge m := (I m).edge m

local notation "D" => S.diagonal σ hS ha r₀ hr₀

/-- All full diagonal parameters and edges respect the original quotient homomorphisms. -/
theorem State.diagonal_compatible : (D).Compatible := by
  constructor
  · intro m i
    change restriction R π m ((I (m + 1)).parameter (m + 1) i) = (I m).parameter m i
    rw [(S.iterate_compatible σ hS ha r₀ hr₀ (m + 1)).1 m i]
    exact S.iterate_parameter_stable σ hS ha r₀ hr₀ (by omega) (by omega) i
  · intro i m
    change _ = ((I m).edge m i).toRingHom.comp _
    rw [← S.iterate_edge_stable σ hS ha r₀ hr₀ (Nat.le_succ m) (by omega) i]
    exact (S.iterate_compatible σ hS ha r₀ hr₀ (m + 1)).2 i m

/-- All diagonal smoothings retain the original top-power annihilators. -/
theorem State.diagonal_annihilated : (D).Annihilated :=
  fun m i ↦ S.iterate_annihilated σ hS ha r₀ hr₀ m m i

/-- Every full edge of the diagonal cycle is standard inversion at every order. -/
theorem State.diagonal_normalized (m : ℕ) : (D).Normalized m :=
  S.iterate_normalized_le σ hS ha r₀ hr₀ m m (by omega)

end FLT.Mazur.PolygonArithmeticCyclic
