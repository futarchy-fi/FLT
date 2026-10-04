/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Unramified.Finite

/-! # Descending flatness through a surjective coefficient map -/

@[expose] public noncomputable section
namespace RingHom.Flat
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- Flatness of a composite descends across a surjective map on coefficients. -/
theorem of_comp_surjective (q : A →+* B) (g : B →+* C)
    (hq : Function.Surjective q) (h : (g.comp q).Flat) : g.Flat := by
  let : Algebra A B := q.toAlgebra
  let : Algebra B C := g.toAlgebra
  let : Algebra A C := (g.comp q).toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId A B) hq
  let : Algebra.FiniteType A B := Algebra.FiniteType.of_surjective (Algebra.ofId A B) hq
  let : Module.Flat A C := h
  exact Algebra.FormallyUnramified.flat_of_restrictScalars A B C
end RingHom.Flat
