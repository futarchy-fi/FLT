/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Finite geometric sections force finite schemes

For a finite type scheme over an algebraically closed field, its field-valued
sections are its closed points. Finitely many such sections force a discrete,
finite underlying space, and hence a finite structure map. Nilpotents are allowed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteGeometricSections

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

/-- Finite geometric sections force finiteness of all points, not only the closed ones. -/
theorem finite_carrier [Finite {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _}] : Finite X := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : Finite (closedPoints X) := Finite.of_equiv _ (pointEquivClosedPoint f)
  have : DiscreteTopology X := JacobsonSpace.discreteTopology (Set.toFinite _)
  exact Set.finite_univ_iff.mp ((closedPoints_eq_univ (X := X)) ▸ Set.toFinite (closedPoints X))

/-- A finite type scheme with finite geometric sections has a finite structure morphism. -/
theorem isFinite [QuasiCompact f]
    [Finite {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _}] : IsFinite f := by
  have := finite_carrier f
  have : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_finite_preimage_singleton f fun _ ↦ Set.toFinite _
  exact IsFinite.of_locallyQuasiFinite f

end FLT.Mazur.FiniteGeometricSections
