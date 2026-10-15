/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentUnitPoints
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Coordinate algebra of a Laurent-valued morphism over its coefficient ring

Full faithfulness of Spec recovers an actual algebra homomorphism and its
invertible Laurent coordinate. Equality of this one unit detects morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentSchemeCoordinates
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (f : Spec (.of A) ⟶ Spec (.of R[T;T⁻¹]))
  (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])) =
    Spec.map (CommRingCat.ofHom (algebraMap R A)))

/-- The exact coefficient algebra map underlying the specified scheme morphism. -/
def algebraHom : R[T;T⁻¹] →ₐ[R] A where
  __ := (Spec.preimage f).hom
  commutes' r := by
    have he : CommRingCat.ofHom (algebraMap R R[T;T⁻¹]) ≫ Spec.preimage f =
        CommRingCat.ofHom (algebraMap R A) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, hf]
    exact congrArg (fun g : CommRingCat.of R ⟶ CommRingCat.of A ↦ g.hom r) he

/-- Passing back to spectra recovers the original morphism exactly. -/
theorem algebraHom_spec : Spec.map (CommRingCat.ofHom (algebraHom f hf).toRingHom) = f :=
  Spec.map_preimage f

/-- The actual invertible coordinate pulled back by the original morphism. -/
def coordinate : Aˣ := LaurentUnitPoints.pointUnit (algebraHom f hf)

/-- The coordinate evaluates back to the whole original coefficient algebra map. -/
theorem coordinate_eval : LaurentUnitPoints.evalUnit (coordinate f hf) = algebraHom f hf :=
  LaurentUnitPoints.evalUnit_pointUnit _

/-- One full unit, including its nilpotent terms, determines the original scheme morphism. -/
theorem ext (g : Spec (.of A) ⟶ Spec (.of R[T;T⁻¹]))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (he : coordinate f hf = coordinate g hg) : f = g := by
  rw [← algebraHom_spec f hf, ← algebraHom_spec g hg]
  congr 2
  have ha := congrArg (LaurentUnitPoints.evalUnit (R := R)) he
  rw [coordinate_eval, coordinate_eval] at ha
  exact congrArg AlgHom.toRingHom ha

end FLT.Mazur.LaurentSchemeCoordinates
