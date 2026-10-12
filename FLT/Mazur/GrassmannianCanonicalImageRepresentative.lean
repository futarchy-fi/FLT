/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianClassifiedImageQuotient

/-!
# A fixed canonical-cover representative of the actual image quotient

The canonical affine cover supplies its original coefficient algebras and all
relations. Packaging this image before specialization keeps its projection intact.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
open GrassmannianOpenChartDescent
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
variable {X : Scheme.{u}} (f : X ⟶ ambientGrassmannianScheme R M κ d)

/-- The actual full image quotient constructed on the fixed canonical affine source cover. -/
@[irreducible] def canonicalImageRepresentative :
    LocallyFreeSheafQuotient (M := M) (f ≫ ambientGrassmannianStructure R M κ d) d :=
  @quotientImageRepresentative R M ι κ _ _ _ _ _ d b hκ X f X.affineOpenCover
    (fun j ↦ schemeChartAlgebra f j) (schemeChartPoint f) (fun _ ↦ rfl)

/-- This fixed-cover original quotient retains the original classifying scheme morphism. -/
theorem canonicalImageRepresentative_classifies :
    SheafQuotientClassifies (f ≫ ambientGrassmannianStructure R M κ d)
      (canonicalImageRepresentative b hκ f).projection b hκ f := by
  unfold canonicalImageRepresentative
  exact @quotientImageRepresentative_classifies R M ι κ _ _ _ _ _ d b hκ X f
    X.affineOpenCover (fun j ↦ schemeChartAlgebra f j) (schemeChartPoint f) (fun _ ↦ rfl)

/-- Retain the original base map when forming the actual fixed-cover quotient. -/
def imageRepresentativeOver (β : X ⟶ Spec (.of R))
    (hf : f ≫ ambientGrassmannianStructure R M κ d = β) :
    LocallyFreeSheafQuotient (M := M) β d :=
  hf ▸ canonicalImageRepresentative b hκ f

/-- Transport of the original base equality preserves the full classification atlas. -/
theorem imageRepresentativeOver_classifies (β : X ⟶ Spec (.of R))
    (hf : f ≫ ambientGrassmannianStructure R M κ d = β) :
    SheafQuotientClassifies β (imageRepresentativeOver b hκ f β hf).projection b hκ f := by
  subst β
  exact canonicalImageRepresentative_classifies b hκ f

end FLT.Mazur.GrassmannianChart
