/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSheafQuotientClasses
public import FLT.Mazur.GrassmannianQuotientImageClassification

/-!
# Actual quotient representatives of arbitrary scheme morphisms

The entire descended quotient on any supplied affine cover gives a locally
free quotient representative. Its original scheme morphism classifies it.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianOpenChartDescent
open GrassmannianChart
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
variable {X : Scheme.{u}} (f : X ⟶ ambientGrassmannianScheme R M κ d)
variable (C : X.AffineOpenCover.{u}) [∀ j, Algebra R (C.X j)]
  (a : ∀ j, {a : Spec (C.X j) ⟶ ambientGrassmannianScheme R M κ d //
    a ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R (C.X j)})
  (h : ∀ j, C.f j ≫ f = (a j).val)

/-- The actual descended quotient, its full epimorphism, and its constructed fixed-rank frames. -/
@[irreducible] def quotientImageRepresentative :
    LocallyFreeSheafQuotient (M := M) (f ≫ ambientGrassmannianStructure R M κ d) d where
  sheaf := quotientImageSheaf b hκ f (fun j ↦ C.X j) C.f a h
  projection := quotientImageAmbientMap b hκ f (fun j ↦ C.X j) C.f a h
  epi := quotientImageAmbientMap_epi b hκ f (fun j ↦ C.X j) C.f a h
    C.openCover.iSup_opensRange
  frames := quotientImageSheaf_fixedFrames b hκ f (fun j ↦ C.X j) C.f a h
    C.openCover.iSup_opensRange

/-- This actual representative retains the original morphism and every local projection. -/
theorem quotientImageRepresentative_classifies :
    SheafQuotientClassifies (f ≫ ambientGrassmannianStructure R M κ d)
      (quotientImageRepresentative b hκ f C a h).projection b hκ f := by
  unfold quotientImageRepresentative
  exact quotientImage_classifies b hκ f C a h

include C a h in
/-- Every supplied source cover constructs an actual quotient classified by its scheme map. -/
theorem exists_quotientImageRepresentative :
    ∃ P : LocallyFreeSheafQuotient (M := M) (f ≫ ambientGrassmannianStructure R M κ d) d,
      SheafQuotientClassifies (f ≫ ambientGrassmannianStructure R M κ d)
        P.projection b hκ f :=
  ⟨quotientImageRepresentative b hκ f C a h,
    quotientImageRepresentative_classifies b hκ f C a h⟩

end FLT.Mazur.GrassmannianOpenChartDescent
