/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientImageDescent
public import FLT.Mazur.GrassmannianSchemeChartPoint

/-!
# Original quotient sheaves for arbitrary Grassmannian morphisms

The canonical affine cover gives each coefficient ring its original base algebra.
Every chart retains the full original Grassmannian morphism and base map.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable {X : Scheme.{u}} (f : X ⟶ ambientGrassmannianScheme R M κ d)

variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)

/-- The original quotients on the canonical affine cover form one sheaf on the source. -/
@[irreducible] def grassmannianSchemeImageQuotient : X.Modules :=
  @GrassmannianOpenChartDescent.quotientImageSheaf R M ι κ _ _ _ _ _ d b hκ X f
    X.affineOpenCover.I₀ (fun j ↦ X.affineOpenCover.X j)
    (fun _ ↦ inferInstance) (fun j ↦ schemeChartAlgebra f j)
    X.affineOpenCover.f (fun _ ↦ inferInstance) (schemeChartPoint f) (fun _ ↦ rfl)

/-- The descended sheaf recovers the original quotient on each canonical affine chart. -/
@[irreducible] def grassmannianSchemeImageQuotientChartIso (j : X.affineOpenCover.I₀) :
    let _ := schemeChartAlgebra f j
    (pullback (X.affineOpenCover.f j)).obj (grassmannianSchemeImageQuotient f b hκ) ≅
      grassmannianQuotientSheaf (A := X.affineOpenCover.X j)
        (ambientMorphismPoint (A := X.affineOpenCover.X j)
          (schemeChartPoint f j).val (schemeChartPoint f j).property) := by
  let _ := schemeChartAlgebra f j
  delta grassmannianSchemeImageQuotient
  exact @GrassmannianOpenChartDescent.quotientImageSheafChartIso R M ι κ _ _ _ _ _ d
    b hκ X f X.affineOpenCover.I₀ (fun j ↦ X.affineOpenCover.X j)
    (fun _ ↦ inferInstance) (fun j ↦ schemeChartAlgebra f j)
    X.affineOpenCover.f (fun _ ↦ inferInstance) (schemeChartPoint f) (fun _ ↦ rfl) j

end FLT.Mazur.GrassmannianChart
