/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientImageAmbientEpi
public import FLT.Mazur.GrassmannianQuotientImageLocalFree

/-!
# The actual global quotient for an arbitrary Grassmannian morphism

The canonical affine cover supplies a global epimorphism from the original
ambient sheaf to the descended locally finite free quotient.
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

/-- The original ambient sheaf maps to the full quotient for any source scheme. -/
@[irreducible] def grassmannianSchemeImageAmbientMap :
    grassmannianSchemeAmbient (M := M) (f ≫ ambientGrassmannianStructure R M κ d) ⟶
      grassmannianSchemeImageQuotient f b hκ := by
  delta grassmannianSchemeImageQuotient
  exact @GrassmannianOpenChartDescent.quotientImageAmbientMap R M ι κ _ _ _ _ _ d b hκ X f
    X.affineOpenCover.I₀ (fun j ↦ X.affineOpenCover.X j)
    (fun _ ↦ inferInstance) (fun j ↦ schemeChartAlgebra f j)
    X.affineOpenCover.f (fun _ ↦ inferInstance) (schemeChartPoint f) (fun _ ↦ rfl)

/-- The constructed arbitrary-scheme ambient quotient map is epi. -/
instance grassmannianSchemeImageAmbientMap_epi :
    Epi (grassmannianSchemeImageAmbientMap f b hκ) := by
  delta grassmannianSchemeImageAmbientMap grassmannianSchemeImageQuotient
  dsimp only [id]
  exact @GrassmannianOpenChartDescent.quotientImageAmbientMap_epi R M ι κ _ _ _ _ _ d b hκ X f
    X.affineOpenCover.I₀ (fun j ↦ X.affineOpenCover.X j)
    (fun _ ↦ inferInstance) (fun j ↦ schemeChartAlgebra f j)
    X.affineOpenCover.f (fun _ ↦ inferInstance) (schemeChartPoint f) (fun _ ↦ rfl)
    X.affineOpenCover.openCover.iSup_opensRange

end FLT.Mazur.GrassmannianChart
