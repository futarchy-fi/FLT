/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianOpenChartComparisons

/-!
# Canonical affine coordinates of arbitrary Grassmannian morphisms

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

/-- The coefficient algebra of an actual canonical affine chart of the source. -/
abbrev schemeChartAlgebra (j : X.affineOpenCover.I₀) : Algebra R (X.affineOpenCover.X j) :=
  (Spec.preimage (X.affineOpenCover.f j ≫ f ≫
    ambientGrassmannianStructure R M κ d)).hom.toAlgebra

/-- The canonical affine chart retains the original Grassmannian morphism and its base map. -/
def schemeChartPoint (j : X.affineOpenCover.I₀) :
    let _ := schemeChartAlgebra f j
    {a : Spec (X.affineOpenCover.X j) ⟶ ambientGrassmannianScheme R M κ d //
      a ≫ ambientGrassmannianStructure R M κ d =
        Spec.algebraMap R (X.affineOpenCover.X j)} := by
  let _ := schemeChartAlgebra f j
  refine ⟨X.affineOpenCover.f j ≫ f, ?_⟩
  change (X.affineOpenCover.f j ≫ f) ≫ ambientGrassmannianStructure R M κ d =
    Spec.map (Spec.preimage (X.affineOpenCover.f j ≫ f ≫
      ambientGrassmannianStructure R M κ d))
  rw [Spec.map_preimage, Category.assoc]

end FLT.Mazur.GrassmannianChart
