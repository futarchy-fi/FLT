/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianDeterminantOpenUnits
public import FLT.Mazur.StructureModuleScalarTransitions
public import FLT.Mazur.ModuleSheafGeometricOpenGluing
public import FLT.Mazur.ModuleLineBundleOpenCover

/-!
# Geometric transitions for the Grassmannian determinant line

On every common chart open the inverse determinant gives an actual line-sheaf
isomorphism. These isomorphisms satisfy refinement and cocycle laws. Packaging
and gluing the global line is a separate construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
open ModuleSheafOpenImageChart ModuleSheafGluing StructureModuleScalarTransitions FCurve
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R M ι : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] {d : ℕ}
local notation "chart" => ambientGrassmannianChart R M ι d

attribute [local irreducible] Scheme.Modules.pullback coordinateIso determinantOpenUnit

/-- The sealed actual determinant comparison on each common subopen. -/
@[irreducible] def determinantLineOverlapIso (i j : AmbientChartIndex R M ι d)
    (U : (ambientGrassmannianScheme R M ι d).Opens)
    (hi : U ≤ (chart i).opensRange) (hj : U ≤ (chart j).opensRange) :
    (pullback (coordinate (chart i) U hi)).obj (structureModule (indexedChartScheme i)) ≅
      (pullback (coordinate (chart j) U hj)).obj (structureModule (indexedChartScheme j)) :=
  coordinateIso (coordinate (chart i) U hi)
    (coordinate (chart j) U hj) (determinantOpenUnit i j U hi hj)⁻¹

/-- The original determinant comparisons refine through the canonical pullback paths. -/
theorem determinantLineOverlapIso_refine (i j : AmbientChartIndex R M ι d)
    (U V : (ambientGrassmannianScheme R M ι d).Opens) (h : V ≤ U)
    (hi : U ≤ (chart i).opensRange) (hj : U ≤ (chart j).opensRange) :
    (pullback ((ambientGrassmannianScheme R M ι d).homOfLE h)).map
        (determinantLineOverlapIso i j U hi hj).hom ≫
      (SheafPullbackPathComparison.comparison _ (coordinate (chart j) U hj)
        (coordinate (chart j) V (h.trans hj)) (coordinate_refine (chart j) h hj)).hom.app
          (structureModule (indexedChartScheme j)) =
      (SheafPullbackPathComparison.comparison _ (coordinate (chart i) U hi)
        (coordinate (chart i) V (h.trans hi)) (coordinate_refine (chart i) h hi)).hom.app
          (structureModule (indexedChartScheme i)) ≫
        (determinantLineOverlapIso i j V (h.trans hi) (h.trans hj)).hom := by
  delta determinantLineOverlapIso
  apply coordinateIso_refine
  have hu := congrArg Inv.inv (determinantOpenUnit_refine i j U V h hi hj)
  rw [← map_inv] at hu
  exact congrArg Units.val hu

/-- The actual determinant comparisons obey the triple cocycle. -/
theorem determinantLineOverlapIso_cocycle (i j k : AmbientChartIndex R M ι d)
    (U : (ambientGrassmannianScheme R M ι d).Opens)
    (hi : U ≤ (chart i).opensRange) (hj : U ≤ (chart j).opensRange)
    (hk : U ≤ (chart k).opensRange) :
    (determinantLineOverlapIso i j U hi hj).hom ≫
        (determinantLineOverlapIso j k U hj hk).hom =
      (determinantLineOverlapIso i k U hi hk).hom := by
  delta determinantLineOverlapIso
  rw [coordinateIso_comp, ← mul_inv, ← determinantOpenUnit_cocycle]

end FLT.Mazur.GrassmannianChart
