/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionProjectionCocycle
public import FLT.Mazur.ModuleUnitCocycleCongr

/-!
# Pullback recovery on the scalar-extended colimit

The model line sheaf pulls back to the sheaf of the tensor-extended units.
The comparison accounts for the equality of chart inverse images.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve.ModuleSheafUnitCocycle
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {S A : Type u} [CommRing S] [CommRing A] [Algebra S A]
  {ι : Type u} [Finite ι] (D : NonemptyChartSet ι ⥤ CommAlgCat S)
  [∀ a b (f : a ⟶ b),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom))]
  [((affineIntersectionSchemeDiagram D) ⋙ Scheme.forget).IsLocallyDirected]
  [((affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)) ⋙
    Scheme.forget).IsLocallyDirected]

variable
  (y : ∀ s, IntersectionPair s → (D.obj s)ˣ)
  (hnat : ∀ {s t} (f : s ⟶ t) (k : IntersectionPair s),
    (D.map f).hom (y s k) = (y t (intersectionPairMap f k) : D.obj t))
  (hmul : ∀ s (k : IntersectionTriple s),
    y s (k.1, k.2.1) * y s (k.2.1, k.2.2) = y s (k.1, k.2.2))

/-- The inverse-image cocycle sheaf is the scalar-extended coordinate cocycle sheaf. -/
def affineIntersectionProjectionCocycleSheafIso :
    ((affineIntersectionModelCocycle D y hnat hmul).inverseImage
      (colimMap (affineIntersectionProjection (A := A) D))).sheaf ≅
      affineIntersectionModelSheaf (affineIntersectionScalarExtension (A := A) D)
        (scalarIntersectionUnit D y) (scalarIntersectionUnit_naturality D y hnat)
        (scalarIntersectionUnit_mul D y hmul) := by
  apply Cocycle.sheafIsoOfUnits _ _
    (fun i ↦ affineIntersectionProjection_preimage D (singletonChartSet i))
  intro i j V hi hj
  have hi' := hi.trans (affineIntersectionProjection_preimage D (singletonChartSet i)).le
  have hj' := hj.trans (affineIntersectionProjection_preimage D (singletonChartSet j)).le
  have hV : V ≤ intersectionColimitOpen
      (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D))
      (pairChartSet i j) := by
    rw [pairChartSet, intersectionColimitOpen_union]
    exact le_inf hi' hj'
  rw [affineIntersectionProjection_inverseImageUnit D y hnat hmul i j V hi hj
    (pairChartSet i j) (by simp) (by simp) hV]
  exact (affineIntersectionModelCocycle_unit_eq _ _ _ _ i j V _ _
    (pairChartSet i j) (by simp) (by simp) hV).symm

/-- Actual sheaf pullback along coefficient projection recovers the scalar-extension model. -/
def affineIntersectionProjectionSheafIso :
    (Scheme.Modules.pullback (colimMap (affineIntersectionProjection (A := A) D))).obj
        (affineIntersectionModelSheaf D y hnat hmul) ≅
      affineIntersectionModelSheaf (affineIntersectionScalarExtension (A := A) D)
        (scalarIntersectionUnit D y) (scalarIntersectionUnit_naturality D y hnat)
        (scalarIntersectionUnit_mul D y hmul) :=
  (affineIntersectionModelCocycle D y hnat hmul).pullbackIso _
    (intersectionColimitOpen_singleton_cover _) ≪≫
      affineIntersectionProjectionCocycleSheafIso D y hnat hmul

end FLT.Mazur.Approximation
