/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeOverlapRefinementCover
public import FLT.Mazur.ModuleSheafLocalHomComparison

/-!
# Local linear maps on relative overlap refinements

A pullback comparison equation on an affine refinement gives equality of
local maps on every subopen of its image in the full relative overlap.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

open AffineIteratedPullbackSections ModuleSheafOpenImmersionLocalHom
open ModuleSheafMorphismGluing

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y) (U V : X.affineOpens)

attribute [local irreducible] Scheme.Modules.pullback relativeTensorTransition
attribute [local irreducible] relativeTensorOverlapChart compositeIso

/-- A concrete affine refinement equation identifies the induced local linear maps. -/
lemma relativeOverlapLocalHom_refine {W Z : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : Z.1 ⟶ W.1)
    (M N : (relativeTensorOverlap J f U V).Modules)
    (a : (pullback (X := Spec (.of (RelativeAlgebra J f W)))
        (relativeTensorOverlapChart J f i j)).obj M ⟶
      (pullback (X := Spec (.of (RelativeAlgebra J f W)))
        (relativeTensorOverlapChart J f i j)).obj N)
    (b : (pullback (X := Spec (.of (RelativeAlgebra J f Z)))
        (relativeTensorOverlapChart J f (k ≫ i) (k ≫ j))).obj M ⟶
      (pullback (X := Spec (.of (RelativeAlgebra J f Z)))
        (relativeTensorOverlapChart J f (k ≫ i) (k ≫ j))).obj N)
    (hab : (pullback (relativeTensorTransition J f k)).map a ≫
        (compositeIso (X := Spec (.of (RelativeAlgebra J f Z)))
          (Y := Spec (.of (RelativeAlgebra J f W))) (relativeTensorTransition J f k)
          (relativeTensorOverlapChart J f i j)
          (relativeTensorOverlapChart J f (k ≫ i) (k ≫ j))
          (relativeTensorOverlapChart_refine J f i j k) N).hom =
      (compositeIso (X := Spec (.of (RelativeAlgebra J f Z)))
          (Y := Spec (.of (RelativeAlgebra J f W))) (relativeTensorTransition J f k)
          (relativeTensorOverlapChart J f i j)
          (relativeTensorOverlapChart J f (k ≫ i) (k ≫ j))
          (relativeTensorOverlapChart_refine J f i j k) M).hom ≫ b)
    (S : (relativeTensorOverlap J f U V).Opens)
    (hS : S ≤ (relativeTensorOverlapChart J f (k ≫ i) (k ≫ j)).opensRange)
    (hW : S ≤ (relativeTensorOverlapChart J f i j).opensRange) :
    localApp (localHom (Y := Spec (.of (RelativeAlgebra J f Z)))
      (relativeTensorOverlapChart J f (k ≫ i) (k ≫ j)) b) hS =
    localApp (localHom (Y := Spec (.of (RelativeAlgebra J f W)))
      (relativeTensorOverlapChart J f i j) a) hW := by
  let _ := relativeTensorTransition_isOpenImmersion J f k
  exact localHom_refine_of_eq (Y := Spec (.of (RelativeAlgebra J f W)))
    (Z := Spec (.of (RelativeAlgebra J f Z)))
    (relativeTensorOverlapChart J f i j) (relativeTensorTransition J f k)
    (relativeTensorOverlapChart J f (k ≫ i) (k ≫ j))
    (relativeTensorOverlapChart_refine J f i j k) a b hab S hS hW

end FLT.Mazur.IdealAdicGradedPullback
