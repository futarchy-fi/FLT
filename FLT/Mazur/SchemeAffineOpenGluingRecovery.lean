/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenImageRecovery
public import FLT.Mazur.SchemeAffineOpenGluing

/-!
# Recovery of the original affine chart modules

The glued image-open object pulls back to each original affine base module.
Further pullback to its faithfully flat covering chart recovers the original
sheaf of the geometric descent datum.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open ModuleSheafOpenImageChart ModuleSheafOverlapImageTransition
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
attribute [local irreducible] Chart.sheaf openGlued

/-- Pullback of the glued module along the original affine chart recovers its descent. -/
def openGluedChartIso (i : ι) :
    (pullback (C i).base).obj (openGlued C D) ≅ (C i).sheaf D :=
  pullbackRecovery (C i).base ((C i).sheaf D) (openGlued C D)
    (openGluedRestrictionIso C D i)

/-- Pullback through each covering chart reconstructs the original geometric sheaf. -/
def openGluedCoverChartIso (i : ι) :
    (pullback (Spec.map (C i).ringMap)).obj
        ((pullback (C i).base).obj (openGlued C D)) ≅
      (pullback (C i).cover).obj M :=
  (pullback (Spec.map (C i).ringMap)).mapIso (openGluedChartIso C D i) ≪≫
    (C i).reconstruction D

end FLT.Mazur.SchemeAffineDescent
