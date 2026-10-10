/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafGluingTransportProjection
public import FLT.Mazur.ModuleSheafOpenImageProjectionRecovery
public import FLT.Mazur.SchemeAffineOpenGluingRecovery

/-!
# Original chart projections of the effectively glued sheaf

The actual affine gluing projections recover the original chart isomorphisms
after pullback and satisfy the original open transition equations.
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
attribute [local irreducible] Chart.sheaf

/-- The glued sheaf projects into the original ambient affine chart pushforward. -/
def openGluedProjection (i : ι) :
    openGlued C D ⟶ (pushforward (C i).base).obj ((C i).sheaf D) :=
  (openGluingData C D).projection i ≫ (imagePushforwardIso (C i).base ((C i).sheaf D)).hom

/-- The original chart recovery is the pulled projection followed by its open counit. -/
lemma openGluedChartIso_projection (i : ι) :
    (openGluedChartIso C D i).hom =
      (pullback (C i).base).map (openGluedProjection C D i) ≫
        (openCounitIso (C i).base ((C i).sheaf D)).hom := by
  exact pullbackRecovery_projection (C i).base ((C i).sheaf D)
    (openGlued C D) ((openGluingData C D).projection i)
    (openGluedRestrictionIso C D i) rfl

/-- The glued projections retain the actual open comparison on every pair overlap. -/
@[reassoc]
lemma openGluedProjection_transition (i j : ι) :
    (openGluedProjection C D i).over ((C i).base.opensRange ⊓ (C j).base.opensRange) ≫
        ((C i).openTestIso (C j) D ((C i).base.opensRange ⊓ (C j).base.opensRange)
          inf_le_left inf_le_right).hom =
      (openGluedProjection C D j).over ((C i).base.opensRange ⊓ (C j).base.opensRange) :=
  ModuleSheafGluing.ambientProjection_transition (fun k ↦ (C k).base.opensRange)
    (fun k ↦ imageModule (C k).base ((C k).sheaf D))
    (fun k ↦ (pushforward (C k).base).obj ((C k).sheaf D))
    (fun k ↦ imagePushforwardIso (C k).base ((C k).sheaf D))
    (fun k l ↦ (C k).openTestIso (C l) D
      ((C k).base.opensRange ⊓ (C l).base.opensRange) inf_le_left inf_le_right)
    (openTransition_cocycle C D) i j

end FLT.Mazur.SchemeAffineDescent
