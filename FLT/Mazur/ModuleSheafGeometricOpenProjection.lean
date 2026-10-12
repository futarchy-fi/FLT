/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafGeometricOpenGluing
public import FLT.Mazur.ModuleSheafGluingTransportProjection
public import FLT.Mazur.ModuleSheafOpenImageProjectionRecovery

/-!
# Original chart projections of geometric gluing

Chart isomorphisms on all common subopens, with their proved pullback coherence
and cocycle, give the actual section cocycle for the original chart pushforwards.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ModuleSheafGluing
open ModuleSheafOpenImageChart ModuleSheafOpenOverlapTransition
open ModuleSheafMorphismGluing SheafPullbackPathComparison
universe u
attribute [local irreducible] Scheme.Modules.pullback Scheme.Modules.pushforward
variable {X : Scheme.{u}} {ι : Type u} (Y : ι → Scheme.{u})
  (i : ∀ j, Y j ⟶ X) [∀ j, IsOpenImmersion (i j)] (M : ∀ j, (Y j).Modules)
variable (D : GeometricOpenSystem Y i M)

/-- Projection of the glued object to each original chart pushforward. -/
@[irreducible] def geometricOpenProjection (j : ι) :
    (ofGeometricOpenSystem Y i M D).glued ⟶ (pushforward (i j)).obj (M j) := by
  delta ofGeometricOpenSystem imageChartDataOfWitness imageChartData
  exact ambientProjection (fun j ↦ (i j).opensRange)
    (fun j ↦ imageModule (i j) (M j)) (fun j ↦ (pushforward (i j)).obj (M j))
    (fun j ↦ imagePushforwardIso (i j) (M j)) (geometricTransition Y i M D.iso)
    ((D.witness Y i M).cocycle Y i M (geometricTransition Y i M D.iso)) j

/-- The original geometric transitions identify the actual glued projections. -/
@[reassoc] theorem geometricOpenProjection_transition (j k : ι) :
    (geometricOpenProjection Y i M D j).over ((i j).opensRange ⊓ (i k).opensRange) ≫
        (geometricTransition Y i M D.iso j k).hom =
      (geometricOpenProjection Y i M D k).over ((i j).opensRange ⊓ (i k).opensRange) := by
  delta geometricOpenProjection ofGeometricOpenSystem imageChartDataOfWitness imageChartData
  exact ambientProjection_transition (fun j ↦ (i j).opensRange)
    (fun j ↦ imageModule (i j) (M j)) (fun j ↦ (pushforward (i j)).obj (M j))
    (fun j ↦ imagePushforwardIso (i j) (M j)) (geometricTransition Y i M D.iso)
    ((D.witness Y i M).cocycle Y i M (geometricTransition Y i M D.iso)) j k

/-- Original chart recovery is exactly the adjoint of the glued chart projection. -/
theorem geometricOpenSystemPullbackIso_projection (j : ι) :
    (geometricOpenSystemPullbackIso Y i M D j).hom =
      (pullback (i j)).map (geometricOpenProjection Y i M D j) ≫
        (ModuleSheafOverlapImageTransition.openCounitIso (i j) (M j)).hom := by
  delta geometricOpenSystemPullbackIso ofGeometricOpenSystem imageChartPullbackIsoOfWitness
    imageChartDataOfWitness imageChartPullbackIso imageChartData geometricOpenProjection
  exact pullbackRecovery_projection (i j) (M j) _ _ _ rfl

end FLT.Mazur.ModuleSheafGluing
