/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineSourceRecoveryCompatibility

/-!
# Global recovery from compatible original source charts

Glue the actual source recovery maps along the original source open cover.
The global isomorphism retains every chart equation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SheafPullbackPathComparison SheafPullbackMapNormalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → SourceChart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).chart.cover).obj M).IsQuasicoherent]
attribute [local irreducible] openGlued Chart.sheaf coverRecoveryIso

variable (hcover : ∀ y : Y, ∃ i, y ∈ Set.range (C i).sourceMap)

/-- The original source cover glues its compatible reconstruction isomorphisms. -/
def sourceGluedRecoveryIso :
    (pullback p).obj (openGlued (fun i ↦ (C i).chart) D) ≅ M :=
  ModuleSheafOpenImmersionGluing.glueIso (fun i ↦ (C i).source)
    (fun i ↦ (C i).sourceMap) hcover (fun i ↦ (sourceRecoveryIso C D i).hom)
    (sourceRecoveryIso_compatible C D) (fun _ ↦ inferInstance)

/-- Global reconstruction pulls back to the prescribed recovery on every source chart. -/
lemma sourceGluedRecoveryIso_pullback (i : ι) :
    (pullback (C i).sourceMap).map (sourceGluedRecoveryIso C D hcover).hom =
      (sourceRecoveryIso C D i).hom :=
  ModuleSheafOpenImmersionGluing.pullback_glue (fun i ↦ (C i).source)
    (fun i ↦ (C i).sourceMap) hcover (fun i ↦ (sourceRecoveryIso C D i).hom)
    (sourceRecoveryIso_compatible C D) i

/-- The source-chart equations determine global reconstruction uniquely. -/
lemma sourceGluedRecoveryIso_hom_unique
    (e : (pullback p).obj (openGlued (fun i ↦ (C i).chart) D) ⟶ M)
    (he : ∀ i, (pullback (C i).sourceMap).map e = (sourceRecoveryIso C D i).hom) :
    e = (sourceGluedRecoveryIso C D hcover).hom := by
  apply ModuleSheafOpenImmersionGluing.hom_ext (fun i ↦ (C i).source)
    (fun i ↦ (C i).sourceMap) hcover
  intro i
  rw [he, sourceGluedRecoveryIso_pullback]

end FLT.Mazur.SchemeAffineDescent
