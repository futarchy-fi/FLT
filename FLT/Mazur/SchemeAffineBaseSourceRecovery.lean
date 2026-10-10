/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineBaseCoverRecovery
public import FLT.Mazur.SchemeAffineSourceGlobalRecovery

/-!
# The triangle between actual base and source recovery

The retained affine cover equation descends to each original source open.
The source cover then proves that the two global recoveries compose to the
candidate reconstruction, without introducing a new choice of either map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → SourceChart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable (A : X.Modules) (e : (pullback p).obj A ≅ M)
variable (he : D.overlap = SchemePullbackOverlap.chartOverlap p
  (Limits.pullback.fst p p) (Limits.pullback.snd p p) (Limits.pullback.fst p p ≫ p)
  rfl Limits.pullback.condition.symm A e)
variable [∀ i, ((pullback (C i).chart.base).obj A).IsQuasicoherent]
variable [∀ i, ((pullback (C i).chart.cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).chart.base]
variable (hcover : ∀ x : X, ∃ i, x ∈ Set.range (C i).chart.base)

attribute [local irreducible] openGlued Chart.sheaf coverRecoveryIso

/-- Base recovery followed by source-chart recovery is the supplied reconstruction. -/
@[reassoc]
lemma baseRecoveryIso_source (i : ι) :
    (pullback (C i).sourceMap).map
        ((pullback p).map
          (baseRecoveryIso (fun j ↦ (C j).chart) D A e he hcover).hom) ≫
        (sourceRecoveryIso C D i).hom = (pullback (C i).sourceMap).map e.hom := by
  let k := SheafPullbackPathComparison.comparison (C i).lift (C i).chart.cover
    (C i).sourceMap (C i).square
  have hl := k.inv.naturality
    ((pullback p).map (baseRecoveryIso (fun j ↦ (C j).chart) D A e he hcover).hom)
  have hr := k.hom.naturality e.hom
  dsimp only [Functor.comp_map] at hl hr
  simp only [sourceRecoveryIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom]
  change _ ≫ k.inv.app _ ≫ _ = _
  rw [← Category.assoc, hl, Category.assoc, ← Functor.map_comp_assoc,
    baseRecoveryIso_cover (fun j ↦ (C j).chart) D A e he hcover i, hr,
    Iso.inv_hom_id_app_assoc]

/-- The actual global source and base recoveries satisfy the candidate triangle. -/
@[reassoc]
lemma baseRecoveryIso_sourceGlued
    (hsource : ∀ y : Y, ∃ i, y ∈ Set.range (C i).sourceMap) :
    (pullback p).map (baseRecoveryIso (fun j ↦ (C j).chart) D A e he hcover).hom ≫
        (sourceGluedRecoveryIso C D hsource).hom = e.hom := by
  apply ModuleSheafOpenImmersionGluing.hom_ext (fun i ↦ (C i).source)
    (fun i ↦ (C i).sourceMap) hsource
  intro i
  rw [Functor.map_comp, sourceGluedRecoveryIso_pullback]
  exact baseRecoveryIso_source C D A e he hcover i

end FLT.Mazur.SchemeAffineDescent
