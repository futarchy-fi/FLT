/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineChartRecognitionIso
public import FLT.Mazur.SchemeAffineOpenGluingRecovery

/-!
# Base recovery on the charts of a glued descent object

Compose candidate recognition with the inverse of actual open-gluing recovery.
This gives local base-object round trips with their prescribed cover equations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SchemePullbackOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable (A : X.Modules) (e : (pullback p).obj A ≅ M)
variable (he : D.overlap = chartOverlap p (Limits.pullback.fst p p)
  (Limits.pullback.snd p p) (Limits.pullback.fst p p ≫ p)
  rfl Limits.pullback.condition.symm A e)
variable [∀ i, ((pullback (C i).base).obj A).IsQuasicoherent]
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]

/-- Candidate recognition and actual gluing give the local base recovery isomorphism. -/
def baseRecoveryChartIso (i : ι) :
    (pullback (C i).base).obj A ≅ (pullback (C i).base).obj (openGlued C D) :=
  (C i).recognitionIso D A e he ≪≫ (openGluedChartIso C D i).symm

/-- Base recovery on a chart retains the prescribed reconstruction over its cover. -/
@[reassoc]
lemma baseRecoveryChartIso_reconstruction (i : ι) :
    (pullback (Spec.map (C i).ringMap)).map (baseRecoveryChartIso C D A e he i).hom ≫
        (openGluedCoverChartIso C D i).hom =
      (SchemeGeometricDescent.Data.recognitionChart p A e
        (C i).ringMap (C i).base (C i).cover (C i).square).hom := by
  simp only [baseRecoveryChartIso, openGluedCoverChartIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (C i).recognitionIso_reconstruction D A e he

end FLT.Mazur.SchemeAffineDescent
