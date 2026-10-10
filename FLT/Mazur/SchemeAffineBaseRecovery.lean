/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineBaseRecoveryCompatibility

/-!
# Global recovery of a recognized base sheaf

The compatible affine-chart isomorphisms glue over the constructed base cover.
Their actual pullbacks and faithfully flat reconstruction equations are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable (A : X.Modules) (e : (pullback p).obj A ≅ M)
variable (he : D.overlap = SchemePullbackOverlap.chartOverlap p
  (Limits.pullback.fst p p) (Limits.pullback.snd p p) (Limits.pullback.fst p p ≫ p)
  rfl Limits.pullback.condition.symm A e)
variable [∀ i, ((pullback (C i).base).obj A).IsQuasicoherent]
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
variable (hcover : ∀ x : X, ∃ i, x ∈ Set.range (C i).base)

/-- Glue recognition into an actual global base-object recovery isomorphism. -/
def baseRecoveryIso : A ≅ openGlued C D :=
  ModuleSheafOpenImmersionGluing.glueIso (fun i ↦ Spec (C i).baseRing)
    (fun i ↦ (C i).base) hcover (fun i ↦ (baseRecoveryChartIso C D A e he i).hom)
    (baseRecoveryChartIso_compatible C D A e he) (fun _ ↦ inferInstance)

/-- Global recovery pulls back to the prescribed chart recovery, without a new choice. -/
lemma baseRecoveryIso_chart (i : ι) :
    (pullback (C i).base).map (baseRecoveryIso C D A e he hcover).hom =
      (baseRecoveryChartIso C D A e he i).hom :=
  ModuleSheafOpenImmersionGluing.pullback_glue (fun i ↦ Spec (C i).baseRing)
    (fun i ↦ (C i).base) hcover _ (baseRecoveryChartIso_compatible C D A e he) i

/-- The global isomorphism retains the candidate's reconstruction over every cover chart. -/
@[reassoc]
lemma baseRecoveryIso_reconstruction (i : ι) :
    (pullback (Spec.map (C i).ringMap)).map
        ((pullback (C i).base).map (baseRecoveryIso C D A e he hcover).hom) ≫
        (openGluedCoverChartIso C D i).hom =
      (SchemeGeometricDescent.Data.recognitionChart p A e
        (C i).ringMap (C i).base (C i).cover (C i).square).hom := by
  rw [baseRecoveryIso_chart]
  exact baseRecoveryChartIso_reconstruction C D A e he i

/-- The actual chart pullbacks uniquely determine global base recovery. -/
lemma baseRecoveryIso_unique (f : A ⟶ openGlued C D)
    (hf : ∀ i, (pullback (C i).base).map f = (baseRecoveryChartIso C D A e he i).hom) :
    f = (baseRecoveryIso C D A e he hcover).hom := by
  apply ModuleSheafOpenImmersionGluing.hom_ext (fun i ↦ Spec (C i).baseRing)
    (fun i ↦ (C i).base) hcover
  intro i
  rw [hf, baseRecoveryIso_chart]

end FLT.Mazur.SchemeAffineDescent
