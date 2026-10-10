/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineBaseRecoveryCharts
public import FLT.Mazur.SchemeAffineRecognitionTest
public import FLT.Mazur.SchemeAffineChartTestRecovery
public import FLT.Mazur.ModuleSheafAffineTestCompatibility

/-!
# Overlap compatibility of local base recovery

On affine tests, both candidate recognition and actual glued chart recovery
intertwine the same effective comparison. Cancelling it proves compatibility
of the local base-object round trips for open-immersion gluing.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y W : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable (A : X.Modules) (e : (pullback p).obj A ≅ M)
variable (he : D.overlap = SchemePullbackOverlap.chartOverlap p
  (Limits.pullback.fst p p) (Limits.pullback.snd p p) (Limits.pullback.fst p p ≫ p)
  rfl Limits.pullback.condition.symm A e)
variable [∀ i, ((pullback (C i).base).obj A).IsQuasicoherent]
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
attribute [local irreducible] Chart.sheaf openGlued Chart.recognitionIso openGluedChartIso

/-- A normalized local base round trip compares recognition with actual chart recovery. -/
lemma baseRecoveryChartIso_normalize (i : ι) (a : W ⟶ X)
    (b : W ⟶ Spec (C i).baseRing) (hb : b ≫ (C i).base = a) :
    SheafPullbackMapNormalization.normalize b (C i).base (C i).base a a hb hb
        (baseRecoveryChartIso C D A e he i).hom =
      ((C i).recognitionTestIso D A e he a b hb).hom ≫
        (chartTestRecoveryIso C D i a b hb).inv := by
  simp only [SheafPullbackMapNormalization.normalize, baseRecoveryChartIso,
    Chart.recognitionTestIso, chartTestRecoveryIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc]

/-- The local base-object isomorphisms agree on every overlap. -/
lemma baseRecoveryChartIso_compatible :
    ModuleSheafOpenImmersionGluing.Compatible (fun i ↦ Spec (C i).baseRing)
      (fun i ↦ (C i).base) (fun i ↦ (baseRecoveryChartIso C D A e he i).hom) := by
  apply ModuleSheafOpenImmersionGluing.compatible_of_affine_tests
  intro i j R b c a hb hc
  rw [baseRecoveryChartIso_normalize, baseRecoveryChartIso_normalize]
  apply (cancel_mono (chartTestRecoveryIso C D j a c hc).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← chartTestRecoveryIso_comparison C D i j a b c hb hc]
  simp only [Iso.inv_hom_id_assoc]
  exact (C i).recognitionTestIso_affine (C j) D A e he a b c hb hc

end FLT.Mazur.SchemeAffineDescent
