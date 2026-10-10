/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineBaseRecovery
public import FLT.Mazur.SchemeAffineCoverRecovery

/-!
# Base recovery on the original affine covering charts

Normalizing the retained base reconstruction through the chart square recovers
the supplied candidate isomorphism on the covering scheme.
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

attribute [local irreducible] openGlued Chart.sheaf

/-- The two chart-square comparisons are inverse paths. -/
lemma Chart.coverPullbackIso_squareIso (c : Chart p) (F : X.Modules) :
    c.coverPullbackIso.hom.app F ≫
        (SchemePullbackSquare.squareIso p (Spec.map c.ringMap) c.base c.cover
          c.square).hom.app F = 𝟙 _ := by
  simp only [Chart.coverPullbackIso, SchemePullbackSquare.squareIso,
    SheafPullbackPathComparison.comparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  simp only [← Category.assoc]
  simp [pullbackCongr]

/-- Base recovery followed by covering-chart recovery equals the candidate reconstruction. -/
@[reassoc]
lemma baseRecoveryIso_cover (i : ι) :
    (pullback (C i).cover).map
        ((pullback p).map (baseRecoveryIso C D A e he hcover).hom) ≫
        (coverRecoveryIso C D i).hom = (pullback (C i).cover).map e.hom := by
  have hn := (C i).coverPullbackIso.hom.naturality
    (baseRecoveryIso C D A e he hcover).hom
  dsimp only [Functor.comp_map] at hn
  simp only [coverRecoveryIso, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, hn, Category.assoc, baseRecoveryIso_reconstruction]
  simp only [SchemeGeometricDescent.Data.recognitionChart, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, Chart.coverPullbackIso_squareIso]
  exact Category.id_comp _

end FLT.Mazur.SchemeAffineDescent
