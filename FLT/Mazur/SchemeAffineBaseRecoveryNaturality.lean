/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineBaseRecovery
public import FLT.Mazur.SchemeAffineRecognitionNaturality
public import FLT.Mazur.SchemeAffineOpenGluingMapRecovery

/-!
# Naturality of global base recovery

The actual affine recognition squares determine the global recovery map.
Faithfully flat reconstruction and the base open cover detect its naturality.
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

variable {N : Y.Modules} (E : SchemeGeometricDescent.Data p N)
variable (B : X.Modules) (e' : (pullback p).obj B ≅ N)
variable (he' : E.overlap = SchemePullbackOverlap.chartOverlap p
  (Limits.pullback.fst p p) (Limits.pullback.snd p p) (Limits.pullback.fst p p ≫ p)
  rfl Limits.pullback.condition.symm B e')
variable [∀ i, ((pullback (C i).base).obj B).IsQuasicoherent]
variable [∀ i, ((pullback (C i).cover).obj N).IsQuasicoherent]
variable (hC : iSup (fun i ↦ (C i).base.opensRange) = ⊤)
attribute [local irreducible] openGlued Chart.sheaf

/-- Global base recovery commutes with every compatible candidate reconstruction square. -/
@[reassoc]
lemma baseRecoveryIso_naturality (f : A ⟶ B) (g : M ⟶ N)
    (hg : D.MapCompatible p E g) (h : (pullback p).map f ≫ e'.hom = e.hom ≫ g) :
    f ≫ (baseRecoveryIso C E B e' he' hcover).hom =
      (baseRecoveryIso C D A e he hcover).hom ≫ openGluedMap C D E hC g hg := by
  apply ModuleSheafOpenImmersionGluing.hom_ext (fun i ↦ Spec (C i).baseRing)
    (fun i ↦ (C i).base) hcover
  intro i
  let _ : ((pullback (C i).base).obj (openGlued C E)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec (C i).baseRing).ringCatSheaf).prop_of_iso
      (openGluedChartIso C E i).symm (inferInstance)
  apply AffineQuasicoherentPullbackFaithful.reconstruction_unique (C i).ringMap
    (C i).faithfullyFlat (openGluedCoverChartIso C E i)
  simp only [Functor.map_comp, Category.assoc]
  rw [baseRecoveryIso_reconstruction, openGluedMap_coverChart,
    ← Category.assoc, baseRecoveryIso_reconstruction]
  exact SchemeGeometricDescent.Data.recognitionChart_naturality p e e' f g h
    (C i).ringMap (C i).base (C i).cover (C i).square

end FLT.Mazur.SchemeAffineDescent
