/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineOpenGluingMapRecovery

/-!
# Reconstruction as actual pullbacks over the covering scheme

Normalize the chart square so reconstruction compares the pullback of the
constructed global object with the original sheaf on the covering scheme.
The normalization retains naturality for every compatible original morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}

/-- Compare the two pullback paths around the original affine chart square. -/
def Chart.coverPullbackIso (C : Chart p) :
    pullback p ⋙ pullback C.cover ≅ pullback C.base ⋙ pullback (Spec.map C.ringMap) :=
  pullbackComp C.cover p ≪≫ pullbackCongr C.square.symm ≪≫
    (pullbackComp (Spec.map C.ringMap) C.base).symm

variable (C : ι → Chart p) {M N : Y.Modules}
variable (D : SchemeGeometricDescent.Data p M) (E : SchemeGeometricDescent.Data p N)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, ((pullback (C i).cover).obj N).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
attribute [local irreducible] openGlued Chart.sheaf

/-- Reconstruction on a covering chart, with both sides pulled back from Y. -/
def coverRecoveryIso (i : ι) :
    (pullback (C i).cover).obj ((pullback p).obj (openGlued C D)) ≅
      (pullback (C i).cover).obj M :=
  (C i).coverPullbackIso.app (openGlued C D) ≪≫ openGluedCoverChartIso C D i

/-- The normalized chart reconstruction recovers the original compatible map. -/
@[reassoc]
lemma coverRecoveryIso_naturality (hC : iSup (fun i ↦ (C i).base.opensRange) = ⊤)
    (f : M ⟶ N) (hf : D.MapCompatible p E f) (i : ι) :
    (pullback (C i).cover).map ((pullback p).map (openGluedMap C D E hC f hf)) ≫
        (coverRecoveryIso C E i).hom =
      (coverRecoveryIso C D i).hom ≫ (pullback (C i).cover).map f := by
  have hn := (C i).coverPullbackIso.hom.naturality (openGluedMap C D E hC f hf)
  dsimp only [Functor.comp_map] at hn
  simp only [coverRecoveryIso, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, hn, Category.assoc, openGluedMap_coverChart, Category.assoc]

end FLT.Mazur.SchemeAffineDescent
