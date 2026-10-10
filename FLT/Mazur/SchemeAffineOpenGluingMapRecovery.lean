/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafGluingMapRestriction
public import FLT.Mazur.ModuleSheafOpenImageMapRecovery
public import FLT.Mazur.SchemeAffineOpenGluingMap
public import FLT.Mazur.SchemeAffineOpenGluingRecovery

/-!
# Recovering the original morphism from affine-chart gluing

The glued map restricts to the transported map on each image open, to the
effective map on each affine base chart, and to the original map on the cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open ModuleSheafOpenImageChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) {M N : Y.Modules}
variable (D : SchemeGeometricDescent.Data p M) (E : SchemeGeometricDescent.Data p N)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, ((pullback (C i).cover).obj N).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
variable (hC : iSup (fun i ↦ (C i).base.opensRange) = ⊤)
variable (f : M ⟶ N) (hf : D.MapCompatible p E f)
attribute [local irreducible] Chart.sheaf Chart.map

/-- The glued map restricts to the transported original map on each image open. -/
@[reassoc]
lemma openGluedMap_restriction (i : ι) :
    (restrictFunctor (C i).base.opensRange.ι).map (openGluedMap C D E hC f hf) ≫
        (openGluedRestrictionIso C E i).hom =
      (openGluedRestrictionIso C D i).hom ≫ imageMap (C i).base ((C i).map D E f hf) :=
  (openGluingMap C D E f hf).gluedMap_restrictionIso hC i

/-- Pullback to each original affine base chart recovers its effective map. -/
@[reassoc]
lemma openGluedMap_chart (i : ι) :
    (pullback (C i).base).map (openGluedMap C D E hC f hf) ≫
        (openGluedChartIso C E i).hom =
      (openGluedChartIso C D i).hom ≫ (C i).map D E f hf :=
  pullbackRecovery_naturality (C i).base _ _ _ _
    (openGluedMap_restriction C D E hC f hf i)

/-- The original morphism is recovered after pullback to the covering affine chart. -/
@[reassoc]
lemma openGluedMap_coverChart (i : ι) :
    (pullback (Spec.map (C i).ringMap)).map
        ((pullback (C i).base).map (openGluedMap C D E hC f hf)) ≫
        (openGluedCoverChartIso C E i).hom =
      (openGluedCoverChartIso C D i).hom ≫ (pullback (C i).cover).map f := by
  have hr : (pullback (Spec.map (C i).ringMap)).map ((C i).map D E f hf) ≫
      ((C i).reconstruction E).hom =
        ((C i).reconstruction D).hom ≫ (pullback (C i).cover).map f := by
    simpa only [Chart.map, Chart.reconstruction, Chart.sheaf] using
      D.chartMap_reconstruction (C i).ringMap p E (C i).base (C i).cover
        (C i).square (C i).faithfullyFlat f hf
  simp only [openGluedCoverChartIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, openGluedMap_chart, Functor.map_comp, Category.assoc, hr]

end FLT.Mazur.SchemeAffineDescent
