/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineOpenGluingMapLaws
public import FLT.Mazur.SchemeAffineSourceMapFaithful
public import FLT.Mazur.SchemeFppfSourceLineGluing

/-!
# Faithful gluing of compatible line-bundle morphisms over an fppf cover

All chart families and coherence instances are constructed from the fppf
morphism and the original line bundles. Their glued maps recover the original
maps on a source open cover, hence gluing is faithful and preserves identities
and composition. Fullness still requires compatible object reconstruction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (p : Y ⟶ X)
variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
variable {M N P : Y.Modules}
variable (D : SchemeGeometricDescent.Data p M) (E : SchemeGeometricDescent.Data p N)
variable (F : SchemeGeometricDescent.Data p P)
variable (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N) (hP : LocallyFreeRankOne P)

/-- Glue a compatible original line-bundle map using the actual source-covering charts. -/
def fppfSourceLineMap (f : M ⟶ N) (hf : D.MapCompatible p E f) :
    fppfSourceLineGlued p D hM ⟶ fppfSourceLineGlued p E hN := by
  let _ := fppfSourceCharts_quasicoherent p hM
  let _ := fppfSourceCharts_quasicoherent p hN
  exact openGluedMap (fun y ↦ (fppfSourceCharts p y).chart) D E
    (fppfSourceCharts_baseCovers p) f hf

/-- The glued map recovers the original morphism on each original source open. -/
@[reassoc]
lemma fppfSourceLineMap_recovery (f : M ⟶ N) (hf : D.MapCompatible p E f) (y : Y) :
    (pullback (fppfSourceCharts p y).sourceMap).map
        ((pullback p).map (fppfSourceLineMap p D E hM hN f hf)) ≫
        (fppfSourceLineRecoveryIso p E hN y).hom =
      (fppfSourceLineRecoveryIso p D hM y).hom ≫
        (pullback (fppfSourceCharts p y).sourceMap).map f := by
  let _ := fppfSourceCharts_quasicoherent p hM
  let _ := fppfSourceCharts_quasicoherent p hN
  exact sourceRecoveryIso_naturality (fppfSourceCharts p) D E
    (fppfSourceCharts_baseCovers p) f hf y

/-- Gluing along an actual fppf morphism distinguishes compatible line-bundle maps. -/
lemma fppfSourceLineMap_injective (f g : M ⟶ N)
    (hf : D.MapCompatible p E f) (hg : D.MapCompatible p E g)
    (hfg : fppfSourceLineMap p D E hM hN f hf = fppfSourceLineMap p D E hM hN g hg) :
    f = g := by
  let _ := fppfSourceCharts_quasicoherent p hM
  let _ := fppfSourceCharts_quasicoherent p hN
  exact openGluedMap_injective_of_sourceCover (fppfSourceCharts p) D E
    (fppfSourceCharts_baseCovers p) (fppfSourceCharts_sourceCovers p) f g hf hg hfg

/-- The constructed fppf gluing preserves the identity. -/
lemma fppfSourceLineMap_identity (hf : D.MapCompatible p D (𝟙 M)) :
    fppfSourceLineMap p D D hM hM (𝟙 M) hf = 𝟙 _ := by
  let _ := fppfSourceCharts_quasicoherent p hM
  exact openGluedMap_identity (fun y ↦ (fppfSourceCharts p y).chart) D
    (fppfSourceCharts_baseCovers p) hf

/-- The constructed fppf gluing preserves composition. -/
lemma fppfSourceLineMap_composition (f : M ⟶ N) (g : N ⟶ P)
    (hf : D.MapCompatible p E f) (hg : E.MapCompatible p F g)
    (hfg : D.MapCompatible p F (f ≫ g)) :
    fppfSourceLineMap p D F hM hP (f ≫ g) hfg =
      fppfSourceLineMap p D E hM hN f hf ≫ fppfSourceLineMap p E F hN hP g hg := by
  let _ := fppfSourceCharts_quasicoherent p hM
  let _ := fppfSourceCharts_quasicoherent p hN
  let _ := fppfSourceCharts_quasicoherent p hP
  exact openGluedMap_composition (fun y ↦ (fppfSourceCharts p y).chart) D E F
    (fppfSourceCharts_baseCovers p) f g hf hg hfg

end FLT.Mazur.SchemeAffineDescent
