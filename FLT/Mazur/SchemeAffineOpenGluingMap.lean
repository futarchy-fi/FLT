/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafGluingTransportMap
public import FLT.Mazur.ModuleSheafOpenImageMap
public import FLT.Mazur.SchemeAffineOpenGluing
public import FLT.Mazur.SchemeAffineOpenTestNaturality

/-!
# Gluing compatible maps of descended affine charts

A compatible map of the original geometric descent data supplies all chart
maps and their overlap compatibility, hence a map of the glued module sheaves.
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
attribute [local irreducible] Chart.sheaf Chart.map

/-- Original compatible maps determine a morphism of the constructed open gluing data. -/
def openGluingMap (f : M ⟶ N) (hf : D.MapCompatible p E f) :
    (openGluingData C D).Map (openGluingData C E) :=
  ModuleSheafGluing.ofPushforwardIsoEvalMap _ _ _ _ _ _ _ _ _ _ _
    (fun i ↦ imageMap (C i).base ((C i).map D E f hf))
    (fun i ↦ (pushforward (C i).base).map ((C i).map D E f hf))
    (fun i ↦ imagePushforwardIso_naturality (C i).base ((C i).map D E f hf))
    (fun i j V hi hj s ↦ (C i).openTestIso_naturality_eval (C j) D E _ _ _
      f hf V (le_inf hi hj) s)

/-- Glue a compatible original map on a jointly covering family of base charts. -/
def openGluedMap (hC : iSup (fun i ↦ (C i).base.opensRange) = ⊤)
    (f : M ⟶ N) (hf : D.MapCompatible p E f) : openGlued C D ⟶ openGlued C E :=
  (openGluingMap C D E f hf).gluedMap hC

/-- Every chart projection of the glued map retains the transported original chart map. -/
@[reassoc]
lemma openGluedMap_projection (hC : iSup (fun i ↦ (C i).base.opensRange) = ⊤)
    (f : M ⟶ N) (hf : D.MapCompatible p E f) (i : ι) :
    openGluedMap C D E hC f hf ≫ (openGluingData C E).projection i =
      (openGluingData C D).projection i ≫
        (pushforward (C i).base.opensRange.ι).map
          (imageMap (C i).base ((C i).map D E f hf)) :=
  (openGluingMap C D E f hf).gluedMap_projection hC i

end FLT.Mazur.SchemeAffineDescent
