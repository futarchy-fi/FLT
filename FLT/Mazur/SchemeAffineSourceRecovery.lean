/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCoverRecovery
public import FLT.Mazur.SchemeAffineFppfSourceChart

/-!
# Reconstruction on original source opens

Pull the chart reconstruction through the constructed source inclusion and
normalize its path. Both objects and compatible morphisms are recovered on
actual open subschemes of the original covering scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SheafPullbackPathComparison
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → SourceChart p) {M N : Y.Modules}
variable (D : SchemeGeometricDescent.Data p M) (E : SchemeGeometricDescent.Data p N)
variable [∀ i, ((pullback (C i).chart.cover).obj M).IsQuasicoherent]
variable [∀ i, ((pullback (C i).chart.cover).obj N).IsQuasicoherent]
attribute [local irreducible] openGlued Chart.sheaf coverRecoveryIso

/-- Reconstruction on an original affine open of the covering scheme. -/
def sourceRecoveryIso (i : ι) :
    (pullback (C i).sourceMap).obj ((pullback p).obj (openGlued (fun j ↦ (C j).chart) D)) ≅
      (pullback (C i).sourceMap).obj M :=
  (comparison (C i).lift (C i).chart.cover (C i).sourceMap (C i).square).symm.app _ ≪≫
    (pullback (C i).lift).mapIso (coverRecoveryIso (fun j ↦ (C j).chart) D i) ≪≫
      (comparison (C i).lift (C i).chart.cover (C i).sourceMap (C i).square).app M

/-- The reconstruction on original source opens retains the original compatible morphism. -/
@[reassoc]
lemma sourceRecoveryIso_naturality
    (hC : iSup (fun i ↦ (C i).chart.base.opensRange) = ⊤)
    (f : M ⟶ N) (hf : D.MapCompatible p E f) (i : ι) :
    (pullback (C i).sourceMap).map
        ((pullback p).map (openGluedMap (fun j ↦ (C j).chart) D E hC f hf)) ≫
        (sourceRecoveryIso C E i).hom =
      (sourceRecoveryIso C D i).hom ≫ (pullback (C i).sourceMap).map f := by
  let e := comparison (C i).lift (C i).chart.cover (C i).sourceMap (C i).square
  have hleft := e.inv.naturality
    ((pullback p).map (openGluedMap (fun j ↦ (C j).chart) D E hC f hf))
  have hright := e.hom.naturality f
  dsimp only [Functor.comp_map] at hleft hright
  simp only [sourceRecoveryIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  change _ ≫ e.inv.app _ ≫ _ = e.inv.app _ ≫ _
  rw [← Category.assoc, hleft, Category.assoc,
    ← Functor.map_comp_assoc,
    coverRecoveryIso_naturality (fun j ↦ (C j).chart) D E hC f hf i,
    Functor.map_comp, Category.assoc, hright]

end FLT.Mazur.SchemeAffineDescent
