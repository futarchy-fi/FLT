/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineDescentChart
public import FLT.Mazur.AffineQuasicoherentPullbackFaithful

/-!
# Functor laws for effective affine chart maps

Faithfully flat reconstruction detects the identity and composition laws
for the actual chart maps obtained from geometric descent data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C : Chart p)
variable {M N P : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable (E : SchemeGeometricDescent.Data p N) (F : SchemeGeometricDescent.Data p P)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C.cover).obj N).IsQuasicoherent]
variable [((pullback C.cover).obj P).IsQuasicoherent]
attribute [local irreducible] sheaf map

/-- Reconstruction of a chart morphism retains the original restricted morphism. -/
@[reassoc]
lemma map_reconstruction (f : M ⟶ N) (hf : D.MapCompatible p E f) :
    (pullback (Spec.map C.ringMap)).map (C.map D E f hf) ≫ (C.reconstruction E).hom =
      (C.reconstruction D).hom ≫ (pullback C.cover).map f := by
  simpa only [map, reconstruction, sheaf] using
    D.chartMap_reconstruction C.ringMap p E C.base C.cover C.square C.faithfullyFlat f hf

/-- Reconstruction uniquely determines each effective chart morphism. -/
lemma map_unique (f : M ⟶ N) (hf : D.MapCompatible p E f)
    (g : C.sheaf D ⟶ C.sheaf E)
    (hg : (pullback (Spec.map C.ringMap)).map g ≫ (C.reconstruction E).hom =
      (C.reconstruction D).hom ≫ (pullback C.cover).map f) : g = C.map D E f hf := by
  apply AffineQuasicoherentPullbackFaithful.reconstruction_unique C.ringMap
    C.faithfullyFlat (C.reconstruction E)
  rw [hg, map_reconstruction]

/-- The effective chart map of a compatible identity is the identity. -/
lemma map_identity (hf : D.MapCompatible p D (𝟙 M)) : C.map D D (𝟙 M) hf = 𝟙 _ := by
  symm
  apply C.map_unique D D (𝟙 M) hf
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- Effective chart maps preserve composition whenever the maps are compatible. -/
lemma map_composition (f : M ⟶ N) (g : N ⟶ P)
    (hf : D.MapCompatible p E f) (hg : E.MapCompatible p F g)
    (hfg : D.MapCompatible p F (f ≫ g)) :
    C.map D F (f ≫ g) hfg = C.map D E f hf ≫ C.map E F g hg := by
  symm
  apply C.map_unique D F (f ≫ g) hfg
  rw [Functor.map_comp, Category.assoc, map_reconstruction,
    ← Category.assoc, map_reconstruction, Category.assoc, Functor.map_comp]

end FLT.Mazur.SchemeAffineDescent.Chart
