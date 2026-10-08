/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesOverlapRefinementCover
public import FLT.Mazur.ModuleSheafLocalHomComparison

/-!
# Local linear maps on relative overlap refinements

A pullback comparison equation on an affine refinement gives equality of
local maps on every subopen of its image in the full relative overlap.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

open AffineIteratedPullbackSections ModuleSheafOpenImmersionLocalHom
open ModuleSheafMorphismGluing

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (J : Ideal R) (U V : X.affineOpens)

attribute [local irreducible] Scheme.Modules.pullback modelMap
attribute [local irreducible] modelOverlapChart compositeIso

/-- A concrete affine refinement equation identifies the induced local linear maps. -/
lemma modelOverlapLocalHom_refine {W Z : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : Z.1 ≤ W.1)
    (M N : (modelOverlap f J U V).Modules)
    (a : (pullback (X := (chartCover f J).X W)
        (modelOverlapChart f J i j)).obj M ⟶
      (pullback (X := (chartCover f J).X W)
        (modelOverlapChart f J i j)).obj N)
    (b : (pullback (X := (chartCover f J).X Z)
        (modelOverlapChart f J (k.trans i) (k.trans j))).obj M ⟶
      (pullback (X := (chartCover f J).X Z)
        (modelOverlapChart f J (k.trans i) (k.trans j))).obj N)
    (hab : (pullback (modelMap f J k)).map a ≫
        (compositeIso (X := (chartCover f J).X Z)
          (Y := (chartCover f J).X W) (modelMap f J k)
          (modelOverlapChart f J i j)
          (modelOverlapChart f J (k.trans i) (k.trans j))
          (modelOverlapChart_refine f J i j k) N).hom =
      (compositeIso (X := (chartCover f J).X Z)
          (Y := (chartCover f J).X W) (modelMap f J k)
          (modelOverlapChart f J i j)
          (modelOverlapChart f J (k.trans i) (k.trans j))
          (modelOverlapChart_refine f J i j k) M).hom ≫ b)
    (S : (modelOverlap f J U V).Opens)
    (hS : S ≤ (modelOverlapChart f J (k.trans i) (k.trans j)).opensRange)
    (hW : S ≤ (modelOverlapChart f J i j).opensRange) :
    localApp (localHom (Y := (chartCover f J).X Z)
      (modelOverlapChart f J (k.trans i) (k.trans j)) b) hS =
    localApp (localHom (Y := (chartCover f J).X W)
      (modelOverlapChart f J i j) a) hW := by
  let _ := modelMap_isOpenImmersion f J k
  exact localHom_refine_of_eq (Y := (chartCover f J).X W)
    (Z := (chartCover f J).X Z)
    (modelOverlapChart f J i j) (modelMap f J k)
    (modelOverlapChart f J (k.trans i) (k.trans j))
    (modelOverlapChart_refine f J i j k) a b hab S hS hW

end FLT.Mazur.BaseAdicRees
