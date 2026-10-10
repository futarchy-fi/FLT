/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesOverlapLocalHom
public import FLT.Mazur.ModuleSheafRefinementGluing

/-!
# Gluing maps on the concrete relative overlap cover

The common affine refinements of the original tensor charts provide the
geometric refinement covers needed to glue module sheaf morphisms.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

open AffineIteratedPullbackSections ModuleSheafOpenImmersionGluing

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (J : Ideal R) (U V : X.affineOpens)

attribute [local irreducible] Scheme.Modules.pullback modelMap
attribute [local irreducible] modelOverlapChart compositeIso

/-- Refinement-compatible maps on the concrete overlap charts satisfy gluing compatibility. -/
lemma modelOverlapMaps_compatible (M N : (modelOverlap f J U V).Modules)
    (a : ∀ (W : X.affineOpens) (i : W.1 ≤ U.1) (j : W.1 ≤ V.1),
      (pullback (X := (chartCover f J).X W)
        (modelOverlapChart f J i j)).obj M ⟶
        (pullback (X := (chartCover f J).X W)
        (modelOverlapChart f J i j)).obj N)
    (ha : ∀ (W Z : X.affineOpens) (i : W.1 ≤ U.1) (j : W.1 ≤ V.1)
      (k : Z.1 ≤ W.1),
      (pullback (modelMap f J k)).map (a W i j) ≫
          (compositeIso (X := (chartCover f J).X Z)
          (Y := (chartCover f J).X W) (modelMap f J k)
          (modelOverlapChart f J i j)
            (modelOverlapChart f J (k.trans i) (k.trans j))
            (modelOverlapChart_refine f J i j k) N).hom =
        (compositeIso (X := (chartCover f J).X Z)
          (Y := (chartCover f J).X W) (modelMap f J k)
          (modelOverlapChart f J i j)
            (modelOverlapChart f J (k.trans i) (k.trans j))
            (modelOverlapChart_refine f J i j k) M).hom ≫
        a Z (k.trans i) (k.trans j)) :
    Compatible (fun W : {W : X.affineOpens // W.1 ≤ U.1 ∧ W.1 ≤ V.1} ↦
        (chartCover f J).X W.val)
      (fun W ↦ modelOverlapChart f J (W.property.1) (W.property.2))
      (fun W ↦ a W.val (W.property.1) (W.property.2)) := by
  let ι := {W : X.affineOpens // W.1 ≤ U.1 ∧ W.1 ≤ V.1}
  let κ (W T : ι) := {Z : X.affineOpens // Z.1 ≤ W.val.1 ∧ Z.1 ≤ T.val.1}
  let l (W T : ι) (Z : κ W T) : Z.val.1 ≤ W.val.1 := Z.property.1
  let r (W T : ι) (Z : κ W T) : Z.val.1 ≤ T.val.1 := Z.property.2
  let i (W : ι) : W.val.1 ≤ U.1 := W.property.1
  let j (W : ι) : W.val.1 ≤ V.1 := W.property.2
  let _ (W T : ι) (Z : κ W T) : IsOpenImmersion (modelMap f J (l W T Z)) :=
    modelMap_isOpenImmersion f J (l W T Z)
  let _ (W T : ι) (Z : κ W T) : IsOpenImmersion (modelMap f J (r W T Z)) :=
    modelMap_isOpenImmersion f J (r W T Z)
  apply ModuleSheafMorphismGluing.compatible_of_refinement_covers
    (fun W : ι ↦ (modelOverlapChart f J (i W) (j W)).opensRange)
    (fun W ↦ ModuleSheafOpenImmersionLocalHom.localHom
      (modelOverlapChart f J (i W) (j W)) (a W.val (i W) (j W))) κ
    (fun W T Z ↦
      (modelOverlapChart f J ((l W T Z).trans (i W)) ((l W T Z).trans (j W))).opensRange)
    (fun W T Z ↦ ModuleSheafOpenImmersionLocalHom.refinementRange_le_of_eq
      (modelOverlapChart f J (i W) (j W))
      (modelMap f J (l W T Z)) _
      (modelOverlapChart_refine f J (i W) (j W) (l W T Z)))
    (fun W T Z ↦ ModuleSheafOpenImmersionLocalHom.refinementRange_le_of_eq
      (modelOverlapChart f J (i T) (j T))
      (modelMap f J (r W T Z)) _
      ((modelOverlapChart_common_refinement f J
        (i T) (j T) (i W) (j W) (r W T Z) (l W T Z)).trans
        (modelOverlapChart_refine f J (i W) (j W) (l W T Z)))) ?_ ?_
  · intro W T x hx
    obtain ⟨Z, k, m, hz⟩ := modelOverlapChart_exists_refinement f J
      (i W) (j W) (i T) (j T) x hx.1 hx.2
    exact ⟨⟨Z, k, m⟩, hz⟩
  · intro W T Z S hS
    have hSW : S ≤ (modelOverlapChart f J (i W) (j W)).opensRange :=
      hS.trans (ModuleSheafOpenImmersionLocalHom.refinementRange_le_of_eq
        (modelOverlapChart f J (i W) (j W))
        (modelMap f J (l W T Z)) _
        (modelOverlapChart_refine f J (i W) (j W) (l W T Z)))
    have hST : S ≤ (modelOverlapChart f J (i T) (j T)).opensRange :=
      hS.trans (ModuleSheafOpenImmersionLocalHom.refinementRange_le_of_eq
        (modelOverlapChart f J (i T) (j T))
        (modelMap f J (r W T Z)) _
        (modelOverlapChart_refine f J (i T) (j T) (r W T Z)))
    have hl := modelOverlapLocalHom_refine f J U V (i W) (j W) (l W T Z) M N
      (a W.val (i W) (j W)) (a Z.val ((l W T Z).trans (i W)) ((l W T Z).trans (j W)))
      (ha W.val Z.val (i W) (j W) (l W T Z)) S hS hSW
    have hr := modelOverlapLocalHom_refine f J U V (i T) (j T) (r W T Z) M N
      (a T.val (i T) (j T)) (a Z.val ((r W T Z).trans (i T)) ((r W T Z).trans (j T)))
      (ha T.val Z.val (i T) (j T) (r W T Z)) S hS hST
    exact hl.symm.trans hr

end FLT.Mazur.BaseAdicRees
