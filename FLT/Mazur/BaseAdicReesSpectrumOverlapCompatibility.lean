/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesOverlapCompatibility
public import FLT.Mazur.BaseAdicReesSpectrumOverlap

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
attribute [local semireducible] modelSpectrum

/-- Both paths from a common affine refinement have the same overlap map. -/
lemma spectrumOverlapChart_common_refinement {W T Z : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (a : T.1 ≤ U.1) (b : T.1 ≤ V.1)
    (k : Z.1 ≤ W.1) (l : Z.1 ≤ T.1) :
    spectrumMap f J k ≫ spectrumOverlapChart f J i j =
      spectrumMap f J l ≫ spectrumOverlapChart f J a b := by
  rw [spectrumOverlapChart_refine, spectrumOverlapChart_refine]

/-- Refinement-compatible maps on the concrete overlap charts satisfy gluing compatibility. -/
lemma spectrumOverlapMaps_compatible (M N : (modelOverlap f J U V).Modules)
    (a : ∀ (W : X.affineOpens) (i : W.1 ≤ U.1) (j : W.1 ≤ V.1),
      (pullback (X := modelSpectrum f J W)
        (spectrumOverlapChart f J i j)).obj M ⟶
        (pullback (X := modelSpectrum f J W)
        (spectrumOverlapChart f J i j)).obj N)
    (ha : ∀ (W Z : X.affineOpens) (i : W.1 ≤ U.1) (j : W.1 ≤ V.1)
      (k : Z.1 ≤ W.1),
      (pullback (spectrumMap f J k)).map (a W i j) ≫
          (compositeIso (X := modelSpectrum f J Z)
          (Y := modelSpectrum f J W) (spectrumMap f J k)
          (spectrumOverlapChart f J i j)
            (spectrumOverlapChart f J (k.trans i) (k.trans j))
            (spectrumOverlapChart_refine f J i j k) N).hom =
        (compositeIso (X := modelSpectrum f J Z)
          (Y := modelSpectrum f J W) (spectrumMap f J k)
          (spectrumOverlapChart f J i j)
            (spectrumOverlapChart f J (k.trans i) (k.trans j))
            (spectrumOverlapChart_refine f J i j k) M).hom ≫
        a Z (k.trans i) (k.trans j)) :
    Compatible (fun W : {W : X.affineOpens // W.1 ≤ U.1 ∧ W.1 ≤ V.1} ↦
        modelSpectrum f J W.val)
      (fun W ↦ spectrumOverlapChart f J (W.property.1) (W.property.2))
      (fun W ↦ a W.val (W.property.1) (W.property.2)) := by
  let ι := {W : X.affineOpens // W.1 ≤ U.1 ∧ W.1 ≤ V.1}
  let κ (W T : ι) := {Z : X.affineOpens // Z.1 ≤ W.val.1 ∧ Z.1 ≤ T.val.1}
  let l (W T : ι) (Z : κ W T) : Z.val.1 ≤ W.val.1 := Z.property.1
  let r (W T : ι) (Z : κ W T) : Z.val.1 ≤ T.val.1 := Z.property.2
  let i (W : ι) : W.val.1 ≤ U.1 := W.property.1
  let j (W : ι) : W.val.1 ≤ V.1 := W.property.2
  let _ (W T : ι) (Z : κ W T) : IsOpenImmersion (spectrumMap f J (l W T Z)) :=
    spectrumMap_isOpenImmersion f J (l W T Z)
  let _ (W T : ι) (Z : κ W T) : IsOpenImmersion (spectrumMap f J (r W T Z)) :=
    spectrumMap_isOpenImmersion f J (r W T Z)
  apply ModuleSheafMorphismGluing.compatible_of_refinement_covers
    (fun W : ι ↦ (spectrumOverlapChart f J (i W) (j W)).opensRange)
    (fun W ↦ ModuleSheafOpenImmersionLocalHom.localHom
      (spectrumOverlapChart f J (i W) (j W)) (a W.val (i W) (j W))) κ
    (fun W T Z ↦
      (spectrumOverlapChart f J ((l W T Z).trans (i W)) ((l W T Z).trans (j W))).opensRange)
    (fun W T Z ↦ ModuleSheafOpenImmersionLocalHom.refinementRange_le_of_eq
      (spectrumOverlapChart f J (i W) (j W))
      (spectrumMap f J (l W T Z)) _
      (spectrumOverlapChart_refine f J (i W) (j W) (l W T Z)))
    (fun W T Z ↦ ModuleSheafOpenImmersionLocalHom.refinementRange_le_of_eq
      (spectrumOverlapChart f J (i T) (j T))
      (spectrumMap f J (r W T Z)) _
      ((spectrumOverlapChart_common_refinement f J U V
        (i T) (j T) (i W) (j W) (r W T Z) (l W T Z)).trans
        (spectrumOverlapChart_refine f J (i W) (j W) (l W T Z)))) ?_ ?_
  · intro W T x hx
    obtain ⟨Z, k, m, hz⟩ := modelOverlapChart_exists_refinement f J
      (i W) (j W) (i T) (j T) x hx.1 hx.2
    exact ⟨⟨Z, k, m⟩, hz⟩
  · intro W T Z S hS
    have hSW : S ≤ (spectrumOverlapChart f J (i W) (j W)).opensRange :=
      hS.trans (ModuleSheafOpenImmersionLocalHom.refinementRange_le_of_eq
        (spectrumOverlapChart f J (i W) (j W))
        (spectrumMap f J (l W T Z)) _
        (spectrumOverlapChart_refine f J (i W) (j W) (l W T Z)))
    have hST : S ≤ (spectrumOverlapChart f J (i T) (j T)).opensRange :=
      hS.trans (ModuleSheafOpenImmersionLocalHom.refinementRange_le_of_eq
        (spectrumOverlapChart f J (i T) (j T))
        (spectrumMap f J (r W T Z)) _
        (spectrumOverlapChart_refine f J (i T) (j T) (r W T Z)))
    have hl := ModuleSheafOpenImmersionLocalHom.localHom_refine_of_eq
      (spectrumOverlapChart f J (i W) (j W)) (spectrumMap f J (l W T Z))
      (spectrumOverlapChart f J ((l W T Z).trans (i W)) ((l W T Z).trans (j W)))
      (spectrumOverlapChart_refine f J (i W) (j W) (l W T Z))
      (a W.val (i W) (j W)) (a Z.val ((l W T Z).trans (i W)) ((l W T Z).trans (j W)))
      (ha W.val Z.val (i W) (j W) (l W T Z)) S hS hSW
    have hr := ModuleSheafOpenImmersionLocalHom.localHom_refine_of_eq
      (spectrumOverlapChart f J (i T) (j T)) (spectrumMap f J (r W T Z))
      (spectrumOverlapChart f J ((r W T Z).trans (i T)) ((r W T Z).trans (j T)))
      (spectrumOverlapChart_refine f J (i T) (j T) (r W T Z))
      (a T.val (i T) (j T)) (a Z.val ((r W T Z).trans (i T)) ((r W T Z).trans (j T)))
      (ha T.val Z.val (i T) (j T) (r W T Z)) S hS hST
    exact hl.symm.trans hr

end FLT.Mazur.BaseAdicRees
