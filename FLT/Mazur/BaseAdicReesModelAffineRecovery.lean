/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelFullOverlapRecovery
public import FLT.Mazur.ModuleSheafChartRecoveryRefinement

/-!
# Original affine restrictions of recovered model charts

Pull back the descended overlap equation to each original common affine
chart. Coherent path normalization recovers the original affine coefficient
comparison, with the original chart recovery maps on both sides.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local instance] spectrumSpaceMap_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback spectrumSheaf
attribute [local irreducible] spectrumImageSheaf spectrumChartImageTransition

attribute [local irreducible] spectrumSpaceMap spectrumOverlapSheafIso

open SheafPullbackPathComparison ModuleSheafOverlapImageTransition
open ModuleSheafMorphismGluing ModuleSheafOpenImmersionLocalHom

/-- Further restriction of chart recovery commutes with path normalization. -/
lemma spectrumModelRecoveryAlong_refine (U : X.affineOpens) {Y Z : Scheme.{u}}
    (c : Z ⟶ Y) (a : Y ⟶ modelSpectrum f J U) (r : Y ⟶ relativeSpace f J)
    (b : Z ⟶ modelSpectrum f J U) (t : Z ⟶ relativeSpace f J)
    (ha : a ≫ spectrumSpaceMap f J U = r) (hb : c ≫ a = b)
    (hc : c ≫ r = t) (ht : b ≫ spectrumSpaceMap f J U = t) :
    (comparison c r t hc).inv.app (spectrumDescendedSheaf f J M) ≫
      (pullback c).map (spectrumModelRecoveryAlong f J M U a r ha).hom ≫
        (comparison c a b hb).hom.app (spectrumSheaf f J M U) =
      (spectrumModelRecoveryAlong f J M U b t ht).hom := by
  unfold spectrumModelRecoveryAlong
  exact ModuleSheafChartRecoveryRefinement.recovery_refine c a (spectrumSpaceMap f J U)
    r b t ha hb hc ht (spectrumDescendedSheaf f J M) (spectrumSheaf f J M U)
    (spectrumModelChartRecovery f J M U).hom

/-- The original model chart restricted through an original affine inclusion. -/
def spectrumModelAffineRecovery {U W : X.affineOpens} (h : W.1 ≤ U.1) :
    (pullback (spectrumSpaceMap f J W)).obj (spectrumDescendedSheaf f J M) ≅
      (pullback (spectrumMap f J h)).obj (spectrumSheaf f J M U) :=
  spectrumModelRecoveryAlong f J M U (spectrumMap f J h) (spectrumSpaceMap f J W)
    (spectrumMap_chart f J h)

/-- On a common original affine chart, recovered sheaves obey the original coefficient map. -/
lemma spectrumModelAffineRecovery_overlap {U V W : X.affineOpens}
    (h : W.1 ≤ U.1) (k : W.1 ≤ V.1) :
    (spectrumModelAffineRecovery f J M h).hom ≫ (spectrumAffineOverlap f J M h k).hom =
      (spectrumModelAffineRecovery f J M k).hom := by
  let c := spectrumOverlapChart f J h k
  let r := spectrumOverlapToSpace f J U V
  let t := spectrumSpaceMap f J W
  have hc : c ≫ r = t := by
    dsimp only [c, r, t, spectrumOverlapToSpace]
    rw [← Category.assoc, spectrumOverlapChart_first, spectrumMap_chart]
  let Cp := comparison c (spectrumOverlapFirst f J U V) (spectrumMap f J h)
    (spectrumOverlapChart_first f J h k)
  let Cq := comparison c (spectrumOverlapSecond f J U V) (spectrumMap f J k)
    (spectrumOverlapChart_second f J h k)
  let H := (comparison c r t hc).inv.app (spectrumDescendedSheaf f J M)
  let A := (spectrumModelRecoveryAlong f J M U (spectrumOverlapFirst f J U V) r rfl).hom
  let B := (spectrumModelRecoveryAlong f J M V (spectrumOverlapSecond f J U V) r
    (spectrumOverlap_condition f J U V).symm).hom
  have he : (pullback c).map A ≫ (pullback c).map
      (spectrumOverlapSheafIso f J M U V).hom = (pullback c).map B := by
    rw [← Functor.map_comp, spectrumModelRecoveryAlong_overlap]
  have ht : (pullback c).map (spectrumOverlapSheafIso f J M U V).hom ≫
      Cq.hom.app (spectrumSheaf f J M V) =
        Cp.hom.app (spectrumSheaf f J M U) ≫ (spectrumAffineOverlap f J M h k).hom := by
    rw [← spectrumOverlapAffineMap_eq]
    simp only [spectrumOverlapAffineMap, Cp, Cq, c,
      Iso.hom_inv_id_app_assoc]
  have hp : H ≫ (pullback c).map A ≫ Cp.hom.app (spectrumSheaf f J M U) =
      (spectrumModelAffineRecovery f J M h).hom :=
    spectrumModelRecoveryAlong_refine f J M U c _ r _ t rfl
      (spectrumOverlapChart_first f J h k) hc (spectrumMap_chart f J h)
  have hq : H ≫ (pullback c).map B ≫ Cq.hom.app (spectrumSheaf f J M V) =
      (spectrumModelAffineRecovery f J M k).hom :=
    spectrumModelRecoveryAlong_refine f J M V c _ r _ t
      (spectrumOverlap_condition f J U V).symm
      (spectrumOverlapChart_second f J h k) hc (spectrumMap_chart f J k)
  rw [← hp, Category.assoc, Category.assoc, ← ht,
    ← Category.assoc ((pullback c).map A), he]
  exact hq

end FLT.Mazur.BaseAdicRees
