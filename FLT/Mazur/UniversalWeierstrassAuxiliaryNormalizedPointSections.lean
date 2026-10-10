/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedLevelPoint
public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedCoefficientMaps

/-!
# Every section of the actual normalized auxiliary point

The scheme morphism represented by the full normalized marking projects each
original normalized section through the exact coefficient group comparison.
The affine chart comparison then recovers its actual coordinate functions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (f : Spec (.of R) ⟶ levelFour.left)

/-- Every labeled section of the actual normalized point is its original normalized section. -/
theorem auxiliaryFamilyNormalizedPoint_section (a : Labels 4) :
    auxiliaryFamilyNormalizedPoint f ≫ (auxiliaryMarking 4 a).left =
      (auxiliaryFamilyNormalizedMarking f a).left ≫
        (auxiliaryNormalizedCoefficientGroupIso (auxiliaryPointSections f)).hom.hom.hom.hom.left ≫
          pullback.fst (integralCurveStructure smoothEquation)
            (auxiliaryNormalizedCoefficientBase (auxiliaryPointSections f)) := by
  have h := DFunLike.congr_fun (auxiliaryNormalizedLevelPoint_marking
    (auxiliaryPointSections f) (auxiliaryRelativePoint f)) a
  rw [AuxiliaryLevel.markingOf_comp] at h
  have hl := congrArg Over.Hom.left h
  rw [Over.comp_left, auxiliaryNormalizedUniversalMarking_left,
    auxiliaryNormalizedUniversalPullbackMarking_left, Category.assoc] at hl
  exact hl

/-- The original affine chart section is the evaluation of its actual normalized coordinates. -/
theorem auxiliaryFamilyNormalizedPoint_affine (a : Labels 4) (ha : a ≠ 1) :
    Spec.map (CommRingCat.ofHom
      ((auxiliaryNormalizedEvaluation (auxiliaryPointSections f) a ha).toRingHom.comp
        (auxiliaryNormalizedChartMap (auxiliaryPointSections f) 2))) =
          auxiliaryFamilyNormalizedPoint f ≫ auxiliaryAffineSection a ha := by
  apply (cancel_mono (integralCurveChart smoothEquation 2)).mp
  rw [Category.assoc, auxiliaryAffineSection_inclusion, auxiliaryFamilyNormalizedPoint_section]
  change (Spec.map (CommRingCat.ofHom (auxiliaryNormalizedChartMap _ 2) ≫
    CommRingCat.ofHom (auxiliaryNormalizedEvaluation _ a ha).toRingHom)) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, auxiliaryNormalizedChartMap_chart,
    ← Category.assoc, ← Category.assoc, auxiliaryFamilyNormalizedMarking_affine, Category.assoc]

/-- Pulling back the original auxiliary coordinate algebra gives the exact normalized evaluation. -/
theorem auxiliaryFamilyNormalizedPoint_coordinates (a : Labels 4) (ha : a ≠ 1) :
    (auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f)).comp
      (auxiliaryCoordinateSections a ha) =
        (auxiliaryNormalizedEvaluation (auxiliaryPointSections f) a ha).toRingHom.comp
          (auxiliaryNormalizedChartMap (auxiliaryPointSections f) 2) := by
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective
    ((auxiliaryPointSections_coordinate_spec (auxiliaryFamilyNormalizedPoint f) a ha).trans
      (auxiliaryFamilyNormalizedPoint_affine f a ha).symm))

/-- Every original coordinate function on the new point is its proved normalized value. -/
theorem auxiliaryFamilyNormalizedPoint_coordinate (a : Labels 4) (ha : a ≠ 1) (i : Fin 3) :
    auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f) (auxiliaryCoordinate a ha i) =
      auxiliaryNormalizedEvaluation (auxiliaryPointSections f) a ha
        (coord (auxiliaryNormalizedEquation (auxiliaryPointSections f)) 2 i) := by
  have h := DFunLike.congr_fun (auxiliaryFamilyNormalizedPoint_coordinates f a ha)
    (coord smoothEquation 2 i)
  exact h.trans (congrArg (auxiliaryNormalizedEvaluation (auxiliaryPointSections f) a ha)
    (auxiliaryNormalizedChartMap_coord (auxiliaryPointSections f) 2 i))

end FLT.Mazur.UniversalWeierstrass
