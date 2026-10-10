/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeMarkingSections

/-!
# Every coordinate of the normalized arbitrary scheme family

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

variable {T : Scheme} (f : T ⟶ levelFour.left)

/-- Every labeled section of the actual normalized point is its original normalized section. -/
theorem auxiliarySchemeNormalizedPoint_section (a : Labels 4) :
    auxiliarySchemeNormalizedPoint f ≫ (auxiliaryMarking 4 a).left =
      (auxiliaryFullNormalizedMarking f.appTop.hom (auxiliarySchemeRelativePoint f) a).left ≫
        (auxiliaryNormalizedCoefficientGroupIso f.appTop.hom).hom.hom.hom.hom.left ≫
          pullback.fst (integralCurveStructure smoothEquation)
            (auxiliaryNormalizedCoefficientBase f.appTop.hom) := by
  have h := DFunLike.congr_fun (auxiliaryNormalizedLevelPoint_marking
    f.appTop.hom (auxiliarySchemeRelativePoint f)) a
  rw [AuxiliaryLevel.markingOf_comp] at h
  have hl := congrArg Over.Hom.left h
  rw [Over.comp_left, auxiliaryNormalizedUniversalMarking_left,
    auxiliaryNormalizedUniversalPullbackMarking_left, Category.assoc] at hl
  exact hl

/-- The original affine chart section is the evaluation of its actual normalized coordinates. -/
theorem auxiliarySchemeNormalizedPoint_affine (a : Labels 4) (ha : a ≠ 1) :
    T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      ((auxiliaryNormalizedEvaluation f.appTop.hom a ha).toRingHom.comp
        (auxiliaryNormalizedChartMap f.appTop.hom 2))) =
          auxiliarySchemeNormalizedPoint f ≫ auxiliaryAffineSection a ha := by
  apply (cancel_mono (integralCurveChart smoothEquation 2)).mp
  simp only [Category.assoc]
  rw [auxiliaryAffineSection_inclusion, auxiliarySchemeNormalizedPoint_section]
  change T.toSpecΓ ≫ (Spec.map (CommRingCat.ofHom (auxiliaryNormalizedChartMap _ 2) ≫
    CommRingCat.ofHom (auxiliaryNormalizedEvaluation _ a ha).toRingHom)) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, auxiliaryNormalizedChartMap_chart]
  rw [← auxiliarySchemeFullNormalizedMarking_affine f a ha]
  simp only [Category.assoc]

/-- Pulling back the original auxiliary coordinate algebra gives the exact normalized evaluation. -/
theorem auxiliarySchemeNormalizedPoint_coordinates (a : Labels 4) (ha : a ≠ 1) :
    (auxiliarySchemeNormalizedPoint f).appTop.hom.comp
      (auxiliaryCoordinateSections a ha) =
        (auxiliaryNormalizedEvaluation f.appTop.hom a ha).toRingHom.comp
          (auxiliaryNormalizedChartMap f.appTop.hom 2) := by
  have h := congrArg Scheme.Hom.appTop (auxiliarySchemeNormalizedPoint_affine f a ha)
  have he := congrArg (fun k =>
    (Scheme.ΓSpecIso (.of (Coordinate smoothEquation 2))).inv ≫ k) h
  rw [Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Scheme.toSpecΓ_appTop,
    Iso.inv_hom_id, Category.comp_id, Scheme.Hom.comp_appTop] at he
  exact (congrArg CommRingCat.Hom.hom he).symm

/-- Every original coordinate function on the new point is its proved normalized value. -/
theorem auxiliarySchemeNormalizedPoint_coordinate (a : Labels 4) (ha : a ≠ 1) (i : Fin 3) :
    (auxiliarySchemeNormalizedPoint f).appTop.hom (auxiliaryCoordinate a ha i) =
      auxiliaryNormalizedEvaluation f.appTop.hom a ha
        (coord (auxiliaryNormalizedEquation f.appTop.hom) 2 i) := by
  have h := DFunLike.congr_fun (auxiliarySchemeNormalizedPoint_coordinates f a ha)
    (coord smoothEquation 2 i)
  exact h.trans (congrArg (auxiliaryNormalizedEvaluation f.appTop.hom a ha)
    (auxiliaryNormalizedChartMap_coord f.appTop.hom 2 i))

end FLT.Mazur.UniversalWeierstrass
