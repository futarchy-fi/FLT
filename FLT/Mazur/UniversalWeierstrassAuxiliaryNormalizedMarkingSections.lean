/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryFullMarkingSections
public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedFrame

/-!
# The complete normalized marking and its original affine frame

Every label of the transported homomorphism is the corresponding normalized
scheme section. In particular its distinguished labels have the proved frame
coordinates, while the identity is the actual infinity section.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)
  {T : Over (Spec (.of R))}
  (p : (Over.map (auxiliaryCoefficientBase g)).obj T ⟶ levelFour)

attribute [local irreducible] auxiliaryPullbackGroup auxiliaryNormalizedGroup
  auxiliaryNormalizationGroupIso auxiliaryCoefficientGroupIso
  auxiliaryFullPullbackMarking auxiliaryFullCoefficientMarking
  integralCurveGroup

/-- The full normalized marking retains the original proper normalization on scheme maps. -/
theorem auxiliaryFullNormalizedMarking_left (a : Labels 4) :
    (auxiliaryFullNormalizedMarking g p a).left =
      (auxiliaryFullPullbackMarking g p a).left ≫
        (auxiliaryNormalizationGroupIso g).inv.hom.hom.hom.left := rfl

/-- Every normalized label commutes with change of test scheme. -/
theorem auxiliaryFullNormalizedMarking_natural {U : Over (Spec (.of R))}
    (k : U ⟶ T) (a : Labels 4) :
    auxiliaryFullNormalizedMarking g ((Over.map (auxiliaryCoefficientBase g)).map k ≫ p) a =
      k ≫ auxiliaryFullNormalizedMarking g p a := by
  apply Over.OverMorphism.ext
  rw [auxiliaryFullNormalizedMarking_left, auxiliaryFullPullbackMarking_natural,
    Over.comp_left, Over.comp_left, auxiliaryFullNormalizedMarking_left, Category.assoc]

attribute [local semireducible] auxiliaryPullbackGroup auxiliaryNormalizedGroup
  auxiliaryNormalizationGroupIso integralCurveGroup auxiliaryFullPullbackMarking

/-- Every nonidentity label of the complete normalized marking is its original affine section. -/
theorem auxiliaryFamilyNormalizedMarking_section (f : Spec (.of R) ⟶ levelFour.left)
    (a : Labels 4) (ha : a ≠ 1) :
    (auxiliaryFamilyNormalizedMarking f a).left =
      auxiliaryNormalizedSection (auxiliaryPointSections f) a ha := by
  rw [auxiliaryFamilyNormalizedMarking, auxiliaryFullNormalizedMarking_left,
    auxiliaryFullPullbackMarking_section f a ha]
  exact auxiliaryPullbackSection_normalize _ a ha

/-- The identity label of the complete normalized marking is the original infinity section. -/
theorem auxiliaryFamilyNormalizedMarking_one (f : Spec (.of R) ⟶ levelFour.left) :
    (auxiliaryFamilyNormalizedMarking f 1).left =
      integralCurveZero (auxiliaryNormalizedEquation (auxiliaryPointSections f)) := by
  rw [map_one]
  change (𝟙 _ ≫ integralCurveZero _) = _
  exact Category.id_comp _

/-- The full normalized marking retains the exact affine evaluation of every nonidentity label. -/
theorem auxiliaryFamilyNormalizedMarking_affine (f : Spec (.of R) ⟶ levelFour.left)
    (a : Labels 4) (ha : a ≠ 1) :
    Spec.map (CommRingCat.ofHom
      (auxiliaryNormalizedEvaluation (auxiliaryPointSections f) a ha).toRingHom) ≫
        integralCurveChart (auxiliaryNormalizedEquation (auxiliaryPointSections f)) 2 =
          (auxiliaryFamilyNormalizedMarking f a).left :=
  (auxiliaryFamilyNormalizedMarking_section f a ha).symm

/-- The complete marking has an affine frame satisfying the four slice equations. -/
theorem auxiliaryFamilyNormalizedMarking_frame (f : Spec (.of R) ⟶ levelFour.left) :
    ∃ e₀ e₁ e₂ : Coordinate (auxiliaryNormalizedEquation (auxiliaryPointSections f)) 2 →ₐ[R] R,
      (Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫ integralCurveChart _ 2 =
        (auxiliaryFamilyNormalizedMarking f frameLabelFirst).left) ∧
      (Spec.map (CommRingCat.ofHom e₁.toRingHom) ≫ integralCurveChart _ 2 =
        (auxiliaryFamilyNormalizedMarking f frameLabelFirst⁻¹).left) ∧
      (Spec.map (CommRingCat.ofHom e₂.toRingHom) ≫ integralCurveChart _ 2 =
        (auxiliaryFamilyNormalizedMarking f frameLabelThird).left) ∧
      e₀ (coord _ 2 0) = 0 ∧ e₀ (coord _ 2 1) = 0 ∧ e₂ (coord _ 2 1) = 0 ∧
        e₂ (coord _ 2 0) = e₁ (coord _ 2 1) := by
  let g := auxiliaryPointSections f
  refine ⟨auxiliaryNormalizedEvaluation g frameLabelFirst frameLabelFirst_ne,
    auxiliaryNormalizedEvaluation g frameLabelFirst⁻¹ (inv_ne_one.mpr frameLabelFirst_ne),
    auxiliaryNormalizedEvaluation g frameLabelThird frameLabelThird_ne,
    auxiliaryFamilyNormalizedMarking_affine f _ _,
    auxiliaryFamilyNormalizedMarking_affine f _ _,
    auxiliaryFamilyNormalizedMarking_affine f _ _,
    (auxiliaryNormalizedEvaluation_first g).1, (auxiliaryNormalizedEvaluation_first g).2,
    (auxiliaryNormalizedEvaluation_third g).2, ?_⟩
  exact (auxiliaryNormalizedEvaluation_third g).1.trans
    (auxiliaryNormalizedEvaluation_inverse g).2.symm

end FLT.Mazur.UniversalWeierstrass
