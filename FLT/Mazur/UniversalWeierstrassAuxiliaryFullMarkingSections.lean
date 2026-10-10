/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryPointCoordinates
public import FLT.Mazur.UniversalWeierstrassAuxiliaryFullNormalizedMarking

/-!
# The full auxiliary marking retains the original scheme sections

The actual coefficient comparison identifies each nonidentity label with its
original affine section. The zero label is the original infinity section.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- The auxiliary group comparison retains the original Cartesian coefficient map. -/
theorem auxiliaryCoefficientGroupIso_hom :
    let _ : Algebra ParameterRing R := (auxiliaryCoefficientHom g).toAlgebra
    (auxiliaryCoefficientGroupIso g).hom.hom.hom.hom.left =
      (integralCurveCoefficientBaseChangeIso smoothEquation).hom := rfl

/-- Its first projection is the actual coefficient morphism. -/
theorem auxiliaryCoefficientGroupIso_fst :
    let _ : Algebra ParameterRing R := (auxiliaryCoefficientHom g).toAlgebra
    (auxiliaryCoefficientGroupIso g).hom.hom.hom.hom.left ≫
      pullback.fst (integralCurveStructure smoothEquation) (auxiliaryCoefficientBase g) =
        integralCoefficientMorphism (S := R) smoothEquation := by
  dsimp only
  let _ : Algebra ParameterRing R := (auxiliaryCoefficientHom g).toAlgebra
  rw [auxiliaryCoefficientGroupIso_hom]
  exact integralCurveCoefficientBaseChangeIso_fst smoothEquation

variable {T : Over (Spec (.of R))}
  (p : (Over.map (auxiliaryCoefficientBase g)).obj T ⟶ levelFour)

/-- Projecting the entire original coefficient marking recovers every original label. -/
theorem auxiliaryFullCoefficientMarking_fst (a : Labels 4) :
    (auxiliaryFullCoefficientMarking g p a).left ≫
      pullback.fst (integralCurveStructure smoothEquation) (auxiliaryCoefficientBase g) =
        p.left ≫ (auxiliaryMarking 4 a).left := by
  exact (GroupMarkingBaseChange.marking_fst (auxiliaryCoefficientBase g)
    (integralCurveGroup smoothEquation smoothEquation_discriminant).X T
    (AuxiliaryLevel.markingOf universalGroup (Labels 4) (p ≫ auxiliaryInclusion 4)) a).trans
      (congrArg Over.Hom.left
        (AuxiliaryLevel.markingOf_comp universalGroup (Labels 4) p (auxiliaryInclusion 4) a))

attribute [local irreducible] auxiliaryPullbackGroup auxiliaryNormalizedGroup
  auxiliaryNormalizationGroupIso auxiliaryCoefficientGroupIso

/-- The complete marking is transported by the actual inverse coefficient map. -/
theorem auxiliaryFullPullbackMarking_apply (a : Labels 4) :
    auxiliaryFullPullbackMarking g p a = auxiliaryFullCoefficientMarking g p a ≫
      (auxiliaryCoefficientGroupIso g).inv.hom.hom.hom := rfl

/-- Following the transported label by the coefficient isomorphism returns the original. -/
theorem auxiliaryFullPullbackMarking_compare (a : Labels 4) :
    auxiliaryFullPullbackMarking g p a ≫ (auxiliaryCoefficientGroupIso g).hom.hom.hom.hom =
      auxiliaryFullCoefficientMarking g p a := by
  rw [auxiliaryFullPullbackMarking_apply, Category.assoc]
  have h : (auxiliaryCoefficientGroupIso g).inv.hom.hom.hom ≫
      (auxiliaryCoefficientGroupIso g).hom.hom.hom.hom = 𝟙 _ :=
    congrArg (fun k => k.hom.hom.hom) (auxiliaryCoefficientGroupIso g).inv_hom_id
  rw [h, Category.comp_id]

attribute [local semireducible] auxiliaryPullbackGroup auxiliaryCoefficientGroupIso

/-- Every full label projects to exactly the original auxiliary section. -/
theorem auxiliaryFullPullbackMarking_coefficient (a : Labels 4) :
    let _ : Algebra ParameterRing R := (auxiliaryCoefficientHom g).toAlgebra
    (auxiliaryFullPullbackMarking g p a).left ≫
      integralCoefficientMorphism (S := R) smoothEquation =
        p.left ≫ (auxiliaryMarking 4 a).left := by
  dsimp only
  let _ : Algebra ParameterRing R := (auxiliaryCoefficientHom g).toAlgebra
  rw [← auxiliaryCoefficientGroupIso_fst g, ← Category.assoc, ← Over.comp_left,
    auxiliaryFullPullbackMarking_compare, auxiliaryFullCoefficientMarking_fst]

/-- The complete marking's nonidentity sections are the original affine auxiliary sections. -/
theorem auxiliaryFullPullbackMarking_section (f : Spec (.of R) ⟶ levelFour.left)
    (a : Labels 4) (ha : a ≠ 1) :
    (auxiliaryFullPullbackMarking (auxiliaryPointSections f) (auxiliaryRelativePoint f) a).left =
      auxiliaryPullbackSection (auxiliaryPointSections f) a ha := by
  let _ : Algebra ParameterRing R :=
    (auxiliaryCoefficientHom (auxiliaryPointSections f)).toAlgebra
  apply (integralCoefficient_isPullback (S := R) smoothEquation).hom_ext
  · exact (auxiliaryFullPullbackMarking_coefficient _ _ a).trans
      (auxiliaryPullbackSection_coefficient f a ha).symm
  · exact (auxiliaryFullPullbackMarking _ (auxiliaryRelativePoint f) a).w.trans
      (auxiliaryPullbackSection_structure (auxiliaryPointSections f) a ha).symm

/-- The identity label remains the original zero section on the actual auxiliary cubic. -/
theorem auxiliaryFullPullbackMarking_one (f : Spec (.of R) ⟶ levelFour.left) :
    (auxiliaryFullPullbackMarking (auxiliaryPointSections f) (auxiliaryRelativePoint f) 1).left =
      integralCurveZero (auxiliaryPullbackEquation (auxiliaryPointSections f)) := by
  rw [map_one]
  change (𝟙 _ ≫ integralCurveZero _) = _
  exact Category.id_comp _

end FLT.Mazur.UniversalWeierstrass
