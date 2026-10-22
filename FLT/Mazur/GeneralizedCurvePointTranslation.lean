/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedEllipticCurve
public import FLT.Mazur.GroupActionPointTranslation
public import FLT.Mazur.GroupObjectPointTranslation

/-!
# Translating the whole original generalized curve

Every point of the given smooth group acts by an isomorphism of the whole
curve. Its restriction is translation for the pre-existing group law.
-/

@[expose] public noncomputable section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
variable {S : AlgebraicGeometry.Scheme} (E : GeneralizedEllipticCurve S)

/-- The defining original action, as an ordinary categorical action object. -/
abbrev originalActionObj : ModObj E.group E.curve where
  smul := E.act
  one_smul := E.unit_act
  mul_smul := E.assoc_act

attribute [local instance] originalActionObj

/-- The actual group point translates the entire original curve. -/
def pointTranslationIso (p : 𝟙_ (Over S) ⟶ E.group) : E.curve ≅ E.curve :=
  GroupActionPointTranslation.translationIso p

/-- The whole translation is specialization of the given action at the given point. -/
theorem pointTranslationIso_hom (p : 𝟙_ (Over S) ⟶ E.group) :
    (E.pointTranslationIso p).hom = (λ_ E.curve).inv ≫ p ▷ E.curve ≫ E.act :=
  GroupActionPointTranslation.translation_eq p

/-- Whole-curve translation restricts to the original smooth-group translation. -/
@[reassoc] theorem inclusion_pointTranslation (p : 𝟙_ (Over S) ⟶ E.group) :
    E.inclusion ≫ (E.pointTranslationIso p).hom =
      (GroupObjectPointTranslation.translationIso p).hom ≫ E.inclusion := by
  change E.inclusion ≫ GroupActionPointTranslation.translation p =
    GroupObjectPointTranslation.translation p ≫ E.inclusion
  simp only [GroupActionPointTranslation.translation, GroupObjectPointTranslation.translation,
    Hom.smul_def, Hom.mul_def, Category.assoc, ← E.action_inclusion]
  simp only [comp_lift_assoc, comp_toUnit_assoc, Category.comp_id,
    ← id_tensorHom, lift_map_assoc, Category.id_comp]
  rfl

/-- The original identity is translated to the specified actual smooth point. -/
@[reassoc] theorem identitySection_pointTranslation (p : 𝟙_ (Over S) ⟶ E.group) :
    E.identitySection ≫ (E.pointTranslationIso p).hom = p ≫ E.inclusion := by
  rw [identitySection, Category.assoc, inclusion_pointTranslation,
    ← Category.assoc, MonObj.one_eq_one]
  exact congrArg (· ≫ E.inclusion) (GroupObjectPointTranslation.one_translation p)

end FLT.Mazur.GeneralizedEllipticCurve
