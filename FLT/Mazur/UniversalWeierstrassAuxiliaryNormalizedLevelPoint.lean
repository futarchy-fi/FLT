/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedUniversalMarking
public import FLT.Mazur.AuxiliaryLevelMappedFaithfulness

/-!
# The actual normalized point of the original level-four scheme

The full normalized marking gives a morphism into the marking equation
scheme. Its universal faithfulness factors that morphism through the original
faithful open. This constructs a scheme point, with its coefficient map and
every marked section, without any affineness assumption on the level scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.UniversalWeierstrass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)
  {T : Over (Spec (.of R))}
  (p : (Over.map (auxiliaryCoefficientBase g)).obj T ⟶ levelFour)

attribute [local irreducible] auxiliaryNormalizedUniversalMarking

/-- The normalized full marking defines an actual point of the marking equation scheme. -/
def auxiliaryNormalizedHomPoint :
    (Over.map (auxiliaryNormalizedCoefficientBase g)).obj T ⟶
      AuxiliaryLevel.homScheme universalGroup (Labels 4) :=
  (AuxiliaryLevel.markingEquiv universalGroup (Labels 4) _).symm
    (auxiliaryNormalizedUniversalMarking g p)

/-- The representing point retains the complete normalized marking. -/
theorem auxiliaryNormalizedHomPoint_marking :
    AuxiliaryLevel.markingOf universalGroup (Labels 4) (auxiliaryNormalizedHomPoint g p) =
      auxiliaryNormalizedUniversalMarking g p :=
  (AuxiliaryLevel.markingEquiv universalGroup (Labels 4) _).apply_symm_apply _

/-- The represented marking is faithful after every nonempty scheme over the original base. -/
theorem auxiliaryNormalizedHomPoint_faithful :
    AuxiliaryLevel.UniversallyFaithful universalGroup (Labels 4)
      (auxiliaryNormalizedHomPoint g p) := by
  apply AuxiliaryLevel.universallyFaithful_of_mapped_tests
    (auxiliaryNormalizedCoefficientBase g) universalGroup (Labels 4) T
  intro U k hU
  let _ := hU
  intro a b hab
  apply auxiliaryNormalizedUniversalMarking_injective g
    ((Over.map (auxiliaryCoefficientBase g)).map k ≫ p)
  apply Over.OverMorphism.ext
  rw [auxiliaryNormalizedUniversalMarking_natural,
    auxiliaryNormalizedUniversalMarking_natural, Over.comp_left, Over.comp_left]
  rw [AuxiliaryLevel.markingOf_comp, AuxiliaryLevel.markingOf_comp,
    auxiliaryNormalizedHomPoint_marking] at hab
  exact congrArg Over.Hom.left hab

/-- Universal faithfulness gives the actual normalized level-four morphism. -/
def auxiliaryNormalizedLevelPoint :
    (Over.map (auxiliaryNormalizedCoefficientBase g)).obj T ⟶ levelFour :=
  AuxiliaryLevel.faithfulLift universalGroup (Labels 4)
    (auxiliaryNormalizedHomPoint g p) (auxiliaryNormalizedHomPoint_faithful g p)

/-- Its inclusion is exactly the point represented by the full normalized marking. -/
@[reassoc] theorem auxiliaryNormalizedLevelPoint_inclusion :
    auxiliaryNormalizedLevelPoint g p ≫ auxiliaryInclusion 4 =
      auxiliaryNormalizedHomPoint g p :=
  AuxiliaryLevel.faithfulLift_inclusion universalGroup (Labels 4) _ _

/-- Every original label is retained by the actual normalized auxiliary point. -/
theorem auxiliaryNormalizedLevelPoint_marking :
    AuxiliaryLevel.markingOf universalGroup (Labels 4)
      (auxiliaryNormalizedLevelPoint g p ≫ auxiliaryInclusion 4) =
        auxiliaryNormalizedUniversalMarking g p := by
  rw [auxiliaryNormalizedLevelPoint_inclusion, auxiliaryNormalizedHomPoint_marking]

/-- Normalize an actual affine auxiliary family into an actual level-four-valued point. -/
def auxiliaryFamilyNormalizedPoint (f : Spec (.of R) ⟶ levelFour.left) :
    Spec (.of R) ⟶ levelFour.left :=
  (auxiliaryNormalizedLevelPoint (auxiliaryPointSections f) (auxiliaryRelativePoint f)).left

/-- The actual normalized point has exactly the normalized coefficient parameter. -/
@[reassoc] theorem auxiliaryFamilyNormalizedPoint_base (f : Spec (.of R) ⟶ levelFour.left) :
    auxiliaryFamilyNormalizedPoint f ≫ levelFour.hom =
      auxiliaryNormalizedCoefficientBase (auxiliaryPointSections f) := by
  have h := (auxiliaryNormalizedLevelPoint
    (auxiliaryPointSections f) (auxiliaryRelativePoint f)).w
  exact h.trans (Category.id_comp _)

end FLT.Mazur.UniversalWeierstrass
