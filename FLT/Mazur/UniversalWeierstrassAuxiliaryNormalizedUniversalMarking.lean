/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupMarkingBaseChangeInverse
public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedParameter
public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedMarkingSections

/-!
# The full normalized marking on the original universal group

Transport every label through the normalized coefficient comparison and the
inverse pullback adjunction. The resulting marking is faithful on nonempty
test schemes and natural in every test scheme over the coefficient ring.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)
  {T : Over (Spec (.of R))}
  (p : (Over.map (auxiliaryCoefficientBase g)).obj T ⟶ levelFour)

attribute [local irreducible] auxiliaryNormalizedGroup auxiliaryNormalizedCoefficientGroupIso
  auxiliaryFullNormalizedMarking integralCurveGroup

/-- The full normalized marking in the pullback of the original universal group. -/
def auxiliaryNormalizedUniversalPullbackMarking :
    Labels 4 →* (T ⟶ (auxiliaryNormalizedUniversalPullbackGroup g).X) :=
  GroupMarkingTransport.transport (auxiliaryNormalizedGroup g)
    (auxiliaryNormalizedUniversalPullbackGroup g) (auxiliaryNormalizedCoefficientGroupIso g)
    (auxiliaryFullNormalizedMarking g p)

/-- The coefficient comparison preserves faithfulness of all sixteen labels. -/
theorem auxiliaryNormalizedUniversalPullbackMarking_injective [Nonempty T.left] :
    Function.Injective (auxiliaryNormalizedUniversalPullbackMarking g p) := by
  unfold auxiliaryNormalizedUniversalPullbackMarking
  apply (GroupMarkingTransport.transport_injective_iff _ _ _ _).mpr
  exact auxiliaryFullNormalizedMarking_injective g p

/-- Each comparison label retains the actual normalized section and coefficient map. -/
theorem auxiliaryNormalizedUniversalPullbackMarking_left (a : Labels 4) :
    (auxiliaryNormalizedUniversalPullbackMarking g p a).left =
      (auxiliaryFullNormalizedMarking g p a).left ≫
        (auxiliaryNormalizedCoefficientGroupIso g).hom.hom.hom.hom.left := rfl

/-- The complete comparison marking commutes with every change of test scheme. -/
theorem auxiliaryNormalizedUniversalPullbackMarking_natural {U : Over (Spec (.of R))}
    (k : U ⟶ T) (a : Labels 4) :
    auxiliaryNormalizedUniversalPullbackMarking g
      ((Over.map (auxiliaryCoefficientBase g)).map k ≫ p) a =
        k ≫ auxiliaryNormalizedUniversalPullbackMarking g p a := by
  apply Over.OverMorphism.ext
  rw [auxiliaryNormalizedUniversalPullbackMarking_left,
    auxiliaryFullNormalizedMarking_natural, Over.comp_left, Over.comp_left,
    auxiliaryNormalizedUniversalPullbackMarking_left, Category.assoc]

attribute [local semireducible] integralCurveGroup

/-- The normalized marking as actual sections of the original universal group. -/
def auxiliaryNormalizedUniversalMarking :
    Labels 4 →* ((Over.map (auxiliaryNormalizedCoefficientBase g)).obj T ⟶ universalGroup) :=
  (GroupMarkingBaseChange.pointsMulEquiv (auxiliaryNormalizedCoefficientBase g)
    universalGroup T).symm.toMonoidHom.comp (auxiliaryNormalizedUniversalPullbackMarking g p)

/-- Returning through the pullback adjunction preserves faithfulness of the entire marking. -/
theorem auxiliaryNormalizedUniversalMarking_injective [Nonempty T.left] :
    Function.Injective (auxiliaryNormalizedUniversalMarking g p) :=
  (GroupMarkingBaseChange.pointsMulEquiv (auxiliaryNormalizedCoefficientBase g)
    universalGroup T).symm.injective.comp
      (auxiliaryNormalizedUniversalPullbackMarking_injective g p)

/-- Each universal label is the original first projection of its full pullback marking. -/
theorem auxiliaryNormalizedUniversalMarking_left (a : Labels 4) :
    (auxiliaryNormalizedUniversalMarking g p a).left =
      (auxiliaryNormalizedUniversalPullbackMarking g p a).left ≫
        Limits.pullback.fst universalGroup.hom (auxiliaryNormalizedCoefficientBase g) :=
  GroupMarkingBaseChange.pointsMulEquiv_symm_left _ _ T _

/-- The universal marking is natural in all test schemes over the coefficient ring. -/
theorem auxiliaryNormalizedUniversalMarking_natural {U : Over (Spec (.of R))}
    (k : U ⟶ T) (a : Labels 4) :
    auxiliaryNormalizedUniversalMarking g
      ((Over.map (auxiliaryCoefficientBase g)).map k ≫ p) a =
        (Over.map (auxiliaryNormalizedCoefficientBase g)).map k ≫
          auxiliaryNormalizedUniversalMarking g p a := by
  apply Over.OverMorphism.ext
  rw [auxiliaryNormalizedUniversalMarking_left,
    auxiliaryNormalizedUniversalPullbackMarking_natural, Over.comp_left, Over.comp_left,
    auxiliaryNormalizedUniversalMarking_left, Category.assoc]
  rfl

end FLT.Mazur.UniversalWeierstrass
