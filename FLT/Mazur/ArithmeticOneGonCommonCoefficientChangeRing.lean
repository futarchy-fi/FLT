/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonCommonCoefficientTower

/-!
# Changing the common coefficient ring of full arithmetic comparisons

The actual coefficient tower maps conjugate the common-ring comparison to its
comparison after a further coefficient extension, preserving the full curve action.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonGeneralizedCurve
open OneGonSmoothing CharacterSchemeBaseChange GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (A B C D : Type) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A C] [Algebra B C] [Algebra C D] [Algebra A D] [Algebra B D]
  [IsScalarTower A C D] [IsScalarTower B C D]
  (a : A) (b : B) (ha : IsUnit (1 + 432 * a)) (hb : IsUnit (1 + 432 * b))
  (e : algebraMap A C a = algebraMap B C b)

/-- The full comparison is natural under an actual extension of the common coefficient ring. -/
@[reassoc] theorem commonCoefficientIso_changeRing :
    ((curve a ha).baseChangeCompEqIso (baseMap A C) (baseMap C D) (baseMap A D)
      (coefficientTower_baseMap A C D).symm).hom ≫
        (baseChangeFunctor (baseMap C D)).map (commonCoefficientIso a b ha hb e).hom =
    (commonCoefficientIso a b ha hb
      (commonCoefficient_parameter_tower A B C D a b e)).hom ≫
        ((curve b hb).baseChangeCompEqIso (baseMap B C) (baseMap C D) (baseMap B D)
          (coefficientTower_baseMap B C D).symm).hom := by
  apply (cancel_epi (coefficientIso (S := D) a ha).hom).mp
  rw [← Category.assoc, ← coefficientIso_tower, commonCoefficientIso_tower_recovery,
    ← Category.assoc, commonCoefficientIso_recovery, Category.assoc, ← coefficientIso_tower]

end FLT.Mazur.ArithmeticOneGonGeneralizedCurve
