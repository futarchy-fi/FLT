/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryRelativePoint
public import FLT.Mazur.GroupMarkingBaseChange
public import FLT.Mazur.GroupMarkingTransportNaturality

/-!
# Normalize the complete marking of an actual auxiliary family

Start with an actual morphism into the original level-four scheme. The
pullback adjunction, coefficient group comparison, and proper normalization
transport its full homomorphism into the normalized cubic. Every label is
retained and faithfulness holds on every nonempty test scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj MonoidalCategory

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)
  {T : Over (Spec (.of R))}
  (p : (Over.map (auxiliaryCoefficientBase g)).obj T ⟶ levelFour)

/-- The complete original marking, as a homomorphism into the coefficient pullback group. -/
def auxiliaryFullCoefficientMarking :
    Labels 4 →* (T ⟶ (auxiliaryUniversalPullbackGroup g).X) :=
  GroupMarkingBaseChange.marking (auxiliaryCoefficientBase g)
    (integralCurveGroup smoothEquation smoothEquation_discriminant).X T
    (AuxiliaryLevel.markingOf universalGroup (Labels 4) (p ≫ auxiliaryInclusion 4))

/-- Pulling back the actual family pulls back each complete coefficient marking section. -/
theorem auxiliaryFullCoefficientMarking_natural {U : Over (Spec (.of R))}
    (k : U ⟶ T) (a : Labels 4) :
    auxiliaryFullCoefficientMarking g ((Over.map (auxiliaryCoefficientBase g)).map k ≫ p) a =
      k ≫ auxiliaryFullCoefficientMarking g p a := by
  change GroupMarkingBaseChange.pointsMulEquiv _ _ U
    (AuxiliaryLevel.markingOf universalGroup (Labels 4)
      (((Over.map (auxiliaryCoefficientBase g)).map k ≫ p) ≫ auxiliaryInclusion 4) a) = _
  rw [Category.assoc, AuxiliaryLevel.markingOf_comp]
  exact (Over.mapPullbackAdj (auxiliaryCoefficientBase g)).homEquiv_naturality_left k _

attribute [local irreducible] auxiliaryPullbackGroup auxiliaryNormalizedGroup
  auxiliaryNormalizationGroupIso auxiliaryCoefficientGroupIso

/-- The complete original marking on the actual auxiliary cubic. -/
def auxiliaryFullPullbackMarking : Labels 4 →* (T ⟶ (auxiliaryPullbackGroup g).X) :=
  GroupMarkingTransport.transport (auxiliaryUniversalPullbackGroup g) (auxiliaryPullbackGroup g)
    (auxiliaryCoefficientGroupIso g).symm (auxiliaryFullCoefficientMarking g p)

/-- Proper normalization transports the complete marking of the actual auxiliary family. -/
def auxiliaryFullNormalizedMarking : Labels 4 →* (T ⟶ (auxiliaryNormalizedGroup g).X) :=
  GroupMarkingTransport.transport (auxiliaryPullbackGroup g) (auxiliaryNormalizedGroup g)
    (auxiliaryNormalizationGroupIso g).symm (auxiliaryFullPullbackMarking g p)

/-- The full marking on the actual auxiliary cubic commutes with test-scheme pullback. -/
theorem auxiliaryFullPullbackMarking_natural {U : Over (Spec (.of R))}
    (k : U ⟶ T) (a : Labels 4) :
    auxiliaryFullPullbackMarking g ((Over.map (auxiliaryCoefficientBase g)).map k ≫ p) a =
      k ≫ auxiliaryFullPullbackMarking g p a :=
  GroupMarkingTransport.transport_natural
    (auxiliaryUniversalPullbackGroup g) (auxiliaryPullbackGroup g)
    (auxiliaryCoefficientGroupIso g).symm k
    (auxiliaryFullCoefficientMarking g p)
    (auxiliaryFullCoefficientMarking g ((Over.map (auxiliaryCoefficientBase g)).map k ≫ p))
    (fun c => auxiliaryFullCoefficientMarking_natural g p k c) a

/-- The full coefficient marking is faithful on every nonempty test scheme. -/
theorem auxiliaryFullCoefficientMarking_injective [Nonempty T.left] :
    Function.Injective (auxiliaryFullCoefficientMarking g p) := by
  unfold auxiliaryFullCoefficientMarking
  apply (GroupMarkingBaseChange.marking_injective_iff _ _ T _).mpr
  let _ : Nonempty ((Over.map (auxiliaryCoefficientBase g)).obj T).left :=
    inferInstanceAs (Nonempty T.left)
  exact auxiliaryMarking_injective 4 p

/-- The full marking on the original pulled-back cubic retains faithfulness. -/
theorem auxiliaryFullPullbackMarking_injective [Nonempty T.left] :
    Function.Injective (auxiliaryFullPullbackMarking g p) := by
  unfold auxiliaryFullPullbackMarking
  apply (GroupMarkingTransport.transport_injective_iff _ _ _ _).mpr
  exact auxiliaryFullCoefficientMarking_injective g p

/-- The full normalized marking retains faithfulness on every nonempty test scheme. -/
theorem auxiliaryFullNormalizedMarking_injective [Nonempty T.left] :
    Function.Injective (auxiliaryFullNormalizedMarking g p) := by
  unfold auxiliaryFullNormalizedMarking
  apply (GroupMarkingTransport.transport_injective_iff _ _ _ _).mpr
  exact auxiliaryFullPullbackMarking_injective g p

/-- Every normalized label remains killed by four in the actual group scheme. -/
theorem auxiliaryFullNormalizedMarking_pow (a : Labels 4) :
    auxiliaryFullNormalizedMarking g p a ^ 4 = 1 := by
  rw [← map_pow, labels_pow, map_one]

/-- An actual affine auxiliary family has a complete marking on its normalized cubic. -/
def auxiliaryFamilyNormalizedMarking (f : Spec (.of R) ⟶ levelFour.left) :
    Labels 4 →* (𝟙_ (Over (Spec (.of R))) ⟶
      (auxiliaryNormalizedGroup (auxiliaryPointSections f)).X) :=
  auxiliaryFullNormalizedMarking (auxiliaryPointSections f) (auxiliaryRelativePoint f)

/-- On a nonempty affine test scheme the normalized actual family has all sixteen labels. -/
theorem auxiliaryFamilyNormalizedMarking_injective
    (f : Spec (.of R) ⟶ levelFour.left) [Nonempty (Spec (.of R))] :
    Function.Injective (auxiliaryFamilyNormalizedMarking f) := by
  let _ : Nonempty (𝟙_ (Over (Spec (.of R)))).left :=
    inferInstanceAs (Nonempty (Spec (.of R)))
  exact auxiliaryFullNormalizedMarking_injective _ _

end FLT.Mazur.UniversalWeierstrass
