/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassNormalizationGroup
public import FLT.Mazur.AuxiliaryCartesianParameterEquivalence

/-!
# Actual normalized faithful parameters on the odd chart

The coefficient comparison and the proper group normalization transport the
entire original level-three marking. Returning it to the normalized coefficient
base gives an actual point of the original faithful parameter scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open AuxiliaryLevel WeierstrassIntegralChart
open IntegralWeierstrassParameter (oddChartEquation oddChart_discriminant)
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- Properness supplies separatedness for the original pulled-back group. -/
instance auxiliaryPullbackGroup_separated : IsSeparated (auxiliaryPullbackGroup g).X.hom := by
  change IsSeparated (integralCurveStructure (auxiliaryPullbackEquation g))
  infer_instance

/-- Properness supplies separatedness for the actual normalized group. -/
instance auxiliaryNormalizedGroup_separated : IsSeparated (auxiliaryNormalizedGroup g).X.hom := by
  change IsSeparated (integralCurveStructure (auxiliaryNormalizedEquation g))
  infer_instance

variable {T : Over (Spec (.of R))}
  (p : (Over.map (auxiliaryCoefficientBase g)).obj T ⟶ levelThree)

/-- Realize the complete original faithful marking on its coefficient pullback. -/
irreducible_def auxiliaryOriginalParameter :
    T ⟶ faithfulScheme (auxiliaryPullbackGroup g).X (Labels 3) :=
  cartesianGroupParameter (auxiliaryCoefficientBase g)
    (integralCurveGroup oddChartEquation oddChart_discriminant) (auxiliaryPullbackGroup g)
    (auxiliaryCoefficientGroupIso g).symm (Labels 3) p

/-- Normalize the whole faithful marking through the actual proper group isomorphism. -/
irreducible_def auxiliaryNormalizedParameter :
    T ⟶ faithfulScheme (auxiliaryNormalizedGroup g).X (Labels 3) :=
  groupTransportParameter (auxiliaryPullbackGroup g) (auxiliaryNormalizedGroup g)
    (auxiliaryNormalizationGroupIso g).symm (Labels 3) (auxiliaryOriginalParameter g p)

/-- Each normalized label is the original label carried through the actual group inverse. -/
@[reassoc] theorem auxiliaryNormalizedParameter_value (a : Labels 3) :
    auxiliaryNormalizedParameter g p ≫
      faithfulInclusion (auxiliaryNormalizedGroup g).X (Labels 3) ≫
        value (auxiliaryNormalizedGroup g).X (Labels 3) a =
      markingOf (auxiliaryPullbackGroup g).X (Labels 3)
        (auxiliaryOriginalParameter g p ≫
          faithfulInclusion (auxiliaryPullbackGroup g).X (Labels 3)) a ≫
            (auxiliaryNormalizationGroupIso g).inv.hom.hom.hom := by
  rw [auxiliaryNormalizedParameter_def]
  exact groupTransportParameter_value _ _ _ _ _ _

/-- The normalized complete marking gives an actual parameter on the odd level scheme. -/
irreducible_def auxiliaryNormalizedLevelPoint :
    (Over.map (auxiliaryNormalizedCoefficientBase g)).obj T ⟶ levelThree :=
  originalGroupParameter (auxiliaryNormalizedCoefficientBase g)
    (integralCurveGroup oddChartEquation oddChart_discriminant) (auxiliaryNormalizedGroup g)
    (auxiliaryNormalizedCoefficientGroupIso g).symm (Labels 3)
    (auxiliaryNormalizedParameter g p)

/-- The original realized parameter commutes with every test-scheme map. -/
@[reassoc] theorem auxiliaryOriginalParameter_natural {U : Over (Spec (.of R))} (k : U ⟶ T) :
    k ≫ auxiliaryOriginalParameter g p =
      auxiliaryOriginalParameter g ((Over.map (auxiliaryCoefficientBase g)).map k ≫ p) := by
  simp only [auxiliaryOriginalParameter_def, cartesianGroupParameter_natural]

/-- Proper normalization retains the entire marking under arbitrary source pullback. -/
@[reassoc] theorem auxiliaryNormalizedParameter_natural {U : Over (Spec (.of R))} (k : U ⟶ T) :
    k ≫ auxiliaryNormalizedParameter g p =
      auxiliaryNormalizedParameter g ((Over.map (auxiliaryCoefficientBase g)).map k ≫ p) := by
  simp only [auxiliaryNormalizedParameter_def, groupTransportParameter_natural,
    auxiliaryOriginalParameter_natural]

/-- The actual normalized odd level point commutes with every source pullback. -/
@[reassoc] theorem auxiliaryNormalizedLevelPoint_natural {U : Over (Spec (.of R))} (k : U ⟶ T) :
    (Over.map (auxiliaryNormalizedCoefficientBase g)).map k ≫ auxiliaryNormalizedLevelPoint g p =
      auxiliaryNormalizedLevelPoint g ((Over.map (auxiliaryCoefficientBase g)).map k ≫ p) := by
  simp only [auxiliaryNormalizedLevelPoint_def, originalGroupParameter_natural,
    auxiliaryNormalizedParameter_natural]

/-- Universal faithfulness applies to the normalized actual level parameter. -/
theorem auxiliaryNormalizedLevelPoint_injective
    [Nonempty ((Over.map (auxiliaryNormalizedCoefficientBase g)).obj T).left] :
    Function.Injective (markingOf universalGroup (Labels 3)
      (auxiliaryNormalizedLevelPoint g p ≫ levelThreeInclusion)) :=
  levelThreeMarking_injective _

end FLT.Mazur.OddWeierstrassParameter
