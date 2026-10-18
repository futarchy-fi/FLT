/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelFiniteType
public import FLT.Mazur.CyclicCharacteristicCoefficientFiniteType

/-!
# Finite type of both smooth auxiliary parameter schemes

Apply properness of the original universal cubics and Noetherianity of the
coefficient bases to the actual faithful marking schemes. Both characteristic
charts are finite type over the integers, including their marking parameters.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The even coefficient base is Noetherian. -/
instance evenCoefficient_isNoetherian : IsNoetherian UniversalWeierstrass.parameterBase where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian evenCoefficientToInt
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace evenCoefficientToInt

/-- The odd coefficient base is Noetherian. -/
instance oddCoefficient_isNoetherian : IsNoetherian OddWeierstrassParameter.parameterBase where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian oddCoefficientToInt
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace oddCoefficientToInt

/-- The even group used by all marking equations is the proper original cubic. -/
instance evenUniversalGroup_isProper : IsProper UniversalWeierstrass.universalGroup.hom := by
  change IsProper (WeierstrassIntegralChart.integralCurveStructure
    UniversalWeierstrass.smoothEquation)
  infer_instance

/-- The odd group used by all marking equations is the proper original cubic. -/
instance oddUniversalGroup_isProper : IsProper OddWeierstrassParameter.universalGroup.hom := by
  change IsProper (WeierstrassIntegralChart.integralCurveStructure
    IntegralWeierstrassParameter.oddChartEquation)
  infer_instance

/-- The complete level-four parameter scheme over the integers. -/
def evenAuxiliaryToInt : UniversalWeierstrass.levelFour.left ⟶ Spec (.of ℤ) :=
  UniversalWeierstrass.levelFour.hom ≫ evenCoefficientToInt

/-- The complete level-three parameter scheme over the integers. -/
def oddAuxiliaryToInt : OddWeierstrassParameter.levelThree.left ⟶ Spec (.of ℤ) :=
  OddWeierstrassParameter.levelThree.hom ≫ oddCoefficientToInt

/-- The full even auxiliary marking parameters are locally of finite type. -/
instance evenAuxiliaryToInt_locallyOfFiniteType : LocallyOfFiniteType evenAuxiliaryToInt := by
  let _ : LocallyOfFiniteType UniversalWeierstrass.levelFour.hom :=
    AuxiliaryLevel.faithfulScheme_locallyOfFiniteType _ _
  unfold evenAuxiliaryToInt
  infer_instance

/-- The full odd auxiliary marking parameters are locally of finite type. -/
instance oddAuxiliaryToInt_locallyOfFiniteType : LocallyOfFiniteType oddAuxiliaryToInt := by
  let _ : LocallyOfFiniteType OddWeierstrassParameter.levelThree.hom :=
    AuxiliaryLevel.faithfulScheme_locallyOfFiniteType _ _
  unfold oddAuxiliaryToInt
  infer_instance

/-- The actual even faithful auxiliary parameter map is quasi-compact. -/
instance evenAuxiliaryToInt_quasiCompact : QuasiCompact evenAuxiliaryToInt := by
  let _ : QuasiCompact UniversalWeierstrass.levelFour.hom :=
    AuxiliaryLevel.faithfulScheme_quasiCompact _ _
  unfold evenAuxiliaryToInt
  infer_instance

/-- The actual odd faithful auxiliary parameter map is quasi-compact. -/
instance oddAuxiliaryToInt_quasiCompact : QuasiCompact oddAuxiliaryToInt := by
  let _ : QuasiCompact OddWeierstrassParameter.levelThree.hom :=
    AuxiliaryLevel.faithfulScheme_quasiCompact _ _
  unfold oddAuxiliaryToInt
  infer_instance

end FLT.Mazur.CyclicCharacteristicAtlas
