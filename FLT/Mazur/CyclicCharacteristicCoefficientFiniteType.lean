/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryLevel
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
# Finite type of the two actual smooth coefficient bases

Both coefficient rings are finite type over the integers: five polynomial
coefficients followed by finitely many principal localizations. Their actual
maps to Spec Z are locally of finite type and quasi-compact. This concerns the
coefficient bases; finite type of the full subgroup atlas remains separate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The even smooth coefficient ring is a finite type integer algebra. -/
theorem evenCoefficientRing_finiteType :
    Algebra.FiniteType ℤ UniversalWeierstrass.ParameterRing := inferInstance

/-- The odd smooth coefficient ring is a finite type integer algebra. -/
theorem oddCoefficientRing_finiteType :
    Algebra.FiniteType ℤ IntegralWeierstrassParameter.OddChartRing := inferInstance

/-- The actual even coefficient base over the integers. -/
def evenCoefficientToInt : UniversalWeierstrass.parameterBase ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ UniversalWeierstrass.ParameterRing))

/-- The actual odd coefficient base over the integers. -/
def oddCoefficientToInt : OddWeierstrassParameter.parameterBase ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ IntegralWeierstrassParameter.OddChartRing))

/-- The even coefficient structure map is locally of finite type. -/
instance evenCoefficientToInt_locallyOfFiniteType : LocallyOfFiniteType evenCoefficientToInt :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr evenCoefficientRing_finiteType)

/-- The odd coefficient structure map is locally of finite type. -/
instance oddCoefficientToInt_locallyOfFiniteType : LocallyOfFiniteType oddCoefficientToInt :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr oddCoefficientRing_finiteType)

/-- Affineness makes the even coefficient map quasi-compact. -/
instance evenCoefficientToInt_quasiCompact : QuasiCompact evenCoefficientToInt := by
  unfold evenCoefficientToInt
  exact (HasAffineProperty.iff_of_isAffine
    (Q := fun X _ _ _ ↦ CompactSpace X)).mpr inferInstance

/-- Affineness makes the odd coefficient map quasi-compact. -/
instance oddCoefficientToInt_quasiCompact : QuasiCompact oddCoefficientToInt := by
  unfold oddCoefficientToInt
  exact (HasAffineProperty.iff_of_isAffine
    (Q := fun X _ _ _ ↦ CompactSpace X)).mpr inferInstance

end FLT.Mazur.CyclicCharacteristicAtlas
