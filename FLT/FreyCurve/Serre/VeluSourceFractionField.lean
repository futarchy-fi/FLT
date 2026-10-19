/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluSourceChartFractions

/-!
# The quadratic model is the fraction field of the actual affine chart

The original coordinate evaluation supplies the algebra structure. Its proved
injectivity and denominator clearing certify the fraction-field property.
-/

@[expose] public noncomputable section

open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [CharZero K] (E : WeierstrassCurve K)

/-- The actual affine coordinate action on the quadratic model. -/
instance sourceGenericChartAlgebra : Algebra (Coordinate E 2) (FunctionField E) :=
  (sourceGenericChart E).toRingHom.toAlgebra

/-- This scalar action is precisely the original coordinate evaluation. -/
theorem sourceGenericChart_algebraMap :
    algebraMap (Coordinate E 2) (FunctionField E) = (sourceGenericChart E).toRingHom := rfl

/-- The coordinate action is faithful by the two-component calculation. -/
instance sourceGenericChartFaithful : FaithfulSMul (Coordinate E 2) (FunctionField E) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (sourceGenericChart_injective E)

/-- Original coefficient scalars agree with the coordinate-ring action. -/
instance sourceGenericChartTower : IsScalarTower K (Coordinate E 2) (FunctionField E) :=
  IsScalarTower.of_algebraMap_eq' (sourceGenericChart E).comp_algebraMap.symm

/-- The original quadratic model is the fraction field of the actual source affine chart. -/
instance sourceGenericChartFractionRing : IsFractionRing (Coordinate E 2) (FunctionField E) :=
  IsFractionRing.of_field _ _ (sourceGenericChart_fraction_surjective E)

/-- The canonical fraction ring is identified with the original quadratic model. -/
def sourceGenericFractionEquiv :
    FractionRing (Coordinate E 2) ≃ₐ[Coordinate E 2] FunctionField E :=
  FractionRing.algEquiv _ _

/-- The comparison retains the exact original value of every affine function. -/
theorem sourceGenericFractionEquiv_algebraMap (a : Coordinate E 2) :
    sourceGenericFractionEquiv E (algebraMap _ (FractionRing (Coordinate E 2)) a) =
      sourceGenericChart E a :=
  (sourceGenericFractionEquiv E).commutes a

end WeierstrassCurve.Velu
