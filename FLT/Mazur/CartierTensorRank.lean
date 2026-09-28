/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.DivisorInvertibleSheaf
public import FLT.Mazur.ModuleSheafTensorRestrict

/-!
# Rank-one Cartier ideals and the sheaf tensor

The local rank-one conditions used by the divisor and tensor constructions agree.
Consequently tensoring actual Cartier ideal sheaves preserves local rank one.
This does not identify the tensor with a product ideal or construct the dual sheaf.
-/

@[expose] public section

open AlgebraicGeometry

namespace FLT.Mazur.FCurve

variable {X : Scheme} {M N : X.Modules}

/-- The divisor and tensor constructions use the same local triviality condition. -/
theorem locallyFreeRankOne_iff_locallyRankOne :
    LocallyFreeRankOne M ↔ ModuleSheafTensor.LocallyRankOne M := Iff.rfl

/-- The actual sheaf tensor preserves local rank-one triviality. -/
theorem LocallyFreeRankOne.tensor (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N) :
    LocallyFreeRankOne (ModuleSheafTensor.tensor M N) :=
  ModuleSheafTensor.LocallyRankOne.tensor hM hN

/-- Tensor products of Cartier ideal sheaves are locally free of rank one. -/
theorem EffectiveCartier.idealModule_tensor_locallyFreeRankOne
    {I J : X.IdealSheafData} (hI : EffectiveCartier I) (hJ : EffectiveCartier J) :
    LocallyFreeRankOne (ModuleSheafTensor.tensor (idealModule I) (idealModule J)) :=
  hI.idealModule_locallyFreeRankOne.tensor hJ.idealModule_locallyFreeRankOne

end FLT.Mazur.FCurve
