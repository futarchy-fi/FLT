/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.GaloisInflationH2
public import FLT.LocalClassFieldTheory.UnramifiedMultiplicativeInflation

/-!
# Injectivity of the constructed unramified inflation

The W23 morphism from the unramified union to the separable closure is
injective on H2. Surjectivity still requires the ramified relative-order theorem.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

attribute [local instance] unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

/-- The already constructed inflation map is injective on continuous H2. -/
theorem unramifiedMultiplicativeInflationH2_injective :
    Function.Injective (unramifiedMultiplicativeInflation R K C 2).hom :=
  galoisMultiplicativeInflationH2_injective K C (maximalUnramified R K C)

end LocalClassFieldTheory
