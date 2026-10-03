/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedInflationInjective
public import FLT.LocalClassFieldTheory.UnramifiedMultiplicativeInvariant
public import FLT.LocalClassFieldTheory.UnramifiedCarryTorsion

/-!
# Unramified classes inside absolute multiplicative H2

The proved injection realizes Q/Z as a subgroup of absolute H2. Inflated
uniformizer carries retain their exact annihilators. No surjectivity or
relative ramified-order assertion is made here.
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

/-- Unramified coordinates give an actual homomorphism into absolute H2. -/
def absoluteUnramifiedClass : AddCircle (1 : ℚ) →+
    continuousCohomology ℤ Gal(C/K) (Additive Cˣ) 2 :=
  (unramifiedMultiplicativeInflation R K C 2).hom.toAddMonoidHom.comp
    (unramifiedMultiplicativeInvariant R K C).symm.toAddMonoidHom

/-- This realizes Q/Z as a subgroup, without asserting that it is all of absolute H2. -/
theorem absoluteUnramifiedClass_injective :
    Function.Injective (absoluteUnramifiedClass R K C) :=
  (unramifiedMultiplicativeInflationH2_injective R K C).comp
    (unramifiedMultiplicativeInvariant R K C).symm.injective

variable {π : R} (hπ : Irreducible π)

/-- The class with coordinate +1/n is the inflation of the actual uniformizer carry. -/
theorem absoluteUnramifiedClass_carry (n : UnramifiedIndex) :
    absoluteUnramifiedClass R K C (↑((1 : ℚ) / n.degree) : AddCircle (1 : ℚ)) =
      (unramifiedMultiplicativeInflation R K C 2).hom
        (unramifiedMultiplicativeCarryClass R K C hπ n) := by
  rw [← unramifiedMultiplicativeCarryClass_coordinate R K C hπ n]
  change (unramifiedMultiplicativeInflation R K C 2).hom
    ((unramifiedMultiplicativeInvariant R K C).symm
      (unramifiedMultiplicativeInvariant R K C _)) = _
  rw [AddEquiv.symm_apply_apply]

/-- Inflating a multiplicative carry preserves its exact annihilator nZ. -/
theorem inflatedMultiplicativeCarry_zsmul_eq_zero (n : UnramifiedIndex) (j : ℤ) :
    j • (unramifiedMultiplicativeInflation R K C 2).hom
      (unramifiedMultiplicativeCarryClass R K C hπ n) = 0 ↔ (n.degree : ℤ) ∣ j := by
  rw [← absoluteUnramifiedClass_carry R K C hπ n, ← map_zsmul,
    map_eq_zero_iff _ (absoluteUnramifiedClass_injective R K C)]
  rw [← unramifiedCarryClass_coordinate R K C n, ← map_zsmul,
    map_eq_zero_iff _ (unramifiedIntegralH2AddEquiv R K C).injective]
  exact unramifiedCarryClass_zsmul_eq_zero R K C n j

end LocalClassFieldTheory
