/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ParameterCarryCoefficients
public import FLT.LocalClassFieldTheory.AbsoluteInvariant
public import FLT.LocalClassFieldTheory.UnramifiedUnionBaseOrder

/-!
# The invariant of an unramified parameter carry

Order sends the parameter carry to the scalar carry multiplied by the base
valuation. The integral invariant then evaluates its character at Frobenius.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete
  trivialCoefficientAction trivialCoefficientIntComm trivialCoefficientContinuous

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]
  {n : ℕ} [NeZero n]

local notation "U" => maximalUnramified R K C

variable (χ : ContinuousScalarCharacter Gal(maximalUnramified R K C/K) (ZMod n))

/-- The carry over the unramified union with the included base-field parameter. -/
def unramifiedParameterCarryClass (u : Additive Kˣ) :
    continuousCohomology ℤ Gal(U/K) (Additive Uˣ) 2 :=
  integralH2Class (k := ℤ)
    (cyclicParameterCarry (M := Additive Uˣ) χ (finiteUnitInvariantInclusion K U u).val)
    (cyclicParameterCarry_isCocycle (M := Additive Uˣ) _ _
      (finiteUnitInvariantInclusion K U u).property)

/-- A base parameter's invariant is its integer valuation times character Frobenius. -/
theorem unramifiedParameterCarry_invariant (u : Additive Kˣ) :
    unramifiedMultiplicativeInvariant R K C (unramifiedParameterCarryClass R K C χ u) =
      discreteOrderAdd R K u • zmodToRatCircle n (χ.val (unramifiedFrobenius R K C)) := by
  change unramifiedIntegralH2AddEquiv R K C
    ((continuousCoefficientCohomologyMap (unramifiedUnionOrderMap R K C) 2).hom _) = _
  rw [unramifiedParameterCarryClass,
    parameterCarry_coefficient_class (unramifiedUnionOrderMap R K C)
      (finiteUnitInvariantInclusion K U u).val (finiteUnitInvariantInclusion K U u).property χ]
  have ho : (unramifiedUnionOrderMap R K C).hom
      (finiteUnitInvariantInclusion K U u).val = discreteOrderAdd R K u :=
    congrArg Multiplicative.toAdd (unramifiedUnionOrder_base R K C (Additive.toMul u))
  rw [parameterCarry_integer_class, map_zsmul, ho]
  change discreteOrderAdd R K u • unramifiedIntegralH2Equiv R K C (scalarCarryClass χ) = _
  rw [scalarCarryClass_character, unramifiedIntegralH2Equiv_character]
  rfl

/-- Restriction inflates an unramified scalar character to the absolute group. -/
def inflatedUnramifiedScalarCharacter : ContinuousScalarCharacter Gal(C/K) (ZMod n) :=
  ⟨⟨fun g => χ.val (unramifiedRestriction R K C g),
    χ.val.continuous.comp (unramifiedRestriction_continuous R K C)⟩,
    fun g h => by
      change χ.val (unramifiedRestriction R K C (g * h)) =
        χ.val (unramifiedRestriction R K C g) + χ.val (unramifiedRestriction R K C h)
      rw [map_mul]
      exact χ.property _ _⟩

/-- The absolute parameter carry is the inflation of its unramified representative. -/
theorem unramifiedParameterCarry_inflation (u : Additive Kˣ) :
    (unramifiedMultiplicativeInflation R K C 2).hom
      (unramifiedParameterCarryClass R K C χ u) =
    integralH2Class (k := ℤ)
      (cyclicParameterCarry (M := Additive Cˣ) (inflatedUnramifiedScalarCharacter R K C χ)
        (finiteUnitInvariantInclusion K C u).val)
      (cyclicParameterCarry_isCocycle (M := Additive Cˣ) _ _
        (finiteUnitInvariantInclusion K C u).property) := by
  refine (continuousInflationH2_class (unramifiedRestriction R K C)
    (unramifiedRestriction_continuous R K C) (unramifiedMultiplicativeInflationCoefficients R K C)
    (cyclicParameterCarry (M := Additive Uˣ) χ (finiteUnitInvariantInclusion K U u).val)
    (cyclicParameterCarry_isCocycle _ _ (finiteUnitInvariantInclusion K U u).property)).trans ?_
  congr 1
  apply ContinuousMap.ext
  intro z
  change (Units.map (U).val.toMonoidHom).toAdditive
    (cyclicCarry (χ.val (unramifiedRestriction R K C z.1))
      (χ.val (unramifiedRestriction R K C z.2)) •
        (finiteUnitInvariantInclusion K U u).val) = _
  rw [map_zsmul]
  congr 1

end LocalClassFieldTheory
