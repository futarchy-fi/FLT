/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedStageCarryCup
public import FLT.LocalClassFieldTheory.UnramifiedMultiplicativeInvariant
public import FLT.LocalClassFieldTheory.GaloisInflationH2
public import FLT.LocalClassFieldTheory.FiniteContinuousH2Class
public import FLT.LocalClassFieldTheory.FiniteRestrictionComparison

/-!
# Inflation of the finite uniformizer carry

The explicit finite carry inflates to the uniformizer carry on the unramified
union. The comparison uses the cochain maps and preserves the positive sign.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory HomologicalComplex groupCohomology

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]
  {π : R} (hπ : Irreducible π) (n : UnramifiedIndex)

local notation "E" => unramifiedFiniteStage R K C n
local notation "M" => Rep.ofAlgebraAutOnUnits K E
local notation "e" => MulEquiv.symm (unramifiedStageCyclicEquiv R K C n)
local notation "x" => finiteUnitInvariantInclusion K E (Additive.ofMul (fractionUniformizer R K hπ))


local notation "U" => maximalUnramified R K C
local notation "Z" => Multiplicative (ZMod n.degree)

attribute [local instance] unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  trivialCoefficientAction trivialCoefficientIntComm trivialCoefficientContinuous

/-- Finite-stage unit coefficients use the discrete topology. -/
local instance unramifiedStageCarryUnitTopology : TopologicalSpace (Additive Eˣ) := ⊥
local instance unramifiedStageCarryUnitDiscrete : DiscreteTopology (Additive Eˣ) := ⟨rfl⟩

/-- The finite carry in continuous cohomology, obtained from the actual cyclic cocycle. -/
def unramifiedStageContinuousCarry : continuousCohomology ℤ Gal(E/K) (Additive Eˣ) 2 :=
  (homologyMap (continuousRestriction (e).toMonoidHom continuous_of_discreteTopology
    (invariantScalarCoefficients M (e).toMonoidHom x)) 2).hom
    (integralH2Class (k := ℤ) (cyclicIntegralCarry n.degree)
      (cyclicIntegralCarry_cocycle n.degree))

/-- Finite comparison recovers the previously constructed ordinary carry. -/
theorem unramifiedStageContinuousCarry_ordinary :
    (finiteContinuousCohomologyIso ℤ Gal(E/K) (Additive Eˣ) 2).hom
      (unramifiedStageContinuousCarry R K C hπ n) =
    H2π M (unramifiedStageOrdinaryCarry R K C hπ n) := by
  have h := finiteContinuousCohomologyIso_restriction (e).toMonoidHom
    continuous_of_discreteTopology (invariantScalarCoefficients M (e).toMonoidHom x) 2
  have he := congrArg (fun f => f.hom
    (integralH2Class (k := ℤ) (cyclicIntegralCarry n.degree)
      (cyclicIntegralCarry_cocycle n.degree))) h
  change _ = groupCohomology.map (e).toMonoidHom
    (invariantScalarCoefficients M (e).toMonoidHom x) 2
      ((finiteContinuousCohomologyIso ℤ Z ℤ 2).hom _) at he
  rw [finiteContinuousH2Class] at he
  exact he.trans (congrArg (fun f => f (cyclicOrdinaryCarry n.degree))
    (congrArg ConcreteCategory.hom (H2π_comp_map (e).toMonoidHom
      (invariantScalarCoefficients M (e).toMonoidHom x))))

/-- The two routes from integral cyclic cochains agree before taking cohomology. -/
theorem unramifiedStageCarry_inflation_complex :
    continuousRestriction (e).toMonoidHom continuous_of_discreteTopology
        (invariantScalarCoefficients M (e).toMonoidHom x) ≫
      continuousRestriction (AlgEquiv.restrictNormalHom E)
        (InfiniteGalois.restrictNormalHom_continuous (E).toIntermediateField)
        (galoisInflationCoefficients K U E) =
    trivialRestriction (unramifiedDegreeCharacter R K C n) ℤ ≫
      continuousCoefficientMap (unramifiedOrderSection R K C hπ) := by
  ext i c : 3
  apply Subtype.ext
  funext g
  change (Units.map (E).toIntermediateField.val.toMonoidHom).toAdditive
    ((c.val _) • (finiteUnitInvariantInclusion K E
      (Additive.ofMul (fractionUniformizer R K hπ))).val) = _
  rw [map_zsmul]
  rfl

/-- The finite-stage carry inflates to the independently defined union carry. -/
theorem unramifiedStageContinuousCarry_inflation :
    (galoisMultiplicativeInflation K U E 2).hom
      (unramifiedStageContinuousCarry R K C hπ n) =
    unramifiedMultiplicativeCarryClass R K C hπ n := by
  have h := congrArg (fun f => homologyMap f 2)
    (unramifiedStageCarry_inflation_complex R K C hπ n)
  rw [homologyMap_comp, homologyMap_comp] at h
  exact congrArg (fun f => f.hom
    (integralH2Class (k := ℤ) (cyclicIntegralCarry n.degree)
      (cyclicIntegralCarry_cocycle n.degree))) h

end LocalClassFieldTheory
