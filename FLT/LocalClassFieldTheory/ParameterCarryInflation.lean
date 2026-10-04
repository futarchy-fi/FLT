/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteParameterCarry
public import FLT.LocalClassFieldTheory.FiniteUnitInvariants
public import FLT.LocalClassFieldTheory.GaloisInflationH2

/-!
# Inflation of parameter carries

Restriction of the character and inclusion of a base-field unit commute
with the actual continuous H² class map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable (K C : Type) [Field K] [Field C] [Algebra K C] [IsGalois K C]
  (F : IntermediateField K C) [IsGalois K F] [FiniteDimensional K F]
  [TopologicalSpace (Additive Cˣ)] [DiscreteTopology (Additive Cˣ)]
  [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]
  {n : ℕ} [NeZero n] (χ : Gal(F/K) →* Multiplicative (ZMod n))

attribute [local instance] fieldUnitAction

/-- The scalar character obtained by actual Galois restriction. -/
def restrictedFiniteScalarCharacter : ContinuousScalarCharacter Gal(C/K) (ZMod n) :=
  ⟨⟨fun g => (χ (g.restrictNormal F)).toAdd,
    (continuous_of_discreteTopology (f := fun g : Gal(F/K) => (χ g).toAdd)).comp
      (InfiniteGalois.restrictNormalHom_continuous F)⟩,
    fun g h => congrArg Multiplicative.toAdd (map_mul (χ.comp (AlgEquiv.restrictNormalHom F)) g h)⟩

variable (u : Additive Kˣ)

local notation "x" => finiteUnitInvariantInclusion K F u
local notation "y" => finiteUnitInvariantInclusion K C u

/-- Inflation preserves the actual positive parameter-carry representative. -/
theorem finiteParameterCarryClass_inflation :
    (galoisMultiplicativeInflation K C F 2).hom (finiteParameterCarryClass χ (Additive Fˣ) x) =
      integralH2Class (k := ℤ)
        (cyclicParameterCarry (M := Additive Cˣ) (restrictedFiniteScalarCharacter K C F χ) (y).val)
        (cyclicParameterCarry_isCocycle (M := Additive Cˣ) _ _ (y).property) := by
  unfold finiteParameterCarryClass galoisMultiplicativeInflation
  refine (continuousInflationH2_class (AlgEquiv.restrictNormalHom F)
    (InfiniteGalois.restrictNormalHom_continuous F) (galoisInflationCoefficients K C F)
    (cyclicParameterCarry (M := Additive Fˣ) (finiteScalarCharacter χ) (x).val)
    (cyclicParameterCarry_isCocycle _ _ (x).property)).trans ?_
  congr 1
  apply ContinuousMap.ext
  intro z
  change (Units.map F.val.toMonoidHom).toAdditive
    (cyclicCarry (χ (z.1.restrictNormal F)).toAdd (χ (z.2.restrictNormal F)).toAdd • (x).val) = _
  rw [map_zsmul]
  congr 1

end LocalClassFieldTheory
