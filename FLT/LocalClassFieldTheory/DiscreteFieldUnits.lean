/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.DiscreteIntegralUnits

/-!
# Discrete multiplicative Galois coefficients

Field units have a discretely continuous action. Inclusion of integral units
is equivariant for this action.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- The usual Galois action, in additive notation for cohomology. -/
@[instance_reducible] def fieldUnitAction : DistribMulAction Gal(L/K) (Additive Lˣ) where
  smul g u := (Rep.ofAlgebraAutOnUnits K L).ρ g u
  one_smul u := congrArg (fun f : Module.End ℤ (Additive Lˣ) => f u)
    (map_one (Rep.ofAlgebraAutOnUnits K L).ρ)
  mul_smul g h u := congrArg (fun f : Module.End ℤ (Additive Lˣ) => f u)
    (map_mul (Rep.ofAlgebraAutOnUnits K L).ρ g h)
  smul_zero _ := map_zero _
  smul_add _ u v := map_add _ u v

attribute [local instance] fieldUnitAction integralUnitAction

/-- On values, the coefficient action is the field automorphism itself. -/
@[simp] theorem fieldUnitAction_val (g : Gal(L/K)) (u : Additive Lˣ) :
    (↑(Additive.toMul (g • u)) : L) = g (Additive.toMul u : Lˣ) := rfl

/-- Algebraicity makes the field-unit action discretely continuous. -/
instance fieldUnitAction_continuousDiscrete [Algebra.IsAlgebraic K L] :
    ContinuousSMulDiscrete Gal(L/K) (Additive Lˣ) := by
  apply continuousSMulDiscrete_iff_isOpen_stabilizer.mpr
  intro u
  convert stabilizer_isOpen_of_isIntegral (K := K) (↑(Additive.toMul u) : L) using 1
  ext g
  change g • u = u ↔ g (Additive.toMul u : Lˣ) = (Additive.toMul u : Lˣ)
  exact ⟨fun h => congrArg (fun x : Additive Lˣ => (↑(Additive.toMul x) : L)) h,
    fun h => Additive.toMul.injective (Units.ext h)⟩

variable (R : Type) [CommRing R] [Algebra R K] [IsFractionRing R K]
  [Algebra R L] [IsScalarTower R K L] [IsGalois K L]

/-- Integral inclusion as a morphism between the actual discrete coefficient representations. -/
def discreteIntegralUnitInclusion :
    Rep.of (Representation.ofDistribMulAction ℤ Gal(L/K) (IntegralUnitModule R L)) ⟶
      Rep.of (Representation.ofDistribMulAction ℤ Gal(L/K) (Additive Lˣ)) :=
  Rep.ofHom ⟨(Units.map (algebraMap (integralClosure R L) L).toMonoidHom).toAdditive.toIntLinearMap,
    fun g => by
      apply LinearMap.ext
      intro u
      apply Additive.toMul.injective
      apply Units.ext
      exact integralUnitAction_val R K L g u⟩

end LocalClassFieldTheory
