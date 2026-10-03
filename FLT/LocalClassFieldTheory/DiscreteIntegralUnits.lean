/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralUnitRepresentation
public import FLT.Mathlib.Topology.Algebra.ContinuousSMulDiscrete
public import Mathlib.FieldTheory.Galois.Infinite

/-!
# Discrete integral units in an algebraic Galois extension

The action restricts field automorphisms to the canonical integral closure.
Its stabilizers are open in the Krull topology, even for infinite extensions.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

variable (R K L : Type) [CommRing R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsGalois K L]

/-- The additive coefficient group of canonical integral units. -/
abbrev IntegralUnitModule := Additive (integralClosure R L)ˣ

/-- Restriction of field automorphisms, as an additive action on units. -/
@[instance_reducible] def integralUnitAction :
    DistribMulAction Gal(L/K) (IntegralUnitModule R L) where
  smul g u := (integralUnitRep R (integralClosure R L) K L).ρ g u
  one_smul u := congrArg (fun f : Module.End ℤ (IntegralUnitModule R L) => f u)
    (map_one (integralUnitRep R (integralClosure R L) K L).ρ)
  mul_smul g h u := congrArg (fun f : Module.End ℤ (IntegralUnitModule R L) => f u)
    (map_mul (integralUnitRep R (integralClosure R L) K L).ρ g h)
  smul_zero _ := map_zero _
  smul_add _ u v := map_add _ u v

attribute [local instance] integralUnitAction

/-- The action is compatible with inclusion into the fraction field. -/
@[simp] theorem integralUnitAction_val (g : Gal(L/K)) (u : IntegralUnitModule R L) :
    ((↑(Additive.toMul (g • u)) : integralClosure R L) : L) =
      g ((↑(Additive.toMul u) : integralClosure R L) : L) :=
  algebraMap_galRestrict_apply R g (↑(Additive.toMul u) : integralClosure R L)

/-- A unit is fixed exactly when its field value is fixed. -/
theorem integralUnitAction_fixed_iff (g : Gal(L/K)) (u : IntegralUnitModule R L) :
    g • u = u ↔ g ((↑(Additive.toMul u) : integralClosure R L) : L) =
      ((↑(Additive.toMul u) : integralClosure R L) : L) := by
  constructor
  · intro h
    rw [← integralUnitAction_val, h]
  · intro h
    apply Additive.toMul.injective
    apply Units.ext
    apply Subtype.ext
    exact (integralUnitAction_val R K L g u).trans h

/-- Integral units form a discretely continuous Galois module. -/
instance integralUnitAction_continuousDiscrete :
    ContinuousSMulDiscrete Gal(L/K) (IntegralUnitModule R L) := by
  apply continuousSMulDiscrete_iff_isOpen_stabilizer.mpr
  intro u
  convert stabilizer_isOpen_of_isIntegral (K := K)
    ((↑(Additive.toMul u) : integralClosure R L) : L) using 1
  ext g
  exact integralUnitAction_fixed_iff R K L g u

end LocalClassFieldTheory
