/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedUnionOrderMap
public import FLT.LocalClassFieldTheory.UnramifiedContinuousUnits

/-!
# The short exact continuous order sequence

The integral-unit kernel and surjective integer order give a short exact
sequence of actual continuous cochain complexes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

local notation "U" => maximalUnramified R K C
local notation "ι" => discreteIntegralUnitInclusion K U R
local notation "ord" => unramifiedUnionOrderMap R K C

attribute [local instance] unramifiedUnionGalois integralUnitAction fieldUnitAction
  trivialCoefficientAction trivialCoefficientIntComm trivialCoefficientContinuous
  unramifiedUnitTopology unramifiedUnitDiscrete
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete

/-- Integral inclusion is injective on the actual additive coefficient module. -/
theorem discreteIntegralUnitInclusion_injective : Function.Injective (ι).hom := by
  intro u v h
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  exact congrArg (fun x : Additive Uˣ => (↑(Additive.toMul x) : U)) h

/-- The continuous order coefficients are exact at the multiplicative term. -/
theorem unramifiedUnionOrderMap_exact (x : Additive Uˣ) :
    (ord).hom x = 0 ↔ ∃ u : IntegralUnitModule R U, (ι).hom u = x := by
  change (unramifiedUnionOrder R K C x.toMul).toAdd = 0 ↔ _
  have he : (unramifiedUnionOrder R K C x.toMul).toAdd = 0 ↔
      unramifiedUnionOrder R K C x.toMul = 1 := Iff.rfl
  rw [he, unramifiedUnionOrder_eq_one_iff]
  rfl

/-- Integer order is surjective as an additive coefficient morphism. -/
theorem unramifiedUnionOrderMap_surjective : Function.Surjective (ord).hom := by
  intro n
  obtain ⟨x, hx⟩ := unramifiedUnionOrder_surjective R K C (Multiplicative.ofAdd n)
  exact ⟨Additive.ofMul x, congrArg Multiplicative.toAdd hx⟩

/-- The integral-unit inclusion has zero composite with order. -/
theorem unramifiedUnionOrderMap_comp_zero : ι ≫ ord = 0 := by
  ext u
  exact (unramifiedUnionOrderMap_exact R K C ((ι).hom u)).mpr ⟨u, rfl⟩

/-- The actual short complex of continuous order cochains. -/
def unramifiedContinuousOrderSequence : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ) :=
  continuousCoefficientShortComplex ι ord (unramifiedUnionOrderMap_comp_zero R K C)

/-- The order sequence is short exact in every continuous cochain degree. -/
theorem unramifiedContinuousOrderSequence_shortExact :
    (unramifiedContinuousOrderSequence R K C).ShortExact :=
  continuousCoefficientShortComplex_shortExact ι ord (unramifiedUnionOrderMap_comp_zero R K C)
    (discreteIntegralUnitInclusion_injective R K C) (unramifiedUnionOrderMap_surjective R K C)
    (unramifiedUnionOrderMap_exact R K C)

end LocalClassFieldTheory
