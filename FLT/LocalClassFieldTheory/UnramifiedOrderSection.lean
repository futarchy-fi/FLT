/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedContinuousOrderH2

/-!
# Uniformizer powers split the order map

A base uniformizer is fixed by Galois and has order +1 in every unramified
stage. Its integer powers therefore give an equivariant section of order.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

local notation "U" => maximalUnramified R K C
local notation "G" => Gal(U/K)
local notation "E[" n "]" => unramifiedFiniteStage R K C n
local notation "S[" n "]" => integralClosure R (E[n])

attribute [local instance] unramifiedUnionGalois stageDvr stageFractionRing stageUnramified
  stageFinite stageLocalHom fieldUnitAction trivialCoefficientAction

variable {π : R} (hπ : Irreducible π)

/-- The base uniformizer as a multiplicative coefficient of the union. -/
def unramifiedUniformizerUnit : Uˣ :=
  Units.map (algebraMap K U).toMonoidHom (fractionUniformizer R K hπ)

/-- The base uniformizer has order +1 in the union. -/
theorem unramifiedUnionOrder_uniformizer :
    unramifiedUnionOrder R K C (unramifiedUniformizerUnit R K C hπ) =
      Multiplicative.ofAdd 1 := by
  let n : UnramifiedIndex := ⟨1⟩
  have hs := unramified_uniformizer_irreducible R (S[n]) hπ
  have he : unramifiedUniformizerUnit R K C hπ =
      unramifiedUnionUnitMap R K C n (fractionUniformizer (S[n]) (E[n]) hs) := by
    apply Units.ext
    change algebraMap K U (algebraMap R K π) =
      algebraMap (E[n]) U (algebraMap (S[n]) (E[n]) (algebraMap R (S[n]) π))
    rw [← IsScalarTower.algebraMap_apply R K U,
      ← IsScalarTower.algebraMap_apply R (S[n]) (E[n])]
    exact ((E[n]).toIntermediateField.val.restrictScalars R).commutes π |>.symm
  rw [he, unramifiedUnionOrder_stage, discreteOrder_fractionUniformizer]

/-- Every Galois automorphism fixes the base uniformizer. -/
theorem unramifiedUniformizerUnit_fixed (g : G) :
    Units.map g.toMonoidHom (unramifiedUniformizerUnit R K C hπ) =
      unramifiedUniformizerUnit R K C hπ := by
  apply Units.ext
  exact g.commutes (algebraMap R K π)

/-- Integer powers of the base uniformizer, as an additive coefficient homomorphism. -/
def unramifiedUniformizerPowers : ℤ →+ Additive Uˣ where
  toFun n := Additive.ofMul (unramifiedUniformizerUnit R K C hπ ^ n)
  map_zero' := by simp
  map_add' n m := congrArg Additive.ofMul
    (zpow_add (unramifiedUniformizerUnit R K C hπ) n m)

/-- Uniformizer powers define an equivariant coefficient section. -/
def unramifiedOrderSection :
    Rep.of (Representation.ofDistribMulAction ℤ G ℤ) ⟶
      Rep.of (Representation.ofDistribMulAction ℤ G (Additive Uˣ)) :=
  Rep.ofHom ⟨(unramifiedUniformizerPowers R K C hπ).toIntLinearMap, fun g => by
    apply LinearMap.ext
    intro n
    change Additive.ofMul (_ ^ n) =
      Additive.ofMul (Units.map g.toMonoidHom (unramifiedUniformizerUnit R K C hπ ^ n))
    rw [(Units.map g.toMonoidHom).map_zpow, unramifiedUniformizerUnit_fixed]⟩

/-- Order sends each uniformizer power to its exponent. -/
theorem unramifiedOrderSection_comp :
    unramifiedOrderSection R K C hπ ≫ unramifiedUnionOrderMap R K C = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro n
  change (unramifiedUnionOrder R K C (unramifiedUniformizerUnit R K C hπ ^ n)).toAdd = n
  rw [map_zpow, unramifiedUnionOrder_uniformizer]
  change n • (1 : ℤ) = n
  simp

end LocalClassFieldTheory
