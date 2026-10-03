/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedUnionOrderExact
public import FLT.LocalClassFieldTheory.DiscreteFieldUnits
public import FLT.LocalClassFieldTheory.RationalCoefficientSequence

/-!
# The continuous order coefficient map

Finite-stage Galois invariance passes to the union. The resulting order map
is a morphism from the discrete multiplicative coefficients to constant Z.
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

/-- Galois commutes with the inclusions of multiplicative finite-stage coefficients. -/
theorem unramifiedUnionUnitMap_galois (n : UnramifiedIndex) (g : G) (x : (E[n])ˣ) :
    Units.map g.toMonoidHom (unramifiedUnionUnitMap R K C n x) =
      unramifiedUnionUnitMap R K C n (Units.map (g.restrictNormal (E[n])).toMonoidHom x) := by
  apply Units.ext
  exact (AlgEquiv.restrictNormal_apply (E[n]).toIntermediateField g (x : E[n])).symm

/-- The union's order is Galois invariant. -/
theorem unramifiedUnionOrder_galois (g : G) (x : Uˣ) :
    unramifiedUnionOrder R K C (Units.map g.toMonoidHom x) = unramifiedUnionOrder R K C x := by
  obtain ⟨n, y, rfl⟩ := exists_unramifiedUnionUnitMap R K C x
  rw [unramifiedUnionUnitMap_galois, unramifiedUnionOrder_stage, unramifiedUnionOrder_stage]
  exact discreteOrder_galois R (S[n]) K (E[n]) (g.restrictNormal (E[n])) y

/-- Normalized union order in additive coefficient notation. -/
def unramifiedUnionOrderAdd : Additive Uˣ →+ ℤ where
  toFun x := (unramifiedUnionOrder R K C x.toMul).toAdd
  map_zero' := by simp
  map_add' x y := by
    change (unramifiedUnionOrder R K C (x.toMul * y.toMul)).toAdd = _
    rw [map_mul]
    rfl

/-- The actual equivariant order morphism with constant integer target. -/
def unramifiedUnionOrderMap :
    Rep.of (Representation.ofDistribMulAction ℤ G (Additive Uˣ)) ⟶
      Rep.of (Representation.ofDistribMulAction ℤ G ℤ) :=
  Rep.ofHom ⟨(unramifiedUnionOrderAdd R K C).toIntLinearMap, fun g => by
    apply LinearMap.ext
    intro x
    exact congrArg Multiplicative.toAdd (unramifiedUnionOrder_galois R K C g x.toMul)⟩

/-- The field-unit coefficients carry the discrete topology. -/
local instance unramifiedFieldUnitTopology : TopologicalSpace (Additive Uˣ) := ⊥
local instance unramifiedFieldUnitDiscrete : DiscreteTopology (Additive Uˣ) := ⟨rfl⟩

end LocalClassFieldTheory
