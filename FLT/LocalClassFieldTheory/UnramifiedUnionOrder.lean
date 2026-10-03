/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedUnionUnits

/-!
# Integer order on the unramified union

Finite-stage orders agree at common refinements. They therefore define an
actual homomorphism on all multiplicative coefficients of the union.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

local notation "U" => maximalUnramified R K C
local notation "E[" n "]" => unramifiedFiniteStage R K C n
local notation "S[" n "]" => integralClosure R (E[n])

attribute [local instance] stageDvr stageFractionRing

/-- Two finite representatives of the same unit have the same order. -/
theorem unramifiedStageOrder_eq {n m : UnramifiedIndex} (x : (E[n])ˣ) (y : (E[m])ˣ)
    (h : unramifiedUnionUnitMap R K C n x = unramifiedUnionUnitMap R K C m y) :
    discreteOrder (S[n]) (E[n]) x = discreteOrder (S[m]) (E[m]) y := by
  obtain ⟨p, hn, hm⟩ := exists_ge_ge n m
  have he : unramifiedStageUnitMap R K C hn x = unramifiedStageUnitMap R K C hm y := by
    apply unramifiedUnionUnitMap_injective R K C p
    simpa only [unramifiedUnionUnitMap_transition] using h
  rw [← unramifiedStageOrder_natural R K C hn, he, unramifiedStageOrder_natural]

/-- Order computed from any chosen finite representative. -/
def unramifiedUnionOrderValue (x : Uˣ) : Multiplicative ℤ :=
  let n := (exists_unramifiedUnionUnitMap R K C x).choose
  let y := (exists_unramifiedUnionUnitMap R K C x).choose_spec.choose
  discreteOrder (S[n]) (E[n]) y

/-- The chosen definition agrees with every finite-stage order. -/
@[simp] theorem unramifiedUnionOrderValue_stage (n : UnramifiedIndex) (x : (E[n])ˣ) :
    unramifiedUnionOrderValue R K C (unramifiedUnionUnitMap R K C n x) =
      discreteOrder (S[n]) (E[n]) x :=
  unramifiedStageOrder_eq R K C _ _
    (exists_unramifiedUnionUnitMap R K C _).choose_spec.choose_spec

/-- The compatible normalized orders define a homomorphism on the union's units. -/
def unramifiedUnionOrder : Uˣ →* Multiplicative ℤ where
  toFun := unramifiedUnionOrderValue R K C
  map_one' := by
    have h := unramifiedUnionOrderValue_stage R K C ⟨1⟩ 1
    simpa only [map_one] using h
  map_mul' x y := by
    obtain ⟨n, x, rfl⟩ := exists_unramifiedUnionUnitMap R K C x
    obtain ⟨m, y, rfl⟩ := exists_unramifiedUnionUnitMap R K C y
    obtain ⟨p, hn, hm⟩ := exists_ge_ge n m
    rw [← unramifiedUnionUnitMap_transition R K C hn x,
      ← unramifiedUnionUnitMap_transition R K C hm y, ← map_mul,
      unramifiedUnionOrderValue_stage, map_mul,
      unramifiedUnionOrderValue_stage, unramifiedUnionOrderValue_stage]

/-- Restriction of union order is exactly the normalized finite-stage order. -/
@[simp] theorem unramifiedUnionOrder_stage (n : UnramifiedIndex) (x : (E[n])ˣ) :
    unramifiedUnionOrder R K C (unramifiedUnionUnitMap R K C n x) =
      discreteOrder (S[n]) (E[n]) x := unramifiedUnionOrderValue_stage R K C n x

/-- All integers occur as orders in the union. -/
theorem unramifiedUnionOrder_surjective : Function.Surjective (unramifiedUnionOrder R K C) := by
  intro a
  obtain ⟨x, hx⟩ := discreteOrder_surjective (S[⟨1⟩]) (E[⟨1⟩]) a
  exact ⟨unramifiedUnionUnitMap R K C ⟨1⟩ x, (unramifiedUnionOrder_stage R K C ⟨1⟩ x).trans hx⟩

end LocalClassFieldTheory
