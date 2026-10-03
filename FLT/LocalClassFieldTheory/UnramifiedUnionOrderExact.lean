/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedUnionOrder
public import FLT.LocalClassFieldTheory.IntegralUnitDescent

/-!
# The kernel of order on the unramified union

Order zero means an actual integral unit. Both directions follow by descent
to canonical finite-stage units, including descent of the integral inverse.
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
local notation "inc" => Units.map (RingHom.toMonoidHom (algebraMap (integralClosure R U) U))

attribute [local instance] stageDvr stageFractionRing

/-- Including a finite-stage integral unit commutes with inclusion into the fraction field. -/
theorem unramifiedUnitInclusion_square (n : UnramifiedIndex) (u : (S[n])ˣ) :
    inc (integralUnitFieldInclusion R K U (E[n]).toIntermediateField u) =
      unramifiedUnionUnitMap R K C n (Units.map (algebraMap (S[n]) (E[n])).toMonoidHom u) := rfl

/-- Actual integral units have order zero in the union. -/
theorem unramifiedUnionOrder_integralUnit (u : (integralClosure R U)ˣ) :
    unramifiedUnionOrder R K C (inc u) = 1 := by
  obtain ⟨n, x, hx⟩ := exists_unramifiedUnionUnitMap R K C (inc u)
  have hu : ((u : integralClosure R U) : U) ∈ (E[n]).toIntermediateField := by
    have he := congrArg Units.val hx
    change ((x : E[n]) : U) = ((u : integralClosure R U) : U) at he
    rw [← he]
    exact (x : E[n]).property
  obtain ⟨v, rfl⟩ := (integralUnitFieldInclusion_range R K U (E[n]).toIntermediateField u).mpr hu
  rw [unramifiedUnitInclusion_square, unramifiedUnionOrder_stage]
  exact discreteOrder_unit (S[n]) (E[n]) v

/-- The kernel of the union order is exactly its integral-unit subgroup. -/
theorem unramifiedUnionOrder_eq_one_iff (x : Uˣ) :
    unramifiedUnionOrder R K C x = 1 ↔ ∃ u : (integralClosure R U)ˣ, inc u = x := by
  constructor
  · intro hx
    obtain ⟨n, y, rfl⟩ := exists_unramifiedUnionUnitMap R K C x
    rw [unramifiedUnionOrder_stage] at hx
    obtain ⟨u, rfl⟩ := (discreteOrder_eq_one_iff (S[n]) (E[n]) y).mp hx
    exact ⟨integralUnitFieldInclusion R K U (E[n]).toIntermediateField u,
      unramifiedUnitInclusion_square R K C n u⟩
  · rintro ⟨u, rfl⟩
    exact unramifiedUnionOrder_integralUnit R K C u

end LocalClassFieldTheory
