/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedStageOrderMaps

/-!
# Multiplicative coefficients of the unramified union

Every field unit lies in a constructed finite stage. The inclusions are
injective and compatible with refinement of the degree index.
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

/-- A finite-stage unit, included in the unramified union. -/
def unramifiedUnionUnitMap (n : UnramifiedIndex) : (E[n])ˣ →* Uˣ :=
  Units.map (E[n]).toIntermediateField.val.toMonoidHom

/-- The stage inclusion is injective on units. -/
theorem unramifiedUnionUnitMap_injective (n : UnramifiedIndex) :
    Function.Injective (unramifiedUnionUnitMap R K C n) := by
  intro x y h
  apply Units.ext
  apply Subtype.ext
  exact congrArg Units.val h

/-- Refining a stage does not change its value in the union. -/
@[simp] theorem unramifiedUnionUnitMap_transition {n m : UnramifiedIndex} (h : n ≤ m)
    (x : (E[n])ˣ) :
    unramifiedUnionUnitMap R K C m (unramifiedStageUnitMap R K C h x) =
      unramifiedUnionUnitMap R K C n x := rfl

/-- Every multiplicative coefficient of the union comes from a finite stage. -/
theorem exists_unramifiedUnionUnitMap (x : Uˣ) :
    ∃ (n : UnramifiedIndex) (y : (E[n])ˣ), unramifiedUnionUnitMap R K C n y = x := by
  obtain ⟨n, hn⟩ := (mem_maximalUnramified_iff R K C ((x : U) : C)).mp (x : U).property
  have hx : (x : U) ∈ (E[⟨n⟩]).toIntermediateField :=
    (mem_unramifiedFiniteStage R K C ⟨n⟩ (x : U)).mpr hn
  let y : E[⟨n⟩] := ⟨(x : U), hx⟩
  have hy : y ≠ 0 := fun h => x.ne_zero (congrArg Subtype.val h)
  exact ⟨⟨n⟩, Units.mk0 y hy, Units.ext rfl⟩

end LocalClassFieldTheory
