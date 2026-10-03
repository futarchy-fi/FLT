/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.DiscreteIntegralUnits

/-!
# Descent of integral units to an intermediate field

An integral unit descends precisely when its field value lies in the
intermediate field. Integrality of both the value and its inverse descends.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

variable (R K L : Type) [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  (E : IntermediateField K L)

/-- Inclusion of the canonical integral units of an intermediate field. -/
def integralUnitFieldInclusion : (integralClosure R E)ˣ →* (integralClosure R L)ˣ :=
  Units.map (E.val.restrictScalars R).mapIntegralClosure.toMonoidHom

/-- Inclusion on units agrees with inclusion on field values. -/
@[simp] theorem integralUnitFieldInclusion_val (u : (integralClosure R E)ˣ) :
    ((integralUnitFieldInclusion R K L E u : integralClosure R L) : L) =
      ((u : integralClosure R E) : E) := rfl

/-- The inclusion loses no unit information. -/
theorem integralUnitFieldInclusion_injective :
    Function.Injective (integralUnitFieldInclusion R K L E) := by
  intro u v h
  apply Units.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun w : (integralClosure R L)ˣ => ((w : integralClosure R L) : L)) h

/-- Descent of a unit, including its integral inverse. -/
theorem integralUnitFieldInclusion_range (u : (integralClosure R L)ˣ) :
    (∃ v, integralUnitFieldInclusion R K L E v = u) ↔
      ((u : integralClosure R L) : L) ∈ E := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ((v : integralClosure R E) : E).property
  · intro hu
    let : IsScalarTower R E L := IsScalarTower.of_algebraMap_eq fun r =>
      ((E.val.restrictScalars R).commutes r).symm
    let x : E := ⟨((u : integralClosure R L) : L), hu⟩
    have hx : IsIntegral R x :=
      (isIntegral_algebraMap_iff (A := E) (B := L)).mp
        (u : integralClosure R L).property
    have hi : IsIntegral R x⁻¹ := by
      apply (isIntegral_algebraMap_iff (A := E) (B := L)).mp
      have hval : algebraMap E L x⁻¹ = ((↑(u⁻¹) : integralClosure R L) : L) := by
        change (((Units.map (algebraMap (integralClosure R L) L).toMonoidHom u : Lˣ) : L))⁻¹ = _
        exact (Units.val_inv_eq_inv_val _).symm
      rw [hval]
      exact (↑(u⁻¹) : integralClosure R L).property
    have hn : x ≠ 0 := by
      intro h
      have hz : ((u : integralClosure R L) : L) = 0 := congrArg Subtype.val h
      exact Units.ne_zero (Units.map (algebraMap (integralClosure R L) L).toMonoidHom u) hz
    let v : (integralClosure R E)ˣ :=
      { val := ⟨x, hx⟩
        inv := ⟨x⁻¹, hi⟩
        val_inv := Subtype.ext (mul_inv_cancel₀ hn)
        inv_val := Subtype.ext (inv_mul_cancel₀ hn) }
    exact ⟨v, Units.ext (Subtype.ext rfl)⟩

variable [IsFractionRing R K] [IsGalois K L]

attribute [local instance] integralUnitAction

/-- Fixed integral units are exactly the units descending to the fixed field. -/
theorem integralUnit_fixed_iff (u : IntegralUnitModule R L) :
    (∀ g : E.fixingSubgroup, (g : Gal(L/K)) • u = u) ↔
      ∃ v, integralUnitFieldInclusion R K L E v = Additive.toMul u := by
  rw [integralUnitFieldInclusion_range]
  conv_rhs => rw [← InfiniteGalois.fixedField_fixingSubgroup E]
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h g hg
    exact (integralUnitAction_fixed_iff R K L g u).mp (h ⟨g, hg⟩)
  · intro h g
    exact (integralUnitAction_fixed_iff R K L g u).mpr (h g g.property)

end LocalClassFieldTheory
