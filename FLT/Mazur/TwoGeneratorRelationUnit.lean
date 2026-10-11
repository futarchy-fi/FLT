/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TwoGeneratorRelationSequence

/-!
# A one-relation quotient with an invertible coefficient

When the first coefficient is invertible, the quotient is free of rank
one, with its first distinguished generator as a basis.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.TwoGeneratorRelation

variable {C : Type*} [CommRing C] (u : Cˣ) (y : C)

/-- Solve the relation for the second generator when its coefficient is a unit. -/
theorem right_eq_smul_left :
    right (u : C) y = (-(↑u⁻¹ * y) : C) • left (u : C) y := by
  have h := congrArg (fun z : Model (u : C) y ↦ (↑u⁻¹ : C) • z) (relation (u : C) y)
  simp only [smul_add, smul_smul, Units.inv_mul, one_smul, smul_zero] at h
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left h

/-- The first generator parametrizes the quotient by a unit-coefficient relation. -/
def unitSection : C →ₗ[C] Model (u : C) y :=
  (LinearMap.id (R := C)).smulRight (left (u : C) y)

/-- Evaluation sends the first generator to one and eliminates the second. -/
def unitEvaluation : Model (u : C) y →ₗ[C] C :=
  lift (u : C) y 1 (-(↑u⁻¹ * y)) (by
    simp only [smul_eq_mul, mul_neg, ← mul_assoc, Units.mul_inv, one_mul, mul_one, neg_add_cancel])

/-- Parametrization followed by evaluation recovers the scalar. -/
theorem unitEvaluation_section (a : C) : unitEvaluation u y (unitSection u y a) = a := by
  change unitEvaluation u y (a • left (u : C) y) = a
  rw [map_smul]
  simp [unitEvaluation]

/-- Evaluation followed by parametrization recovers the whole quotient. -/
theorem unitSection_evaluation (q : Model (u : C) y) :
    unitSection u y (unitEvaluation u y q) = q := by
  have h : (unitSection u y).comp (unitEvaluation u y) = LinearMap.id := by
    apply hom_ext
    · change unitSection u y (unitEvaluation u y (left (u : C) y)) = left (u : C) y
      simp [unitEvaluation, unitSection]
    · change unitSection u y (unitEvaluation u y (right (u : C) y)) = right (u : C) y
      rw [unitEvaluation, lift_right]
      exact (right_eq_smul_left u y).symm
  exact LinearMap.congr_fun h q

/-- The explicit quotient is a free rank-one module when the first coefficient is a unit. -/
def unitEquiv : Model (u : C) y ≃ₗ[C] C :=
  { unitEvaluation u y with
    invFun := unitSection u y
    left_inv := unitSection_evaluation u y
    right_inv := unitEvaluation_section u y }

/-- The resulting coordinate sends the distinguished first generator to one. -/
@[simp] theorem unitEquiv_left : unitEquiv u y (left (u : C) y) = 1 := by
  change unitEvaluation u y (left (u : C) y) = 1
  simp [unitEvaluation]

/-- A unit coefficient identifies the one-relation quotient with the coefficient ring. -/
def ofIsUnitEquiv (x y : C) (hx : IsUnit x) : Model x y ≃ₗ[C] C := by
  simpa only [hx.unit_spec] using unitEquiv hx.unit y

end FLT.Mazur.TwoGeneratorRelation
