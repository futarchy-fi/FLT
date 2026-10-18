/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Exchange errors modulo actual target boundary corrections

The image of the boundary kernel under an exchange operator is the space of
available corrections. The error class is independent of the chosen boundary
lift. A surjective boundary map therefore induces a canonical obstruction map.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.BoundaryExchangeObstruction
variable {R T B S : Type*} [CommRing R]
  [AddCommGroup T] [AddCommGroup B] [AddCommGroup S]
  [Module R T] [Module R B] [Module R S]
  (b : T →ₗ[R] B) (δ : T →ₗ[R] S)

/-- Only exchanges of actual boundary-zero target elements are allowed. -/
def correctionImage : Submodule R S := (LinearMap.ker b).map δ

/-- The exchange class of a chosen lift. -/
def liftClass : T →ₗ[R] (S ⧸ correctionImage b δ) :=
  (correctionImage b δ).mkQ.comp δ

/-- Equality of original boundary values makes the two exchange classes equal. -/
theorem liftClass_eq_of_boundary_eq (v w : T) (h : b v = b w) :
    liftClass b δ v = liftClass b δ w := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  change (correctionImage b δ).mkQ (δ (v - w)) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨v - w, by change b (v - w) = 0; rw [map_sub, h, sub_self], rfl⟩

/-- Vanishing constructs a target correction in the original boundary kernel. -/
theorem liftClass_zero_iff (v : T) :
    liftClass b δ v = 0 ↔ ∃ z : T, b z = 0 ∧ δ z = δ v := by
  change (correctionImage b δ).mkQ (δ v) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

/-- Equivalently the given boundary value admits an exchange-free target lift. -/
theorem liftClass_zero_iff_lift (v : T) :
    liftClass b δ v = 0 ↔ ∃ w : T, b w = b v ∧ δ w = 0 := by
  rw [liftClass_zero_iff]
  constructor
  · rintro ⟨z, hz, hd⟩
    exact ⟨v - z, by rw [map_sub, hz, sub_zero], by rw [map_sub, hd, sub_self]⟩
  · rintro ⟨w, hw, hd⟩
    exact ⟨v - w, by rw [map_sub, hw, sub_self], by rw [map_sub, hd, sub_zero]⟩

/-- The exchange class factors through the original boundary quotient. -/
def boundaryQuotientMap : (T ⧸ LinearMap.ker b) →ₗ[R] (S ⧸ correctionImage b δ) :=
  (LinearMap.ker b).liftQ (liftClass b δ) (by
    intro v hv
    change liftClass b δ v = 0
    exact (liftClass_zero_iff b δ v).mpr ⟨v, hv, rfl⟩)

/-- A surjective boundary map gives a canonical operator on boundary values. -/
def boundaryMap (hb : Function.Surjective b) : B →ₗ[R] (S ⧸ correctionImage b δ) :=
  (boundaryQuotientMap b δ).comp (b.quotKerEquivOfSurjective hb).symm.toLinearMap

/-- The canonical boundary operator computes using any lift. -/
theorem boundaryMap_apply (hb : Function.Surjective b) (v : T) :
    boundaryMap b δ hb (b v) = liftClass b δ v := by
  change boundaryQuotientMap b δ ((b.quotKerEquivOfSurjective hb).symm (b v)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- Its kernel consists exactly of boundary values with exchange-free lifts. -/
theorem boundaryMap_zero_iff (hb : Function.Surjective b) (t : B) :
    boundaryMap b δ hb t = 0 ↔ ∃ w : T, b w = t ∧ δ w = 0 := by
  obtain ⟨v, rfl⟩ := hb t
  rw [boundaryMap_apply, liftClass_zero_iff_lift]

end FLT.Mazur.BoundaryExchangeObstruction
