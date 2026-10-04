/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.PicardGroup

/-!
# Unit generators for invertible submodules over a local ring

Local Picard triviality constructs the linear coordinate. The inverse submodule
then proves that its chosen generator is an algebra unit. Neither a coordinate
isomorphism nor a unit generator is supplied as input.
-/

@[expose] public noncomputable section

namespace Submodule

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [FaithfulSMul R A] [IsLocalRing R] (I : (Submodule R A)ˣ)

/-- A coordinate on an invertible submodule, constructed by local Picard vanishing. -/
def localUnitCoordinate : (I : Submodule R A) ≃ₗ[R] R :=
  (Module.Invertible.free_iff_linearEquiv.mp (inferInstance : Module.Free R I)).some

/-- The chosen generator is the vector with coordinate one. -/
def localUnitGenerator : A := (localUnitCoordinate I).symm 1

/-- The constructed generator belongs to the original submodule. -/
theorem localUnitGenerator_mem : localUnitGenerator I ∈ (I : Submodule R A) :=
  ((localUnitCoordinate I).symm 1).property

/-- Every vector is a scalar multiple of the constructed generator. -/
theorem eq_span_localUnitGenerator :
    (I : Submodule R A) = span R {localUnitGenerator I} := by
  apply le_antisymm
  · intro x hx
    let v : (I : Submodule R A) := ⟨x, hx⟩
    have h : (localUnitCoordinate I v) • localUnitGenerator I = x := by
      change (((localUnitCoordinate I v) • (localUnitCoordinate I).symm 1 :
        (I : Submodule R A)) : A) = x
      rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
    rw [← h]
    exact (span R {localUnitGenerator I}).smul_mem _ (subset_span (by simp))
  · exact span_le.mpr (Set.singleton_subset_iff.mpr (localUnitGenerator_mem I))

/-- Multiplication with the inverse component makes the generator a unit. -/
theorem localUnitGenerator_isUnit : IsUnit (localUnitGenerator I) := by
  have h : (1 : A) ∈ (I : Submodule R A) * (↑I⁻¹ : Submodule R A) := by
    rw [I.mul_inv]; exact one_le.mp le_rfl
  rw [eq_span_localUnitGenerator I, mem_span_singleton_mul] at h
  obtain ⟨y, _, hy⟩ := h
  exact ⟨⟨localUnitGenerator I, y, hy, by rw [mul_comm, hy]⟩, rfl⟩

/-- The unit generator constructed from the submodule and its inverse. -/
def localGeneratorUnit : Aˣ := (localUnitGenerator_isUnit I).unit

/-- Its underlying vector is the chosen local generator. -/
@[simp] theorem coe_localGeneratorUnit :
    (localGeneratorUnit I : A) = localUnitGenerator I :=
  (localUnitGenerator_isUnit I).unit_spec

end Submodule
