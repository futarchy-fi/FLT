/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeReductionKernelAbsorption

/-!
# Simultaneous boundary corrections absorbing the reduction kernel

Express absorption using the original linear boundary and discrepancy maps.
The witnesses are single boundary-zero families, rather than independently
chosen corrections for each mixed coordinate.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.RelativeBoundaryConnectingMap
variable {R A B C : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  (b : A →ₗ[R] B) (δ : A →ₗ[R] C) (J : Ideal R) (N : Submodule R C)

/-- Reduced injectivity is exactly simultaneous correction of every lost boundary residue. -/
theorem reducedInclusion_injective_iff_boundary_corrections
    (hKN : (LinearMap.ker b).map δ ≤ N) :
    Function.Injective (RelativeSubmoduleQuotient.reducedInclusion J N
      ((LinearMap.ker b).map δ)) ↔
        ∀ x ∈ N ⊓ J • (⊤ : Submodule R C), ∃ z : A, b z = 0 ∧ x - δ z ∈ J • N := by
  refine (RelativeSubmoduleQuotient.reducedInclusion_injective_iff_corrections
    J N ((LinearMap.ker b).map δ) hKN).trans ?_
  constructor
  · intro h x hx
    obtain ⟨y, hy, he⟩ := h x hx
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, hz, he⟩
  · intro h x hx
    obtain ⟨z, hz, he⟩ := h x hx
    exact ⟨δ z, ⟨z, hz, rfl⟩, he⟩

end FLT.Mazur.RelativeBoundaryConnectingMap
