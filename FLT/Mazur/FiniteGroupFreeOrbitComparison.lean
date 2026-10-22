/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupFreeUnramified

/-!
# The full orbit comparison for a free finite action

Translating the identity separator gives all coordinate delta functions.
Their linear combinations construct the inverse of the actual tensor orbit
map. No reduction of the source or target is used.
-/

@[expose] public noncomputable section
open TensorProduct
open scoped BigOperators
namespace FLT.Mazur.FiniteGroupQuotient
variable (G : Type*) [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
local notation "S" => invariantRing G A
local notation "C" => A ⊗[S] A

/-- The canonical map from full relation tensors to all orbit coordinates. -/
def orbitTensorComparison : C →ₐ[S] (G → A) := AlgHom.pi (orbitTensorCoordinate G A)

/-- Translating the second factor translates the actual orbit coordinates. -/
theorem orbitTensorCoordinate_translate (g h : G) (t : C) :
    orbitTensorCoordinate G A h (tensorActionHom G A A g t) =
      orbitTensorCoordinate G A (h * g) t := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp only [tensorActionHom_tmul, orbitTensorCoordinate_tmul, mul_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

variable [Finite G] (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤)
include hfree

/-- Every prescribed orbit function is realized by a full original tensor. -/
theorem orbitTensorComparison_surjective : Function.Surjective (orbitTensorComparison G A) := by
  classical
  let _ := Fintype.ofFinite G
  obtain ⟨t, ht₁, ht₀⟩ := exists_identity_orbit_tensor G A hfree
  intro f
  refine ⟨∑ g : G, (f g ⊗ₜ[S] 1) * tensorActionHom G A A g⁻¹ t, ?_⟩
  apply funext
  intro h
  change orbitTensorCoordinate G A h _ = f h
  simp only [map_sum, map_mul, orbitTensorCoordinate_tmul, smul_one, mul_one,
    orbitTensorCoordinate_translate]
  rw [Fintype.sum_eq_single h]
  · rw [mul_inv_cancel, ht₁, mul_one]
  · intro g hg
    rw [ht₀ (h * g⁻¹) (fun he ↦ hg (mul_inv_eq_one.mp he).symm), mul_zero]

/-- Freeness constructs the full comparison as an algebra isomorphism. -/
def freeOrbitTensorEquiv : C ≃ₐ[S] (G → A) :=
  AlgEquiv.ofBijective (orbitTensorComparison G A)
    ⟨fun _ _ h ↦ orbitTensorCoordinate_ext G A hfree (congrFun h),
      orbitTensorComparison_surjective G A hfree⟩

/-- The constructed isomorphism is the original endpoint evaluation on pure tensors. -/
theorem freeOrbitTensorEquiv_tmul (a b : A) (g : G) :
    freeOrbitTensorEquiv G A hfree (a ⊗ₜ[S] b) g = a * (g • b) := rfl

/-- The inverse recovers every original orbit coordinate, including its nilpotents. -/
theorem freeOrbitTensorEquiv_symm_coordinate (f : G → A) (g : G) :
    orbitTensorCoordinate G A g ((freeOrbitTensorEquiv G A hfree).symm f) = f g :=
  congrFun ((freeOrbitTensorEquiv G A hfree).apply_symm_apply f) g

end FLT.Mazur.FiniteGroupQuotient
