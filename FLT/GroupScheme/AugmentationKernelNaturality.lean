/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SquareZeroAugmentationPoints

/-! # Naturality of actual augmentation kernels across commuting reductions -/

@[expose] public noncomputable section
namespace AlgHom
variable {R A B C D E : Type*} [CommRing R] [CommRing A] [CommRing B]
  [CommRing C] [CommRing D] [CommRing E] [Algebra R A] [Algebra R B]
  [Algebra R C] [Algebra R D] [Algebra R E]
  (q : B →ₐ[R] C) (q' : D →ₐ[R] E) (β : B →ₐ[R] D) (γ : C →ₐ[R] E)
  (hc : q'.comp β = γ.comp q)

/-- The actual map of reduction kernels induced by a commuting square. -/
def reductionKernelMap : RingHom.ker q →ₗ[R] RingHom.ker q' :=
  (β.toLinearMap.comp ((RingHom.ker q).restrictScalars R).subtype).codRestrict
    ((RingHom.ker q').restrictScalars R) fun b ↦ by
      change q' (β b) = 0
      rw [show q' (β b) = γ (q b) from AlgHom.congr_fun hc b, b.property, map_zero]

variable (ε : A →ₐ[R] R)

/-- Postcomposition sends actual augmentation points to actual augmentation points. -/
def augmentationKernelMap (f : ε.AugmentationPointKernel q) :
    ε.AugmentationPointKernel q' :=
  ⟨β.comp f.val, by
    rw [← comp_assoc, hc, comp_assoc, f.property]
    ext a
    exact γ.commutes (ε a)⟩

/-- Postcomposition of module-valued tangents uses the same map on reduction kernels. -/
def reductionTangentMap (d : ε.augmentationTangent (M := RingHom.ker q)) :
    ε.augmentationTangent (M := RingHom.ker q') :=
  ⟨(reductionKernelMap q q' β γ hc).comp d.val, by
    intro a b
    change reductionKernelMap q q' β γ hc (d.val (a * b)) = _
    rw [d.property, map_add, map_smul, map_smul]
    rfl⟩

/-- Extracting a tangent commutes with the actual change of test algebras. -/
theorem augmentationPointToTangent_natural
    (hJ : RingHom.ker q ^ 2 = ⊥) (hJ' : RingHom.ker q' ^ 2 = ⊥)
    (f : ε.AugmentationPointKernel q) :
    augmentationPointToTangent ε q' hJ' (augmentationKernelMap q q' β γ hc ε f) =
      reductionTangentMap q q' β γ hc ε (augmentationPointToTangent ε q hJ f) := by
  apply Subtype.ext
  ext a
  change β (f.val a) - algebraMap R D (ε a) =
    β (f.val a - algebraMap R B (ε a))
  rw [map_sub, β.commutes]

/-- Reconstruction also commutes, without choosing replacement points or kernels. -/
theorem tangentToAugmentationPoint_natural
    (hJ : RingHom.ker q ^ 2 = ⊥) (hJ' : RingHom.ker q' ^ 2 = ⊥)
    (d : ε.augmentationTangent (M := RingHom.ker q)) :
    tangentToAugmentationPoint ε q' hJ' (reductionTangentMap q q' β γ hc ε d) =
      augmentationKernelMap q q' β γ hc ε (tangentToAugmentationPoint ε q hJ d) := by
  apply Subtype.ext
  ext a
  change algebraMap R D (ε a) + β (d.val a) =
    β (algebraMap R B (ε a) + d.val a)
  rw [map_add, β.commutes]

end AlgHom
