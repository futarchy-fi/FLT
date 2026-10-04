/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.AugmentationKernelNaturality
public import FLT.GroupScheme.PointDifferenceCotangentEvaluation
public import FLT.GroupScheme.FiniteFlatCotangentFinite

/-! # Naturality of the original cotangent pairing in the test algebra -/

@[expose] public noncomputable section
namespace AlgHom
variable {R A B C D E : Type*} [CommRing R] [CommRing A] [CommRing B]
  [CommRing C] [CommRing D] [CommRing E] [Algebra R A] [Algebra R B]
  [Algebra R C] [Algebra R D] [Algebra R E]
  (ε : A →ₐ[R] R) (q : B →ₐ[R] C) (q' : D →ₐ[R] E)
  (β : B →ₐ[R] D) (γ : C →ₐ[R] E) (hc : q'.comp β = γ.comp q)

/-- Changing the test algebra postcomposes the same cotangent functional with the kernel map. -/
theorem augmentationPointCotangentEquiv_natural
    (hJ : RingHom.ker q ^ 2 = ⊥) (hJ' : RingHom.ker q' ^ 2 = ⊥)
    (f : ε.AugmentationPointKernel q) :
    ε.augmentationPointCotangentEquiv q' hJ' (augmentationKernelMap q q' β γ hc ε f) =
      (reductionKernelMap q q' β γ hc).comp (ε.augmentationPointCotangentEquiv q hJ f) := by
  ext a
  obtain ⟨b, rfl⟩ := ε.augmentationCotangent_surjective a
  change (ε.augmentationPointCotangentEquiv q' hJ' _ (ε.augmentationCotangent b) : D) =
    β (ε.augmentationPointCotangentEquiv q hJ f (ε.augmentationCotangent b))
  rw [augmentationPointCotangentEquiv_projection,
    augmentationPointCotangentEquiv_projection, map_sub, β.commutes]
  rfl

end AlgHom
