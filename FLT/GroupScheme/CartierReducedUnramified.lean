/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierReducedDifferential
public import Mathlib.RingTheory.Unramified.Basic

/-! # Reduced Cartier differentials vanish on formally unramified coordinates -/

@[expose] public noncomputable section
namespace HopfAlgebra.CartierDual
variable {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]
  [Algebra.FormallyUnramified R A]

omit [Module.Finite R A] [Module.Free R A] in
/-- A point reducing to the augmentation is the augmentation on unramified coordinates. -/
theorem unramified_augmentationPoint (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥)
    (f : (Bialgebra.counitAlgHom R A).AugmentationPointKernel q) :
    f.val = (Algebra.ofId R B).comp (Bialgebra.counitAlgHom R A) := by
  apply Algebra.FormallyUnramified.lift_unique' q ⟨2, hJ⟩
  rw [f.property]
  ext a
  exact (q.commutes _).symm

omit [Module.Finite R A] [Module.Free R A] in
/-- The actual tangent extracted from such a point is zero. -/
theorem unramified_augmentationTangent (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥)
    (f : (Bialgebra.counitAlgHom R A).AugmentationPointKernel q) :
    AlgHom.augmentationPointToTangent _ q hJ f = 0 := by
  apply Subtype.ext
  ext a
  change f.val a - algebraMap R B (Coalgebra.counit a) = 0
  rw [unramified_augmentationPoint q hJ f]
  exact sub_self _

/-- Every reduced dual character evaluates to zero on unramified infinitesimal points. -/
theorem reducedLogDifferential_unramified (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hJ : RingHom.ker q ^ 2 = ⊥) (ψ : CartierDual R A →ₐ[R] C)
    (f : (Bialgebra.counitAlgHom R A).AugmentationPointKernel q) :
    reducedLogDifferential q hq ψ (AlgHom.augmentationPointToTangent _ q hJ f) = 0 := by
  rw [unramified_augmentationTangent q hJ f, map_zero]

end HopfAlgebra.CartierDual
