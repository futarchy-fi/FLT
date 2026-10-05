/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Etale.Basic

/-! # Augmentation cotangents of formally unramified algebras -/

@[expose] public noncomputable section
namespace AlgHom
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FormallyUnramified R A]

/-- The kernel of an augmentation on an unramified algebra is idempotent. -/
theorem augmentation_ker_idempotent_of_unramified (ε : A →ₐ[R] R) :
    IsIdempotentElem (RingHom.ker ε) := by
  let : Algebra A R := ε.toRingHom.toAlgebra
  let : IsScalarTower R A R := IsScalarTower.of_algHom ε
  let : Algebra.FormallyEtale A R := Algebra.FormallyEtale.of_restrictScalars (R := R)
  exact (Algebra.FormallyEtale.iff_of_surjective
    (show Function.Surjective (algebraMap A R) from fun r ↦
      ⟨algebraMap R A r, ε.commutes r⟩)).mp inferInstance

/-- The actual augmentation cotangent quotient of an unramified algebra is zero. -/
theorem augmentationCotangent_subsingleton_of_unramified (ε : A →ₐ[R] R) :
    Subsingleton (RingHom.ker ε).Cotangent :=
  (Ideal.cotangent_subsingleton_iff _).mpr
    ε.augmentation_ker_idempotent_of_unramified

end AlgHom
