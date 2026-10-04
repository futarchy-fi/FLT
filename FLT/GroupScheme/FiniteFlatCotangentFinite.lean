/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatCotangent

/-! # Finite generation of actual finite-flat augmentation cotangents -/

@[expose] public noncomputable section
namespace AlgHom
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The original augmented algebra surjects onto its augmentation cotangent. -/
theorem augmentationCotangent_surjective (ε : A →ₐ[R] R) :
    Function.Surjective ε.augmentationCotangent := by
  intro a
  obtain ⟨b, rfl⟩ := (RingHom.ker ε).toCotangent_surjective a
  exact ⟨b, ε.augmentationCotangent_of_mem b⟩

/-- Finite generation descends from the actual algebra, without a Noetherian assumption. -/
theorem augmentationCotangent_finite [Module.Finite R A] (ε : A →ₐ[R] R) :
    Module.Finite R (RingHom.ker ε).Cotangent :=
  Module.Finite.of_surjective ε.augmentationCotangent ε.augmentationCotangent_surjective

end AlgHom
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

/-- Each original finite-flat model has a finite cotangent module over its original base. -/
instance FF.cotangentFinite (X : FF R K) : Module.Finite R X.Cotangent :=
  (Bialgebra.counitAlgHom R X.CoordinateRing).augmentationCotangent_finite

end ThreeAdicPlan
