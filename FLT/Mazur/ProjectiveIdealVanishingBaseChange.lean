/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveIdealVanishingScheme
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Base change of the coefficient ideal of an algebra ideal

The coefficient ideal of the actual extended ideal is the extension of the
original coefficient ideal. Arbitrary test rings, including nonflat rings,
are allowed; the source ideal need not be finitely generated.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.ProjectiveIdealVanishing
variable (R A B C : Type) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
  (J : Ideal B)

/-- Iterated extension of the actual ideal is identified by the tensor cancellation map. -/
theorem extendedIdeal_cancel :
    ((J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map
      (Algebra.TensorProduct.includeRight :
        A ⊗[R] B →ₐ[A] C ⊗[A] (A ⊗[R] B)).toRingHom).map
          (Algebra.TensorProduct.cancelBaseChange R A C C B).toRingHom =
      J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] C ⊗[R] B).toRingHom := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  ext b
  simp

/-- Iterated extension vanishes exactly when direct extension vanishes. -/
theorem iterated_extendedIdeal_eq_bot_iff :
    (J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map
      (Algebra.TensorProduct.includeRight :
        A ⊗[R] B →ₐ[A] C ⊗[A] (A ⊗[R] B)).toRingHom = ⊥ ↔
      J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] C ⊗[R] B).toRingHom = ⊥ := by
  rw [← extendedIdeal_cancel R A B C J]
  exact (Ideal.map_eq_bot_iff_of_injective
    (f := (Algebra.TensorProduct.cancelBaseChange R A C C B).toRingHom)
    (Algebra.TensorProduct.cancelBaseChange R A C C B).injective).symm

variable [Module.Projective R B]

/-- Actual coefficient ideals commute with all base changes, in particular localization. -/
theorem ideal_extendedIdeal :
    ideal A (A ⊗[R] B)
      (J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) =
        (ideal R B J).map (algebraMap R A) := by
  have h (I : Ideal A) :
      ideal A (A ⊗[R] B)
        (J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) ≤ I ↔
          (ideal R B J).map (algebraMap R A) ≤ I := by
    have hk : RingHom.ker (algebraMap A (A ⧸ I)) = I := by
      simp only [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    rw [← hk, ← extendedIdeal_eq_bot_iff_coefficients,
      iterated_extendedIdeal_eq_bot_iff, extendedIdeal_eq_bot_iff_coefficients,
      Ideal.map_le_iff_le_comap, IsScalarTower.algebraMap_eq R A (A ⧸ I),
      ← RingHom.comap_ker]
  exact le_antisymm ((h _).mpr le_rfl) ((h _).mp le_rfl)

end FLT.Mazur.ProjectiveIdealVanishing
