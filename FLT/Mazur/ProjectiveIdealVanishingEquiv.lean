/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveIdealVanishingBaseChange

/-!
# Independence of the algebra coordinates of vanishing equations

Transporting the full ideal along an algebra isomorphism preserves its
coefficient ideal. This compares affine charts using their actual coordinate
maps, without a choice of projective embedding in the result.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.ProjectiveIdealVanishing
variable (R B D : Type) [CommRing R] [CommRing B] [CommRing D]
  [Algebra R B] [Algebra R D] (e : B ≃ₐ[R] D) (J : Ideal B)
  (A : Type) [CommRing A] [Algebra R A]

/-- An algebra isomorphism transports the full extended ideal in tensor coordinates. -/
theorem extendedIdeal_equiv :
    (J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map
      (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) e).toRingHom =
        (J.map e.toRingHom).map
          (Algebra.TensorProduct.includeRight : D →ₐ[R] A ⊗[R] D).toRingHom := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1

/-- Coordinate changes preserve vanishing under every test algebra. -/
theorem extendedIdeal_equiv_eq_bot_iff :
    (J.map e.toRingHom).map
      (Algebra.TensorProduct.includeRight : D →ₐ[R] A ⊗[R] D).toRingHom = ⊥ ↔
        J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom = ⊥ := by
  rw [← extendedIdeal_equiv R B D e J A]
  exact Ideal.map_eq_bot_iff_of_injective
    (f := (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) e).toRingHom)
    (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) e).injective

variable [Module.Projective R B] [Module.Projective R D]

/-- The coefficient ideal is intrinsic to the algebra and its ideal. -/
theorem ideal_equiv : ideal R D (J.map e.toRingHom) = ideal R B J := by
  have h (I : Ideal R) : ideal R D (J.map e.toRingHom) ≤ I ↔ ideal R B J ≤ I := by
    have hk : RingHom.ker (algebraMap R (R ⧸ I)) = I := by
      simp only [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    rw [← hk, ← extendedIdeal_eq_bot_iff_coefficients,
      ← extendedIdeal_eq_bot_iff_coefficients]
    exact extendedIdeal_equiv_eq_bot_iff R B D e J (R ⧸ I)
  exact le_antisymm ((h _).mpr le_rfl) ((h _).mp le_rfl)

end FLT.Mazur.ProjectiveIdealVanishing
