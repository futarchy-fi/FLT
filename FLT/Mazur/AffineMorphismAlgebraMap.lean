/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Algebra maps of affine morphisms over a coefficient spectrum

A morphism of spectra respecting their coefficient maps determines an actual
algebra homomorphism, whose spectrum is the original morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (f : Spec (.of B) ⟶ Spec (.of A))
variable (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
  Spec.map (CommRingCat.ofHom (algebraMap R B)))

/-- The actual algebra map determined by an affine morphism over the coefficient base. -/
def affineOverAlgHom : A →ₐ[R] B :=
  { (Spec.preimage f).hom with
    commutes' := by
      intro r
      have h : CommRingCat.ofHom (algebraMap R A) ≫ Spec.preimage f =
          CommRingCat.ofHom (algebraMap R B) := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage]
        exact hf
      exact congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of B ↦ k r) h }

/-- Taking the spectrum of the recovered algebra map returns the original morphism. -/
theorem affineOverAlgHom_spec :
    Spec.map (CommRingCat.ofHom (affineOverAlgHom R A B f hf).toRingHom) = f :=
  Spec.map_preimage f

end FLT.Mazur
