/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelSurjectiveDescent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed immersions descend between fixed affine models

This supplies the affine closedness ingredient for descending a diagonal.
The recovered morphism must be a closed immersion, but the initial model
need not be one. No assertion of global properness is made here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- A closed immersion of affine spectra is induced by a surjection of rings. -/
theorem surjective_of_integer_model_spec_closedImmersion {R T : CommRingCat.{u}}
    (f : R ⟶ T) [IsClosedImmersion (Spec.map f)] : Function.Surjective f := by
  have h := (Spec.map f).app_surjective ⊤ (isAffineOpen_top _)
  have he : f = (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop ≫
      (Scheme.ΓSpecIso T).hom := by simp
  rw [he]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso T).hom).surjective.comp
    (h.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).surjective)

/-- An affine closed immersion descends after enlarging the fixed coefficient models. -/
theorem exists_integer_model_closedImmersion {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀]
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (φ : B →ₐ[A] C) [IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))]
    (hf : ∀ b, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      φ (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : P.HasCoeffs S, ∃ _hQ : Q.HasCoeffs S,
        IsClosedImmersion (Spec.map
          (CommRingCat.ofHom (integerModelTransportHom P Q h f).toRingHom)) := by
  obtain ⟨S, hS, hsS, h, hP, hQ, hsurj⟩ := exists_integer_model_surjective P Q A₀ f φ
    (surjective_of_integer_model_spec_closedImmersion (CommRingCat.ofHom φ.toRingHom)) hf s hs
  let := hP
  let := hQ
  exact ⟨S, hS, hsS, h, hP, hQ, IsClosedImmersion.spec_of_surjective _ hsurj⟩

end FLT.Mazur.Approximation
