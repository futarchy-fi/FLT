/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelFiniteDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper affine morphisms descend to fixed coefficient models

An affine proper morphism is finite. Descending its integral generators
therefore descends properness. This only concerns affine morphisms: it is
not the missing properness descent theorem for a general glued scheme.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- A fixed map of affine models recovering a proper morphism eventually becomes proper. -/
theorem exists_integer_model_affine_proper {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀]
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (φ : B →ₐ[A] C) [IsProper (Spec.map (CommRingCat.ofHom φ.toRingHom))]
    (hf : ∀ b, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      φ (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : P.HasCoeffs S, ∃ _hQ : Q.HasCoeffs S,
        IsProper (Spec.map
          (CommRingCat.ofHom (integerModelTransportHom P Q h f).toRingHom)) := by
  have hfin : IsFinite (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  obtain ⟨S, hS, hsS, h, hP, hQ, hfinite⟩ := exists_integer_model_finite P Q A₀ f φ
    ((IsFinite.SpecMap_iff _).mp hfin) hf s hs
  let := hP
  let := hQ
  have : IsFinite (Spec.map
      (CommRingCat.ofHom (integerModelTransportHom P Q h f).toRingHom)) :=
    (IsFinite.SpecMap_iff _).mpr hfinite
  exact ⟨S, hS, hsS, h, hP, hQ, inferInstance⟩

end FLT.Mazur.Approximation
