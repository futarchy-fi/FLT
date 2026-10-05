/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelOpenImmersionBaseChange

/-!
# Morphism properties persist under coefficient enlargement

The actual cartesian transition square preserves every property stable
under base change. This permits independently descended properties to be
combined at a common stage without changing the presentation models.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

/-- A property stable under base change persists under transport of a fixed model map. -/
theorem integerModelTransportHom_property {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    {A₀ A₁ : Subalgebra ℤ A}
    [P.HasCoeffs A₀] [P.HasCoeffs A₁] [Q.HasCoeffs A₀] [Q.HasCoeffs A₁]
    (h : A₀ ≤ A₁) (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (W : MorphismProperty Scheme.{u}) [W.IsStableUnderBaseChange]
    (hf : W (Spec.map (CommRingCat.ofHom f.toRingHom))) :
    W (Spec.map (CommRingCat.ofHom (integerModelTransportHom P Q h f).toRingHom)) :=
  MorphismProperty.of_isPullback (integerModelTransportHom_isPullback P Q h f) hf

end FLT.Mazur.Approximation
