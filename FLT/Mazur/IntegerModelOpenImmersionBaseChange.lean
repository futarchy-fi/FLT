/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntegerModel
public import FLT.Mazur.IntegerModelBaseChange
public import FLT.Mazur.IntegerModelHomTransport
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Open immersions under coefficient enlargement

Transport of a fixed model map is a base change on spectra. Thus every
open immersion already obtained at a coefficient stage persists at all
larger stages, without any flatness assumption on coefficient inclusions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- The square of spectra associated to a coefficient transition is cartesian. -/
theorem integerModelTransition_isPullback {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] {n m : ℕ}
    (P : Algebra.Presentation A B (Fin n) (Fin m))
    {A₀ A₁ : Subalgebra ℤ A} [P.HasCoeffs A₀] [P.HasCoeffs A₁] (h : A₀ ≤ A₁) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (integerModelTransition P h)))
      (Spec.map (CommRingCat.ofHom (algebraMap A₁ (P.ModelOfHasCoeffs A₁))))
      (Spec.map (CommRingCat.ofHom (algebraMap A₀ (P.ModelOfHasCoeffs A₀))))
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)) := by
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  have he : (integerModelBaseChangeEquiv P h).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom = integerModelTransition P h := by
    apply RingHom.ext
    intro b
    exact integerModelBaseChangeEquiv_one_tmul P h b
  simpa only [he, RingHom.algebraMap_toAlgebra] using
    integerModel_isPullback (integerModelBaseChangeEquiv P h)

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] {n m r t : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin m))
  (Q : Algebra.Presentation A C (Fin r) (Fin t))
  {A₀ A₁ : Subalgebra ℤ A}
  [P.HasCoeffs A₀] [P.HasCoeffs A₁] [Q.HasCoeffs A₀] [Q.HasCoeffs A₁]
  (h : A₀ ≤ A₁) (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)

/-- Transport of a fixed algebra map gives a cartesian square on spectra. -/
theorem integerModelTransportHom_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (integerModelTransition Q h)))
      (Spec.map (CommRingCat.ofHom (integerModelTransportHom P Q h f).toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom (integerModelTransition P h))) := by
  have hf : Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A₀ (P.ModelOfHasCoeffs A₀))) =
      Spec.map (CommRingCat.ofHom (algebraMap A₀ (Q.ModelOfHasCoeffs A₀))) := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact f.commutes a
  have hF : Spec.map (CommRingCat.ofHom (integerModelTransportHom P Q h f).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A₁ (P.ModelOfHasCoeffs A₁))) =
      Spec.map (CommRingCat.ofHom (algebraMap A₁ (Q.ModelOfHasCoeffs A₁))) := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact (integerModelTransportHom P Q h f).commutes a
  apply IsPullback.of_bot (t := integerModelTransition_isPullback P h)
  · simpa only [hf, hF] using integerModelTransition_isPullback Q h
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    exact (integerModelTransportHom_transition P Q h f b).symm

/-- Open immersions survive arbitrary further coefficient enlargement. -/
theorem integerModelTransportHom_isOpenImmersion
    (hf : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))) :
    IsOpenImmersion (Spec.map
      (CommRingCat.ofHom (integerModelTransportHom P Q h f).toRingHom)) :=
  IsOpenImmersion.of_isPullback (integerModelTransportHom_isPullback P Q h f) hf

end FLT.Mazur.Approximation
