/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePresentationIntegerModel
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Affine schemes over finite-type integer rings

The coefficient models give cartesian squares of schemes, including for a
finite family of affine charts over the same base. This is the affine part
of approximation, before descending overlap maps and gluing the charts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- A tensor-product model gives the required cartesian square on spectra. -/
theorem integerModel_isPullback {A₀ A B₀ B : Type u}
    [CommRing A₀] [CommRing A] [CommRing B₀] [CommRing B]
    [Algebra A₀ A] [Algebra A₀ B₀] [Algebra A B]
    (e : A ⊗[A₀] B₀ ≃ₐ[A] B) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀)))
      (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) := by
  apply isPullback_SpecMap_of_isPushout
  apply ((CommRingCat.isPushout_tensorProduct A₀ A B₀).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toRingEquiv.toCommRingCatIso
    (by simp) (by simp) ?_ ?_).flip
  · ext x
    exact e.commutes x
  · rfl

/-- Simultaneous affine approximation over a common finite-type integer base. -/
theorem exists_common_affine_integer_models {A : Type u} [CommRing A]
    {ι : Type v} [Finite ι] (B : ι → Type u)
    [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    [∀ i, Algebra.FinitePresentation A (B i)] (s : Set A) (hs : s.Finite) :
    ∃ A₀ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₀ ∧ s ⊆ A₀ ∧
      ∀ i, ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)),
        IsAffine X₀ ∧ LocallyOfFinitePresentation f₀ ∧
          ∃ p : Spec (CommRingCat.of (B i)) ⟶ X₀,
            IsPullback p (Spec.map (CommRingCat.ofHom (algebraMap A (B i)))) f₀
              (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) := by
  obtain ⟨A₀, hA₀, hs₀, h⟩ := exists_common_integer_models (A := A) B s hs
  refine ⟨A₀, hA₀, hs₀, fun i ↦ ?_⟩
  obtain ⟨B₀, _, _, hB₀, ⟨e⟩⟩ := h i
  refine ⟨Spec (CommRingCat.of B₀), Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀)),
    inferInstance, ?_, _, integerModel_isPullback e⟩
  simpa only [LocallyOfFinitePresentation.SpecMap_iff,
    CommRingCat.hom_ofHom, RingHom.finitePresentation_algebraMap] using hB₀

/-- A finitely presented affine scheme is a base change of an affine scheme
of finite presentation over a finite-type integer subalgebra. -/
theorem exists_affine_integer_model {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.FinitePresentation A B] :
    ∃ A₀ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₀ ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)),
        IsAffine X₀ ∧ LocallyOfFinitePresentation f₀ ∧
          ∃ p : Spec (CommRingCat.of B) ⟶ X₀,
            IsPullback p (Spec.map (CommRingCat.ofHom (algebraMap A B))) f₀
              (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) := by
  obtain ⟨A₀, hA₀, _, h⟩ := exists_common_affine_integer_models (A := A)
    (fun _ : Unit ↦ B) ∅ Set.finite_empty
  exact ⟨A₀, hA₀, h ()⟩

end FLT.Mazur.Approximation
