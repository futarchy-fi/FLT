/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenImmersionLocalizationCriterion
public import FLT.Mazur.FiniteLocalizedIntegerComparisons
public import FLT.Mazur.IntegerModelDiagramTransport
public import FLT.Mazur.PrincipalRestrictionEquivalence

/-!
# Descending an affine open immersion with fixed principal refinements

A finite source cover whose target denominators recover principal opens in
an open immersion's image suffices. The canonical restrictions become
bijective together, so the transported map is itself an open immersion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- A fixed finite refinement descends an open immersion after coefficient enlargement. -/
theorem exists_integer_model_openImmersion_of_refinement {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀]
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (φ : B →ₐ[A] C) [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))]
    (hf : ∀ b, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      φ (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    {I : Type v} [Finite I] (x : I → P.ModelOfHasCoeffs A₀)
    (hcover : (⨆ i, PrimeSpectrum.basicOpen (f (x i))) = ⊤)
    (hx : ∀ i, (PrimeSpectrum.basicOpen
      (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ x i)) : Set (PrimeSpectrum B)) ⊆
        Set.range (Spec.map (CommRingCat.ofHom φ.toRingHom)))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : P.HasCoeffs S, ∃ _hQ : Q.HasCoeffs S,
        IsOpenImmersion (Spec.map
          (CommRingCat.ofHom (integerModelTransportHom P Q h f).toRingHom)) := by
  let e := fun i ↦ principalTargetAlgEquiv φ
    (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ x i))
    (Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f (x i))) (hf (x i)).symm (hx i)
  have he (i) (b) : e i (algebraMap B _ (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b))) =
      algebraMap C _ (Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b)) := by
    rw [principalTargetAlgEquiv_algebraMap]
    exact congrArg (algebraMap C _) (hf b).symm
  obtain ⟨S, hS, hsS, h, hP, hQ, hlocal⟩ :=
    exists_integer_model_finite_localized_comparisons P Q A₀ f x (fun i ↦ f (x i))
      (fun _ ↦ rfl) e he s hs
  let := hP
  let := hQ
  refine ⟨S, hS, hsS, h, hP, hQ, ?_⟩
  apply isOpenImmersion_of_localized_bijective
    (integerModelTransportHom P Q h f).toRingHom (fun i ↦ integerModelTransition P h (x i))
  · change (⨆ i, PrimeSpectrum.basicOpen
      (integerModelTransportHom P Q h f (integerModelTransition P h (x i)))) = ⊤
    simpa only [integerModelTransportHom_transition] using
      integerModelTransition_principal_cover Q h (fun i ↦ f (x i)) hcover
  · intro i
    have hi := hlocal i
    rw [← integerModelTransportHom_transition P Q h f (x i)] at hi
    obtain ⟨e₁, he₁⟩ := hi
    exact restriction_bijective_of_chart_equiv _ _ e₁.toRingEquiv he₁

end FLT.Mazur.Approximation
