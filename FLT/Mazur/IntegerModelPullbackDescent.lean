/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommutativeIntegerModelPullbackDescent
public import FLT.Mazur.IntegerModelRelationDescent
public import FLT.Mazur.PrincipalChartIntegerDescent

/-!
# Descending arbitrary recovered affine pullbacks

The recovered pullback first supplies an eventual commutative-square law.
The canonical tensor comparison then descends the pullback property itself.
Neither commutativity nor cartesianness is assumed at the initial stage.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- Any fixed model square recovering an affine pullback becomes cartesian. -/
theorem exists_integer_model_pullback {A B C D E : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D] [CommRing E]
    [Algebra A B] [Algebra A C] [Algebra A D] [Algebra A E]
    {n m r t p q k l : ℕ}
    (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (R : Algebra.Presentation A D (Fin p) (Fin q))
    (T : Algebra.Presentation A E (Fin k) (Fin l))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀] [R.HasCoeffs A₀] [T.HasCoeffs A₀]
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (g : P.ModelOfHasCoeffs A₀ →ₐ[A₀] R.ModelOfHasCoeffs A₀)
    (i : Q.ModelOfHasCoeffs A₀ →ₐ[A₀] T.ModelOfHasCoeffs A₀)
    (j : R.ModelOfHasCoeffs A₀ →ₐ[A₀] T.ModelOfHasCoeffs A₀)
    (F : B →ₐ[A] C) (G : B →ₐ[A] D) (I : C →ₐ[A] E) (J : D →ₐ[A] E)
    (hf : ∀ b, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      F (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (hg : ∀ b, R.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ g b) =
      G (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (hi : ∀ c, T.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ i c) =
      I (Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ c)))
    (hj : ∀ d, T.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ j d) =
      J (R.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ d)))
    (hp : IsPullback (Spec.map (CommRingCat.ofHom I.toRingHom))
      (Spec.map (CommRingCat.ofHom J.toRingHom))
      (Spec.map (CommRingCat.ofHom F.toRingHom))
      (Spec.map (CommRingCat.ofHom G.toRingHom))) (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : P.HasCoeffs S, ∃ _hQ : Q.HasCoeffs S,
        ∃ _hR : R.HasCoeffs S, ∃ _hT : T.HasCoeffs S,
          IsPullback
            (Spec.map (CommRingCat.ofHom (integerModelTransportHom Q T h i).toRingHom))
            (Spec.map (CommRingCat.ofHom (integerModelTransportHom R T h j).toRingHom))
            (Spec.map (CommRingCat.ofHom (integerModelTransportHom P Q h f).toRingHom))
            (Spec.map (CommRingCat.ofHom (integerModelTransportHom P R h g).toRingHom)) := by
  have hOrig : I.comp F = J.comp G := by
    have hh := hp.w
    rw [← Spec.map_comp, ← Spec.map_comp] at hh
    exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective hh))
  have hrel (b) : T.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ (i.comp f) b) =
      T.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ (j.comp g) b) := by
    simp only [AlgHom.comp_apply, hi, hj, hf, hg]
    exact AlgHom.congr_fun hOrig _
  obtain ⟨A₁, hA₁, _, h₀₁, hP₁, hT₁, heq⟩ :=
    exists_integer_model_transport_eq P T A₀ (i.comp f) (j.comp g) hrel ∅ Set.finite_empty
  let := hA₁
  let := hP₁
  let := hT₁
  let hQ₁ := integerModel_hasCoeffs_mono Q h₀₁
  let hR₁ := integerModel_hasCoeffs_mono R h₀₁
  let f₁ := integerModelTransportHom P Q h₀₁ f
  let g₁ := integerModelTransportHom P R h₀₁ g
  let i₁ := integerModelTransportHom Q T h₀₁ i
  let j₁ := integerModelTransportHom R T h₀₁ j
  have hcomm : i₁.comp f₁ = j₁.comp g₁ := by
    simpa only [integerModelTransportHom_comp] using heq
  obtain ⟨S, hS, hsS, h₁S, hPS, hQS, hRS, hTS, hpS⟩ :=
    exists_integer_model_pullback_of_commutative P Q R T A₁ f₁ g₁ i₁ j₁ hcomm F G I J
      (integerModelTransportHom_recovery P Q h₀₁ f F hf)
      (integerModelTransportHom_recovery P R h₀₁ g G hg)
      (integerModelTransportHom_recovery Q T h₀₁ i I hi)
      (integerModelTransportHom_recovery R T h₀₁ j J hj) hp s hs
  let := hPS
  let := hQS
  let := hRS
  let := hTS
  refine ⟨S, hS, hsS, h₀₁.trans h₁S, hPS, hQS, hRS, hTS, ?_⟩
  simpa only [f₁, g₁, i₁, j₁, integerModelTransportHom_trans] using hpS

end FLT.Mazur.Approximation
