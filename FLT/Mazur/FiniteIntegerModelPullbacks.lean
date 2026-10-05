/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonCoefficientStage
public import FLT.Mazur.IntegerModelPullbackDescent
public import FLT.Mazur.IntegerModelPullbackTransport

/-!
# Simultaneous descent of affine overlap pullbacks

Finitely many recovered pullback squares become cartesian at one common
coefficient stage. Their rings and presentations may differ from square
to square. Further enlargement preserves all of their actual arrows.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- A finite family of recovered affine pullbacks descends at a common stage. -/
theorem exists_integer_model_finite_pullbacks {A : Type u} [CommRing A]
    {ι : Type v} [Finite ι] (B C D E : ι → Type u)
    [∀ a, CommRing (B a)] [∀ a, CommRing (C a)]
    [∀ a, CommRing (D a)] [∀ a, CommRing (E a)]
    [∀ a, Algebra A (B a)] [∀ a, Algebra A (C a)]
    [∀ a, Algebra A (D a)] [∀ a, Algebra A (E a)]
    (n m r t p q k l : ι → ℕ)
    (P : ∀ a, Algebra.Presentation A (B a) (Fin (n a)) (Fin (m a)))
    (Q : ∀ a, Algebra.Presentation A (C a) (Fin (r a)) (Fin (t a)))
    (R : ∀ a, Algebra.Presentation A (D a) (Fin (p a)) (Fin (q a)))
    (T : ∀ a, Algebra.Presentation A (E a) (Fin (k a)) (Fin (l a)))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [∀ a, (P a).HasCoeffs A₀] [∀ a, (Q a).HasCoeffs A₀]
    [∀ a, (R a).HasCoeffs A₀] [∀ a, (T a).HasCoeffs A₀]
    (f : ∀ a, (P a).ModelOfHasCoeffs A₀ →ₐ[A₀] (Q a).ModelOfHasCoeffs A₀)
    (g : ∀ a, (P a).ModelOfHasCoeffs A₀ →ₐ[A₀] (R a).ModelOfHasCoeffs A₀)
    (i : ∀ a, (Q a).ModelOfHasCoeffs A₀ →ₐ[A₀] (T a).ModelOfHasCoeffs A₀)
    (j : ∀ a, (R a).ModelOfHasCoeffs A₀ →ₐ[A₀] (T a).ModelOfHasCoeffs A₀)
    (F : ∀ a, B a →ₐ[A] C a) (G : ∀ a, B a →ₐ[A] D a)
    (I : ∀ a, C a →ₐ[A] E a) (J : ∀ a, D a →ₐ[A] E a)
    (hf : ∀ a b, (Q a).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f a b) =
      F a ((P a).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (hg : ∀ a b, (R a).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ g a b) =
      G a ((P a).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (hi : ∀ a c, (T a).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ i a c) =
      I a ((Q a).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ c)))
    (hj : ∀ a d, (T a).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ j a d) =
      J a ((R a).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ d)))
    (hp : ∀ a, IsPullback (Spec.map (CommRingCat.ofHom (I a).toRingHom))
      (Spec.map (CommRingCat.ofHom (J a).toRingHom))
      (Spec.map (CommRingCat.ofHom (F a).toRingHom))
      (Spec.map (CommRingCat.ofHom (G a).toRingHom))) (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : ∀ a, (P a).HasCoeffs S,
        ∃ _hQ : ∀ a, (Q a).HasCoeffs S, ∃ _hR : ∀ a, (R a).HasCoeffs S,
          ∃ _hT : ∀ a, (T a).HasCoeffs S, ∀ a,
            IsPullback
              (Spec.map (CommRingCat.ofHom
                (integerModelTransportHom (Q a) (T a) h (i a)).toRingHom))
              (Spec.map (CommRingCat.ofHom
                (integerModelTransportHom (R a) (T a) h (j a)).toRingHom))
              (Spec.map (CommRingCat.ofHom
                (integerModelTransportHom (P a) (Q a) h (f a)).toRingHom))
              (Spec.map (CommRingCat.ofHom
                (integerModelTransportHom (P a) (R a) h (g a)).toRingHom)) := by
  classical
  have hex (a) := exists_integer_model_pullback (P a) (Q a) (R a) (T a) A₀
    (f a) (g a) (i a) (j a) (F a) (G a) (I a) (J a)
    (hf a) (hg a) (hi a) (hj a) (hp a) ∅ Set.finite_empty
  choose K hK _ h₀K hPK hQK hRK hTK hpK using hex
  obtain ⟨S, hS, hsS, h₀S, hKS⟩ := exists_common_coefficient_extension A₀ K hK s hs
  let hPS : ∀ a, (P a).HasCoeffs S := fun a ↦ integerModel_hasCoeffs_mono (P a) h₀S
  let hQS : ∀ a, (Q a).HasCoeffs S := fun a ↦ integerModel_hasCoeffs_mono (Q a) h₀S
  let hRS : ∀ a, (R a).HasCoeffs S := fun a ↦ integerModel_hasCoeffs_mono (R a) h₀S
  let hTS : ∀ a, (T a).HasCoeffs S := fun a ↦ integerModel_hasCoeffs_mono (T a) h₀S
  refine ⟨S, hS, hsS, h₀S, hPS, hQS, hRS, hTS, fun a ↦ ?_⟩
  let := hPK a
  let := hQK a
  let := hRK a
  let := hTK a
  have hpa := integerModelTransportHom_preserves_pullback (P a) (Q a) (R a) (T a)
    (hKS a) (integerModelTransportHom (P a) (Q a) (h₀K a) (f a))
    (integerModelTransportHom (P a) (R a) (h₀K a) (g a))
    (integerModelTransportHom (Q a) (T a) (h₀K a) (i a))
    (integerModelTransportHom (R a) (T a) (h₀K a) (j a)) (hpK a)
  simpa only [integerModelTransportHom_trans] using hpa

end FLT.Mazur.Approximation
