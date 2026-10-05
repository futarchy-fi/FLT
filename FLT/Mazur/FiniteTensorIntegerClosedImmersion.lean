/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorIntegerModelTransport
public import FLT.Mazur.FiniteClosedImmersionIntegerDescent

/-!
# Simultaneous closedness of finitely many overlap product maps

A finite family of overlaps that are closed in their recovered chart
products becomes closed in the actual products at one coefficient stage.
The maps are precisely the transported original restrictions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- Finitely many closed overlap maps into products descend at a common stage. -/
theorem exists_finite_tensor_integer_closedImmersions {A : Type u} [CommRing A]
    {I : Type v} [Finite I] (B C D : I → Type u)
    [∀ i, CommRing (B i)] [∀ i, CommRing (C i)] [∀ i, CommRing (D i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra A (C i)] [∀ i, Algebra A (D i)]
    (n m r t k l : I → ℕ)
    (P : ∀ i, Algebra.Presentation A (B i) (Fin (n i)) (Fin (m i)))
    (Q : ∀ i, Algebra.Presentation A (C i) (Fin (r i)) (Fin (t i)))
    (T : ∀ i, Algebra.Presentation A (D i) (Fin (k i)) (Fin (l i)))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [∀ i, (P i).HasCoeffs A₀] [∀ i, (Q i).HasCoeffs A₀] [∀ i, (T i).HasCoeffs A₀]
    (f : ∀ i, (P i).ModelOfHasCoeffs A₀ →ₐ[A₀] (T i).ModelOfHasCoeffs A₀)
    (g : ∀ i, (Q i).ModelOfHasCoeffs A₀ →ₐ[A₀] (T i).ModelOfHasCoeffs A₀)
    (φ : ∀ i, B i →ₐ[A] D i) (ψ : ∀ i, C i →ₐ[A] D i)
    [∀ i, IsClosedImmersion (Spec.map
      (CommRingCat.ofHom (Algebra.TensorProduct.productMap (φ i) (ψ i)).toRingHom))]
    (hf : ∀ i b, (T i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f i b) =
      φ i ((P i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (hg : ∀ i c, (T i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ g i c) =
      ψ i ((Q i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ c)))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : ∀ i, (P i).HasCoeffs S,
        ∃ _hQ : ∀ i, (Q i).HasCoeffs S, ∃ _hT : ∀ i, (T i).HasCoeffs S,
          ∀ i, IsClosedImmersion (Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.productMap (integerModelTransportHom (P i) (T i) h (f i))
              (integerModelTransportHom (Q i) (T i) h (g i))).toRingHom)) := by
  obtain ⟨S, hS, hsS, h, hPQ, hT, hc⟩ := exists_integer_model_finite_closedImmersions
    (fun i ↦ B i ⊗[A] C i) D _ _ k l (fun i ↦ tensorIntegerPresentation (P i) (Q i) A₀) T
    A₀ (fun i ↦ tensorIntegerModelMap (P i) (Q i) (T i) A₀ (f i) (g i))
    (fun i ↦ Algebra.TensorProduct.productMap (φ i) (ψ i))
    (fun i ↦ tensorIntegerModelMap_recovery (P i) (Q i) (T i) A₀
      (f i) (g i) (φ i) (ψ i) (hf i) (hg i)) s hs
  let := hPQ
  let := hT
  let hP : ∀ i, (P i).HasCoeffs S := fun i ↦ integerModel_hasCoeffs_mono (P i) h
  let hQ : ∀ i, (Q i).HasCoeffs S := fun i ↦ integerModel_hasCoeffs_mono (Q i) h
  refine ⟨S, hS, hsS, h, hP, hQ, hT, fun i ↦ ?_⟩
  have hi := hc i
  rw [tensorIntegerModelMap_transport] at hi
  have he : CommRingCat.ofHom
      (((Algebra.TensorProduct.productMap (integerModelTransportHom (P i) (T i) h (f i))
        (integerModelTransportHom (Q i) (T i) h (g i))).comp
          (tensorIntegerPresentationEquivAt (P i) (Q i) h).toAlgHom).toRingHom) =
      CommRingCat.ofHom (tensorIntegerPresentationEquivAt (P i) (Q i) h).toRingHom ≫
        CommRingCat.ofHom (Algebra.TensorProduct.productMap
          (integerModelTransportHom (P i) (T i) h (f i))
          (integerModelTransportHom (Q i) (T i) h (g i))).toRingHom := rfl
  rw [he, Spec.map_comp] at hi
  let : IsIso (CommRingCat.ofHom (tensorIntegerPresentationEquivAt (P i) (Q i) h).toRingHom) :=
    (tensorIntegerPresentationEquivAt (P i) (Q i) h).toRingEquiv.toCommRingCatIso.isIso_hom
  exact (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ _).mp hi

end FLT.Mazur.Approximation
