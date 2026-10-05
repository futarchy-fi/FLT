/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSquareScalarExtension
public import FLT.Mazur.EnlargedPresentationModel
public import FLT.Mazur.IntegerModelIsomorphismDescent

/-!
# Descending bijectivity of a scalar-extended map

For finitely presented algebras over an integer coefficient ring, a map
which becomes bijective over the original base becomes bijective over a
larger finite-type coefficient ring. The resulting map is the scalar
extension of the given map, rather than an unspecified isomorphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- Bijectivity after scalar extension is witnessed at a finite coefficient stage. -/
theorem exists_integer_scalarExtension_bijective {A : Type u} [CommRing A]
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    {B₀ C₀ : Type u} [CommRing B₀] [CommRing C₀] [Algebra A₀ B₀] [Algebra A₀ C₀]
    [Algebra.FinitePresentation A₀ B₀] [Algebra.FinitePresentation A₀ C₀]
    (f : B₀ →ₐ[A₀] C₀)
    (hf : Function.Bijective (affineScalarExtensionHom (S := A) f))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
        Function.Bijective (affineScalarExtensionHom (S := S) f) := by
  let P₀ := Algebra.Presentation.ofFinitePresentation A₀ B₀
  let Q₀ := Algebra.Presentation.ofFinitePresentation A₀ C₀
  let eP := (AlgEquiv.refl : A ⊗[A₀] B₀ ≃ₐ[A] A ⊗[A₀] B₀)
  let eQ := (AlgEquiv.refl : A ⊗[A₀] C₀ ≃ₐ[A] A ⊗[A₀] C₀)
  let P := integerBaseChangedPresentation A₀ P₀ eP
  let Q := integerBaseChangedPresentation A₀ Q₀ eQ
  let dP := integerBaseChangedModelEquiv A₀ P₀ eP
  let dQ := integerBaseChangedModelEquiv A₀ Q₀ eQ
  let F := dQ.symm.toAlgHom.comp (f.comp dP.toAlgHom)
  let e := AlgEquiv.ofBijective (affineScalarExtensionHom (S := A) f) hf
  have hF (b) : Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ F b) =
      e (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)) := by
    rw [integerBaseChangedModelEquiv_recovery, integerBaseChangedModelEquiv_recovery]
    change (1 : A) ⊗ₜ dQ (dQ.symm (f (dP b))) = 1 ⊗ₜ f (dP b)
    rw [AlgEquiv.apply_symm_apply]
  obtain ⟨S, hS, hsS, h, hP, hQ, eS, heS, _⟩ :=
    exists_integer_model_isomorphism P Q A₀ F e hF s hs
  let := hP
  let := hQ
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  let dPS := integerBaseChangedModelEquivAt A₀ P₀ eP h
  let dQS := integerBaseChangedModelEquivAt A₀ Q₀ eQ h
  let E := (dPS.symm.trans eS).trans dQS
  have hE : E.toAlgHom = affineScalarExtensionHom (S := S) f := by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro b
    change dQS (eS (dPS.symm (1 ⊗ₜ b))) = 1 ⊗ₜ f b
    rw [integerBaseChangedModelEquivAt_symm_one_tmul, heS,
      integerBaseChangedModelEquivAt_transition]
    change (1 : S) ⊗ₜ dQ (dQ.symm (f (dP (dP.symm b)))) = 1 ⊗ₜ f b
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  refine ⟨S, hS, hsS, h, ?_⟩
  rw [← hE]
  exact E.bijective

end FLT.Mazur.Approximation
