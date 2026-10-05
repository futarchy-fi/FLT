/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelDiagramTransport
public import FLT.Mazur.IntegerModelEventualEquality

/-!
# Descending equations between transported model maps

Maps that agree after recovery become equal on an enlarged model. This
establishes triangle equations, such as cocycles, from their recovered laws;
no equality at the initial coefficient stage is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- Recovered equality becomes equality of the full transported algebra maps. -/
theorem exists_integer_model_transport_eq {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀]
    (f g : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (hfg : ∀ b, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ g b))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : P.HasCoeffs S, ∃ _hQ : Q.HasCoeffs S,
        integerModelTransportHom P Q h f = integerModelTransportHom P Q h g := by
  let : Algebra.FiniteType ℤ (P.ModelOfHasCoeffs A₀) :=
    Algebra.FiniteType.trans (R := ℤ) (S := A₀) inferInstance inferInstance
  obtain ⟨S, hS, hsS, h, hQ, heq⟩ :=
    exists_integer_model_eventual_hom_eq Q A₀ f.toRingHom g.toRingHom hfg s hs
  let := hQ
  let hP : P.HasCoeffs S := integerModel_hasCoeffs_mono P h
  refine ⟨S, hS, hsS, h, hP, hQ, ?_⟩
  apply integerModel_hom_ext P h
  intro b
  simp only [integerModelTransportHom_transition]
  exact RingHom.congr_fun heq b

/-- A recovered triangle law, including a triple-overlap cocycle, descends. -/
theorem exists_integer_model_triangle {A B C D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D] {n m r t p q : ℕ}
    (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (T : Algebra.Presentation A D (Fin p) (Fin q))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀] [T.HasCoeffs A₀]
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (g : Q.ModelOfHasCoeffs A₀ →ₐ[A₀] T.ModelOfHasCoeffs A₀)
    (k : P.ModelOfHasCoeffs A₀ →ₐ[A₀] T.ModelOfHasCoeffs A₀)
    (hk : ∀ b, T.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ g (f b)) =
      T.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ k b))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : P.HasCoeffs S, ∃ _hQ : Q.HasCoeffs S,
        ∃ _hT : T.HasCoeffs S,
          (integerModelTransportHom Q T h g).comp (integerModelTransportHom P Q h f) =
            integerModelTransportHom P T h k := by
  obtain ⟨S, hS, hsS, h, hP, hT, heq⟩ :=
    exists_integer_model_transport_eq P T A₀ (g.comp f) k hk s hs
  let := hP
  let := hT
  let hQ : Q.HasCoeffs S := integerModel_hasCoeffs_mono Q h
  refine ⟨S, hS, hsS, h, hP, hQ, hT, ?_⟩
  rw [← integerModelTransportHom_comp, heq]

end FLT.Mazur.Approximation
