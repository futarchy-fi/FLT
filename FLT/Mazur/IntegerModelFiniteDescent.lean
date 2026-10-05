/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelIntegralElements
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Finiteness descends between fixed coefficient models

The target's finitely many algebra generators become integral at a common
stage. Finite type then turns integrality into module finiteness. In
particular, this supplies properness descent for affine scheme morphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- A fixed model map recovering a finite ring map becomes finite after enlargement. -/
theorem exists_integer_model_finite {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀]
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (φ : B →ₐ[A] C) (hφ : φ.toRingHom.Finite)
    (hf : ∀ b, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      φ (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : P.HasCoeffs S, ∃ _hQ : Q.HasCoeffs S,
        (integerModelTransportHom P Q h f).toRingHom.Finite := by
  let x : Fin r → Q.ModelOfHasCoeffs A₀ := fun i ↦ Ideal.Quotient.mk _ (X i)
  obtain ⟨S, hS, hsS, h, hP, hQ, hx⟩ :=
    exists_integer_model_integral_elements P Q A₀ f φ hf x
      (fun _ ↦ hφ.to_isIntegral _) s hs
  let := hP
  let := hQ
  let fS := integerModelTransportHom P Q h f
  have hgen (i) : fS.toRingHom.IsIntegralElem (Ideal.Quotient.mk _ (X i)) := by
    simpa only [x, integerModelTransition_mk, map_X] using hx i
  have hint : fS.toRingHom.IsIntegral := by
    intro c
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
    induction p using MvPolynomial.induction_on with
    | C a =>
      change fS.toRingHom.IsIntegralElem (algebraMap S (Q.ModelOfHasCoeffs S) a)
      rw [← fS.commutes]
      exact RingHom.isIntegralElem_map _
    | add p q hp hq =>
      rw [map_add]
      exact RingHom.IsIntegralElem.add _ hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact RingHom.IsIntegralElem.mul _ hp (hgen i)
  have hft : fS.toRingHom.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap S (P.ModelOfHasCoeffs S))
    have he : fS.toRingHom.comp (algebraMap S (P.ModelOfHasCoeffs S)) =
        algebraMap S (Q.ModelOfHasCoeffs S) := fS.comp_algebraMap
    rw [he]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  exact ⟨S, hS, hsS, h, hP, hQ, hint.to_finite hft⟩

end FLT.Mazur.Approximation
