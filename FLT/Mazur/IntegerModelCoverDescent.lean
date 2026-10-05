/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FixedModelElementLifts
public import FLT.Mazur.IntegerModelDiagramTransport
public import FLT.Mazur.IntegerModelEventualEquality

/-!
# Descending principal covers of fixed models

A finite family whose recovered principal opens cover becomes a cover after
enlargement. The proof lifts coefficients of a unit-ideal equation and then
kills its error at a later stage; recovery need not be injective.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- A recovered finite principal cover descends with its explicit unit-ideal witness. -/
theorem exists_integer_model_principal_cover {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] {n m : ℕ}
    (P : Algebra.Presentation A B (Fin n) (Fin m))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀] [P.HasCoeffs A₀]
    {I : Type v} [Fintype I] (x : I → P.ModelOfHasCoeffs A₀)
    (hx : (⨆ i, PrimeSpectrum.basicOpen
      (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ x i))) = ⊤)
    (s : Set A) (hs : s.Finite) :
    ∃ A₁ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₁ ∧ s ⊆ A₁ ∧
      ∃ h : A₀ ≤ A₁, ∃ _hP : P.HasCoeffs A₁,
        ∃ c : I → P.ModelOfHasCoeffs A₁,
          (∑ i, c i * integerModelTransition P h (x i) = 1) ∧
          (⨆ i, PrimeSpectrum.basicOpen (integerModelTransition P h (x i))) = ⊤ := by
  classical
  have hspan := PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp hx
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    (show (1 : B) ∈ Ideal.span (Set.range fun i ↦
      P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ x i)) by rw [hspan]; trivial)
  obtain ⟨A₁, hA₁, hs₁, h₀₁, hP₁, c₁, hc₁⟩ :=
    exists_fixed_model_element_lifts P A₀ c s hs
  let := hP₁
  let := hA₁
  let z := ∑ i, c₁ i * integerModelTransition P h₀₁ (x i) - 1
  have hz : P.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ z) = 0 := by
    change integerModelRecoveryHom P z = 0
    simp only [z, map_sub, map_sum, map_mul, map_one, integerModelRecoveryHom_apply,
      hc₁, integerModelTransition_recovery, hc, sub_self]
  obtain ⟨A₂, hA₂, hs₂, h₁₂, hP₂, hz₂⟩ :=
    exists_integer_model_eventual_zero P A₁ (fun _ : Unit ↦ z) (fun _ ↦ hz) s hs
  let := hP₂
  have heq : ∑ i, integerModelTransition P h₁₂ (c₁ i) *
      integerModelTransition P (h₀₁.trans h₁₂) (x i) = 1 := by
    have hh := hz₂ ()
    simpa only [z, map_sub, map_sum, map_mul, map_one,
      integerModelTransition_trans, sub_eq_zero] using hh
  refine ⟨A₂, hA₂, hs₂, h₀₁.trans h₁₂, hP₂,
    fun i ↦ integerModelTransition P h₁₂ (c₁ i), heq, ?_⟩
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr
  apply Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
  exact Ideal.mem_span_range_iff_exists_fun.mpr
    ⟨fun i ↦ integerModelTransition P h₁₂ (c₁ i), heq⟩

end FLT.Mazur.Approximation
