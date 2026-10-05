/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonCoefficientStage
public import FLT.Mazur.IntegerModelEventualEquality
public import FLT.Mazur.IntegerModelHomTransport

/-!
# Simultaneous eventual equations for elements of coordinate models

Finitely many recovered element equalities, in possibly different rings,
become actual equalities after one common coefficient enlargement. The
proof uses eventual vanishing, without assuming injectivity of recovery.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v w

/-- Recovered element equations in a finite family of models hold at a common later stage. -/
theorem exists_integer_model_finite_element_relations {A : Type u} [CommRing A]
    {I : Type v} [Finite I] (B : I → Type u)
    [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    (n m : I → ℕ) (P : ∀ i, Algebra.Presentation A (B i) (Fin (n i)) (Fin (m i)))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀] [∀ i, (P i).HasCoeffs A₀]
    (K : I → Type w) [∀ i, Finite (K i)]
    (x y : ∀ i, K i → (P i).ModelOfHasCoeffs A₀)
    (hxy : ∀ i k, (P i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ x i k) =
      (P i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ y i k))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : ∀ i, (P i).HasCoeffs S,
        ∀ i k, integerModelTransition (P i) h (x i k) =
          integerModelTransition (P i) h (y i k) := by
  classical
  have hz (i k) : (P i).tensorModelOfHasCoeffsEquiv A₀
      (1 ⊗ₜ (x i k - y i k)) = 0 := by
    simp only [TensorProduct.tmul_sub, map_sub, hxy, sub_self]
  have hex (i) := exists_integer_model_eventual_zero (P i) A₀
    (fun k ↦ x i k - y i k) (hz i) ∅ Set.finite_empty
  choose R hR _ h₀R hPR heq using hex
  obtain ⟨S, hS, hsS, h₀S, hRS⟩ := exists_common_coefficient_extension A₀ R hR s hs
  let hPS : ∀ i, (P i).HasCoeffs S := fun i ↦ integerModel_hasCoeffs_mono (P i) h₀S
  refine ⟨S, hS, hsS, h₀S, hPS, fun i k ↦ ?_⟩
  let := hPR i
  have h := congrArg (integerModelTransition (P i) (hRS i)) (heq i k)
  simpa only [integerModelTransition_trans, map_sub, map_zero, sub_eq_zero] using h

end FLT.Mazur.Approximation
