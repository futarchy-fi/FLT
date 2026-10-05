/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonCoefficientStage
public import FLT.Mazur.IntegerModelRelationDescent
public import FLT.Mazur.PrincipalChartIntegerDescent

/-!
# A common coefficient stage for finitely many diagram equations

Each pair of maps may have different source and target presentations.
Recovered equalities become simultaneous equalities of the transported maps,
and the initial coefficient stage is retained even for an empty family.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- Finite recovered diagram equations hold together at one later model stage. -/
theorem exists_integer_model_finite_relations {A : Type u} [CommRing A]
    {I : Type v} [Finite I] (B C : I → Type u)
    [∀ i, CommRing (B i)] [∀ i, CommRing (C i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra A (C i)]
    (n m r t : I → ℕ)
    (P : ∀ i, Algebra.Presentation A (B i) (Fin (n i)) (Fin (m i)))
    (Q : ∀ i, Algebra.Presentation A (C i) (Fin (r i)) (Fin (t i)))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [∀ i, (P i).HasCoeffs A₀] [∀ i, (Q i).HasCoeffs A₀]
    (f g : ∀ i, (P i).ModelOfHasCoeffs A₀ →ₐ[A₀] (Q i).ModelOfHasCoeffs A₀)
    (hfg : ∀ i b, (Q i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f i b) =
      (Q i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ g i b))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : ∀ i, (P i).HasCoeffs S,
        ∃ _hQ : ∀ i, (Q i).HasCoeffs S,
          ∀ i, integerModelTransportHom (P i) (Q i) h (f i) =
            integerModelTransportHom (P i) (Q i) h (g i) := by
  classical
  have hex (i) := exists_integer_model_transport_eq (P i) (Q i) A₀
    (f i) (g i) (hfg i) ∅ Set.finite_empty
  choose R hR _ h₀R hPR hQR heq using hex
  obtain ⟨S, hS, hsS, h₀S, hRS⟩ := exists_common_coefficient_extension A₀ R hR s hs
  let hPS : ∀ i, (P i).HasCoeffs S := fun i ↦ integerModel_hasCoeffs_mono (P i) h₀S
  let hQS : ∀ i, (Q i).HasCoeffs S := fun i ↦ integerModel_hasCoeffs_mono (Q i) h₀S
  refine ⟨S, hS, hsS, h₀S, hPS, hQS, fun i ↦ ?_⟩
  let := hPR i
  let := hQR i
  have hi := congrArg (integerModelTransportHom (P i) (Q i) (hRS i)) (heq i)
  simpa only [integerModelTransportHom_trans] using hi

end FLT.Mazur.Approximation
