/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonCoefficientStage
public import FLT.Mazur.PrincipalChartIntegerDescent
public import FLT.Mazur.LocalizedIntegerComparisonTransport
public import FLT.Mazur.PrincipalIntegerRestriction

/-!
# Simultaneous descent of localized restrictions

A finite family of canonical restrictions recovering isomorphisms becomes a
family of localized chart equivalences at one common coefficient stage.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- Finitely many localized comparisons descend together, retaining the actual map. -/
theorem exists_integer_model_finite_localized_comparisons {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀]
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    {I : Type v} [Finite I]
    (x : I → P.ModelOfHasCoeffs A₀) (y : I → Q.ModelOfHasCoeffs A₀)
    (hxy : ∀ i, f (x i) = y i)
    (e : ∀ i, Localization.Away (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ x i)) ≃ₐ[A]
      Localization.Away (Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ y i)))
    (he : ∀ i b, e i (algebraMap B _ (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b))) =
      algebraMap C _ (Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b)))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : P.HasCoeffs S, ∃ _hQ : Q.HasCoeffs S,
        ∀ i, ∃ e₁ : Localization.Away (integerModelTransition P h (x i)) ≃ₐ[S]
          Localization.Away (integerModelTransition Q h (y i)),
          ∀ b, e₁ (algebraMap _ _ b) =
            algebraMap _ _ (integerModelTransportHom P Q h f b) := by
  classical
  have hex (i) := exists_integer_model_localized_chart_comparison P Q A₀ (x i) (y i) f
    (principalRestrictionAlgHom f (x i) (y i) (hxy i))
    (principalRestrictionAlgHom_algebraMap f (x i) (y i) (hxy i)) (e i)
    (principalIntegerModel_restriction_recovery (P.tensorModelOfHasCoeffsEquiv A₀)
      (Q.tensorModelOfHasCoeffsEquiv A₀) f (x i) (y i) (hxy i) (e i).toAlgHom (he i))
    ∅ Set.finite_empty
  choose R hR _ h₀R hPR hQR eR heR using hex
  obtain ⟨S, hS, hsS, h₀S, hRS⟩ := exists_common_coefficient_extension A₀ R hR s hs
  let hPS : P.HasCoeffs S := integerModel_hasCoeffs_mono P h₀S
  let hQS : Q.HasCoeffs S := integerModel_hasCoeffs_mono Q h₀S
  refine ⟨S, hS, hsS, h₀S, hPS, hQS, fun i ↦ ?_⟩
  let := hPR i
  let := hQR i
  have hi := integerModel_localized_comparison_transport P Q (hRS i)
    (integerModelTransition P (h₀R i) (x i)) (integerModelTransition Q (h₀R i) (y i))
    (integerModelTransportHom P Q (h₀R i) f) (eR i) (heR i)
  rw [integerModelTransition_trans P (h₀R i) (hRS i),
    integerModelTransition_trans Q (h₀R i) (hRS i)] at hi
  simpa only [integerModelTransportHom_trans] using hi

end FLT.Mazur.Approximation
