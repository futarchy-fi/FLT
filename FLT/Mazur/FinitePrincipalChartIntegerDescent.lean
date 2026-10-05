/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonCoefficientStage
public import FLT.Mazur.IntegerModelOpenImmersionBaseChange
public import FLT.Mazur.PrincipalChartIntegerDescent

/-!
# Simultaneous descent of finite principal chart families

Starting with fixed model maps recovering principal charts, one coefficient
enlargement makes every chart an open immersion. Empty families are allowed.
The returned maps are transports of the original maps, so existing diagram
relations can be retained independently of the choices made for each chart.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- Finitely many fixed maps recovering principal charts become open immersions
at one common finite-type integer coefficient stage. -/
theorem exists_integer_model_finite_principal_charts {A : Type u} [CommRing A]
    {I : Type v} [Finite I] (B : I → Type u)
    [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    (n m r t : I → ℕ)
    (P : ∀ i, Algebra.Presentation A (B i) (Fin (n i)) (Fin (m i)))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀] [∀ i, (P i).HasCoeffs A₀]
    (x : ∀ i, (P i).ModelOfHasCoeffs A₀)
    (Q : ∀ i, Algebra.Presentation A
      (Localization.Away ((P i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ x i)))
      (Fin (r i)) (Fin (t i))) [∀ i, (Q i).HasCoeffs A₀]
    (f : ∀ i, (P i).ModelOfHasCoeffs A₀ →ₐ[A₀] (Q i).ModelOfHasCoeffs A₀)
    (hf : ∀ i b, (Q i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f i b) =
      algebraMap (B i) _ ((P i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : ∀ i, (P i).HasCoeffs S,
        ∃ _hQ : ∀ i, (Q i).HasCoeffs S,
          ∀ i, IsOpenImmersion (Spec.map
            (CommRingCat.ofHom (integerModelTransportHom (P i) (Q i) h (f i)).toRingHom)) := by
  classical
  have hex (i) := exists_integer_model_principal_chart (P i) A₀ (x i) (Q i)
    (f i) (hf i) ∅ Set.finite_empty
  choose R hR _ h₀R hPR hQR hopen using hex
  obtain ⟨S, hS, hsS, h₀S, hRS⟩ := exists_common_coefficient_extension A₀ R hR s hs
  let hPS : ∀ i, (P i).HasCoeffs S := fun i ↦ integerModel_hasCoeffs_mono (P i) h₀S
  let hQS : ∀ i, (Q i).HasCoeffs S := fun i ↦ integerModel_hasCoeffs_mono (Q i) h₀S
  refine ⟨S, hS, hsS, h₀S, hPS, hQS, fun i ↦ ?_⟩
  let := hPR i
  let := hQR i
  have hbase := integerModelTransportHom_isOpenImmersion (P i) (Q i) (hRS i)
    (integerModelTransportHom (P i) (Q i) (h₀R i) (f i)) (hopen i)
  simpa only [integerModelTransportHom_trans] using hbase

end FLT.Mazur.Approximation
