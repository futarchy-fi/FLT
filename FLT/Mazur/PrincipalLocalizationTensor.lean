/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Principal tensor coefficients and actual localizations

Scalar extension by a principal localization is canonically the localization
of the original coefficient algebra. Its naturality identifies extended
coefficient maps with any geometric restriction maps satisfying the original
coefficient square.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.PrincipalLocalizationTensor
variable {R A C : Type*} [CommRing R] [CommRing A] [CommRing C]
  [Algebra R A] [Algebra R C] (r : R)
  (A' : Type*) [CommRing A'] [Algebra A A']
  [IsLocalization.Away (algebraMap R A r) A']
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Actual principal scalar extension identified with the supplied coefficient localization. -/
def comparison : Localization.Away r ⊗[R] A ≃ₐ[A] A' :=
  IsLocalization.algEquiv (.powers (algebraMap R A r)) _ _

/-- The comparison retains every original coefficient. -/
theorem comparison_one_tmul (a : A) :
    comparison r A' (1 ⊗ₜ[R] a) = algebraMap A A' a :=
  (comparison r A').commutes a

variable {A'} (C' : Type*) [CommRing C'] [Algebra C C']
  [IsLocalization.Away (algebraMap R C r) C']
  (g : A →ₐ[R] C) (g' : A' →+* C')
  (hg : ∀ a, g' (algebraMap A A' a) = algebraMap C C' (g a))

include hg in
/-- Tensor extension equals the actual localized map on every tensor, including denominators. -/
theorem naturality (z : Localization.Away r ⊗[R] A) :
    comparison r C' (Algebra.TensorProduct.map (AlgHom.id (Localization.Away r) _) g z) =
      g' (comparison r A' z) := by
  have h : (comparison r C').toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id (Localization.Away r) _) g).toRingHom =
        g'.comp (comparison r A').toRingHom := by
    apply IsLocalization.ringHom_ext (.powers (algebraMap R A r))
    ext a
    change comparison r C' (1 ⊗ₜ[R] g a) = g' (comparison r A' (1 ⊗ₜ[R] a))
    rw [comparison_one_tmul, comparison_one_tmul, hg]
  exact RingHom.congr_fun h z

end FLT.Mazur.PrincipalLocalizationTensor
