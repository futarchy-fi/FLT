/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InfinitesimalCotangentDerivation
public import FLT.Mazur.AdicModuleIdealTransport
public import FLT.Mazur.AdicDerivationCompletion

/-!
# Derivatives with values in completed original cotangent spaces

Complete the tensor-valued original derivation and change the module
filtration to the target ideal. The completed presenting ring acts through
the actual completed projection onto the target algebra.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicPresentationDerivation

open AdicExtensionProjection
open scoped TensorProduct

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (P : Algebra.Extension R A) (I : Ideal A)

/-- Cotangent-space completion can be computed over either original scalar ring. -/
def scalarEquiv : AdicCompletion (ideal P I) P.CotangentSpace ≃ₗ[P.Ring]
    AdicCompletion I P.CotangentSpace :=
  AdicModuleIdealTransport.equiv (ideal P I) I (ideal_map P I)

/-- The scalar comparison uses the genuine completed projection. -/
theorem scalarEquiv_smul (a : AdicCompletion (ideal P I) P.Ring)
    (x : AdicCompletion (ideal P I) P.CotangentSpace) :
    scalarEquiv P I (a • x) = projection P I a • scalarEquiv P I x := by
  have he (L J : Ideal A) (h : L = J) (b : AdicCompletion L A) :
      idealEquiv (R := P.Ring) h b = idealEquiv (R := R) h b := by
    subst J
    rfl
  have hh := AdicModuleIdealTransport.equiv_smul (ideal P I) I (ideal_map P I) a x
  change scalarEquiv P I (a • x) = idealEquiv (R := P.Ring) (ideal_map P I)
    (AdicCompletionScalars.algebraMapCompletion (ideal P I) a) • scalarEquiv P I x at hh
  rw [he] at hh
  exact hh

/-- Scalar comparison preserves each original cotangent vector. -/
@[simp] theorem scalarEquiv_of (x : P.CotangentSpace) :
    scalarEquiv P I (AdicCompletion.of (ideal P I) P.CotangentSpace x) =
      AdicCompletion.of I P.CotangentSpace x :=
  AdicModuleIdealTransport.equiv_of (ideal P I) I (ideal_map P I) x

/-- The completed presenting ring acts through the actual projection. -/
local instance spaceModule : Module (AdicCompletion (ideal P I) P.Ring)
    (AdicCompletion I P.CotangentSpace) :=
  Module.compHom _ (projection P I).toRingHom

/-- Differentiate completed sections into the completion of the ORIGINAL cotangent space. -/
def derivation : Derivation R (AdicCompletion (ideal P I) P.Ring)
    (AdicCompletion I P.CotangentSpace) where
  toLinearMap := (scalarEquiv P I).toLinearMap.restrictScalars R |>.comp
    (AdicDerivationFiltration.completion
      (InfinitesimalCotangentDerivation.derivation P) (ideal P I)).toLinearMap
  map_one_eq_zero' := by
    change scalarEquiv P I (AdicDerivationFiltration.completion
      (InfinitesimalCotangentDerivation.derivation P) (ideal P I) 1) = 0
    rw [Derivation.map_one_eq_zero, map_zero]
  leibniz' a b := by
    change scalarEquiv P I (AdicDerivationFiltration.completion
      (InfinitesimalCotangentDerivation.derivation P) (ideal P I) (a * b)) = _
    rw [Derivation.leibniz, map_add, scalarEquiv_smul, scalarEquiv_smul]
    rfl

/-- Original sections have their original tensor-valued differential. -/
theorem derivation_of (x : P.Ring) :
    derivation P I (AdicCompletion.of (ideal P I) P.Ring x) =
      AdicCompletion.of I P.CotangentSpace
        (1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x) := by
  change scalarEquiv P I (AdicDerivationFiltration.completion
    (InfinitesimalCotangentDerivation.derivation P) (ideal P I)
      (AdicCompletion.of (ideal P I) P.Ring x)) = _
  rw [AdicDerivationFiltration.completion_of, scalarEquiv_of]
  rfl

end FLT.Mazur.AdicPresentationDerivation
