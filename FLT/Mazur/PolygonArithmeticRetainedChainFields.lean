/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainState

/-!
# Measured next fields on every retained-chain edge

Select the full next Laurent field of each actual compatible overlap. Every
internal edge and both boundary edges retain all coefficients in one fixed
integral lift. No predecessor edge is introduced when the chain has depth zero.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticRetainedChain
open PolygonArithmeticStages PolygonArithmeticSimultaneous
variable {R : Type*} [CommRing R] {π : R} {n : ℕ}
  (B : (m : ℕ) →
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])
  (S : State R π n) (hS : S.Compatible) (hB : CompatibleEquiv B)

include hS hB

/-- Normalization of every actual retained-chain edge descends to earlier quotients. -/
theorem State.normalized_restriction {k m : ℕ} (hkm : k ≤ m) (hm : S.Normalized B m) :
    S.Normalized B k := by
  intro e b
  have h := laurentSystem_identity_restriction (fun i ↦ (S.error B e b i).toAlgHom)
    (S.error_compatible B hS hB e b) hkm
    (congrArg AlgEquiv.toAlgHom (S.error_normalized B m hm e b))
  ext z : 1
  apply (edgeBase B e k).symm.injective
  have hz := DFunLike.congr_fun h z
  change (edgeBase B e k).symm (S.edgeEquiv e k b z) = z at hz
  exact hz.trans ((edgeBase B e k).symm_apply_apply z).symm

variable (r : ℕ) (hr : S.Normalized B r) (e : Edge n) (b : Bool)

/-- Measure the entire next error of each boundary or internal edge. -/
def State.nextField : (Quotient R π (r + 1))[T;T⁻¹] :=
  laurentSystemNextField (fun m ↦ (S.error B e b m).toAlgHom)
    (S.error_compatible B hS hB e b) r
    (congrArg AlgEquiv.toAlgHom (S.error_normalized B r hr e b))

/-- Every coefficient of each complete next error is represented by its measured field. -/
theorem State.nextField_subst :
    (S.error B e b (r + 1)).toAlgHom =
      LaurentSquareZeroAutomorphism.subst (parameter R π (r + 1) ^ (r + 1))
        (nextCorrectionParameter_square R π r) (S.nextField B hS hB r hr e b) :=
  laurentSystemNextField_subst (fun m ↦ (S.error B e b m).toAlgHom)
    (S.error_compatible B hS hB e b) r
    (congrArg AlgEquiv.toAlgHom (S.error_normalized B r hr e b))

/-- One fixed integral field for the full measured error at every retained-chain position. -/
def State.nextIntegralField : R[T;T⁻¹] :=
  integralCorrectionLift R π (r + 1) (S.nextField B hS hB r hr e b)

/-- The chosen integral field retains every measured coefficient on its defining quotient. -/
theorem State.nextIntegralField_spec :
    correctionField R π (r + 1) (S.nextIntegralField B hS hB r hr e b) =
      S.nextField B hS hB r hr e b := integralCorrectionLift_spec R π _ _

end FLT.Mazur.PolygonArithmeticRetainedChain
