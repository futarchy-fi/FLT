/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTripleCoefficientMaps

/-!
# Generator criterion for the actual coefficient maps

Equality of the two concrete additive maps reduces to their values on pure
tensors. The generator hypothesis is stated with the bundled transport map;
converting the existing unbundled pure transport theorem to that hypothesis
remains a separate obligation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineDirectTripleTransport
open AffineOverlapTensor AffineOverlapPullback AffineTripleOverlapMaps
open AffineTripleOverlapPullback AffineTensorCocycle AffineDirectTripleAdditivity
open AffineIteratedPullbackSections AffineLiftedOverlapCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
variable (e : AffineGeometricOverlap.Overlap R S M)

private theorem tensor_hom_ext {A B N Q : Type u}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup N] [Module A N]
    [AddCommGroup Q] (F G : B ⊗[A] N →+ Q)
    (h : ∀ a n, F (a ⊗ₜ[A] n) = G (a ⊗ₜ[A] n)) : F = G := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul a n => exact h a n
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Equality of the actual additive transport maps is determined on pure coefficients. -/
theorem coefficientMaps_eq_iff (t : S) :
    coefficientTransport R S M e t = coefficientAction R S M e t ↔
      ∀ (a : S) (n : coefficients S M),
        coefficientTransport R S M e t (a ⊗ₜ[R] n) =
          coefficientAction R S M e t (a ⊗ₜ[R] n) := by
  constructor
  · intro h a n
    exact congrArg (fun f ↦ f (a ⊗ₜ[R] n)) h
  · exact tensor_hom_ext _ _

/-- The remaining generator equation uses the already evaluated coefficient action. -/
theorem coefficientMaps_eq_of_tmul (t : S)
    (h : ∀ (a : S) (n : coefficients S M),
      let x : coefficients S M ⊗[R] S := n ⊗ₜ[R] t
      coefficientTransport R S M e t (a ⊗ₜ[R] n) =
        sections R S M (a ⊗ₜ[R] AffineGeometricOverlap.tensorEquiv R S M e x)) :
    coefficientTransport R S M e t = coefficientAction R S M e t :=
  (coefficientMaps_eq_iff R S M e t).mpr
    (fun a n ↦ (h a n).trans (coefficientAction_tmul R S M e a t n).symm)

/-- A bundled generator equation extends to all coefficient tensors. -/
theorem coefficientTransport_coefficients_of_tmul (t : S)
    (h : ∀ (a : S) (n : coefficients S M),
      let z : coefficients S M ⊗[R] S := n ⊗ₜ[R] t
      coefficientTransport R S M e t (a ⊗ₜ[R] n) =
        sections R S M (a ⊗ₜ[R] AffineGeometricOverlap.tensorEquiv R S M e z))
    (x : S ⊗[R] coefficients S M) :
    coefficientTransport R S M e t x =
      sections R S M
        (((AffineGeometricOverlap.tensorEquiv R S M e).toLinearMap.restrictScalars R).lTensor S
          ((TensorProduct.assoc R S (coefficients S M) S) (x ⊗ₜ[R] t))) :=
  (congrArg (fun f ↦ f x) (coefficientMaps_eq_of_tmul R S M e t h)).trans
    (coefficientAction_apply R S M e t x)

end FLT.Mazur.AffineDirectTripleTransport
