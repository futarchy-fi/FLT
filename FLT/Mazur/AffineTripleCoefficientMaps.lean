/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineDirectTriplePureTransport

/-!
# Additive maps in the last-pair transport diagram

Bundle the actual scaled pair12 lift followed by pair23 transport, and the
coefficient action followed by the direct third-coordinate chart. The latter
map evaluates on arbitrary and pure tensors. Equality of these two maps is
the remaining compatibility obligation.
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

private theorem tensor_diagram_tmul {A B N : Type u}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup N] [Module A N]
    [Module B N] [IsScalarTower A B N]
    (E : N ⊗[A] B ≃ₗ[B] B ⊗[A] N) (a t : B) (n : N) :
    (E.toLinearMap.restrictScalars A).lTensor B
      ((TensorProduct.assoc A B N B) ((a ⊗ₜ[A] n) ⊗ₜ[A] t)) =
      a ⊗ₜ[A] E (n ⊗ₜ[A] t) := rfl

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
variable (e : AffineGeometricOverlap.Overlap R S M)

/-- The actual last-pair transport applied to the scaled pair12 lift, as an additive map. -/
def coefficientTransport (t : S) : S ⊗[R] coefficients S M →+
    moduleSpecΓFunctor.obj (coordinate R S M (coord3 R S)) :=
  (moduleSpecΓFunctor.map (transport23 R S M e).hom).hom.toAddMonoidHom.comp
    ((smulAddHom (Triple R S)
      (moduleSpecΓFunctor.obj ((pullback (Spec.map (CommRingCat.ofHom (coord2 R S)))).obj M))
        (coord3 R S t)).comp
      ((mappedUnit (CommRingCat.ofHom (pair12 R S).toRingHom) _
        (comparison (right R S) (pair12 R S).toRingHom
          (coord2 R S) (pair12_right R S) M).hom).comp
        (secondSections R S M).toAddMonoidHom))

/-- The last-slot coefficient action followed by the direct third-coordinate chart. -/
def coefficientAction (t : S) : S ⊗[R] coefficients S M →+
    moduleSpecΓFunctor.obj (coordinate R S M (coord3 R S)) :=
  (sections R S M).toAddMonoidHom.comp
    ((((AffineGeometricOverlap.tensorEquiv R S M e).toLinearMap.restrictScalars R).lTensor S).comp
      ((TensorProduct.assoc R S (coefficients S M) S).toLinearMap.comp
        ((TensorProduct.mk R (S ⊗[R] coefficients S M) S).flip t))).toAddMonoidHom

/-- Evaluate the coefficient action before taking the direct section chart. -/
theorem coefficientAction_apply (t : S) (x : S ⊗[R] coefficients S M) :
    coefficientAction R S M e t x =
    sections R S M
      (((AffineGeometricOverlap.tensorEquiv R S M e).toLinearMap.restrictScalars R).lTensor S
        ((TensorProduct.assoc R S (coefficients S M) S) (x ⊗ₜ[R] t))) := rfl

/-- The coefficient action on a pure tensor. -/
theorem coefficientAction_tmul (a t : S) (n : coefficients S M) :
    let x : coefficients S M ⊗[R] S := n ⊗ₜ[R] t
    coefficientAction R S M e t (a ⊗ₜ[R] n) =
      sections R S M (a ⊗ₜ[R] (AffineGeometricOverlap.tensorEquiv R S M e x)) :=
  (coefficientAction_apply R S M e t (a ⊗ₜ[R] n)).trans
    (congrArg (sections R S M)
      (tensor_diagram_tmul (AffineGeometricOverlap.tensorEquiv R S M e) a t n))

end FLT.Mazur.AffineDirectTripleTransport
