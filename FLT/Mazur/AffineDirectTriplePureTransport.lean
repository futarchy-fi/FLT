/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineDirectTripleMiddleBalance
public import FLT.Mazur.AffineDirectTripleTransport

/-!
# Last-pair transport on pure coefficient tensors

The actual last-pair sheaf transport agrees with applying the coefficient
isomorphism in the last two tensor slots.
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
/-- Keep the scalar and section types fixed when changing tensor notation. -/
theorem outer_smul (Q : (Spec (.of (Triple R S))).Modules) (a : S)
    (x : moduleSpecΓFunctor.obj Q) :
    (a ⊗ₜ[R] (1 : S ⊗[R] S)) • x =
      @HSMul.hSMul (Triple R S) _ (moduleSpecΓFunctor.obj Q) _
        (a ⊗ₜ[R] (1 : S ⊗[R] S)) x := rfl


variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
variable (e : AffineGeometricOverlap.Overlap R S M)

/-- The last-pair transport agrees with the overlap on a pure inner tensor. -/
theorem transport23_tmul (a t : S) (n : coefficients S M) :
    let x : coefficients S M ⊗[R] S := n ⊗ₜ[R] t
    moduleSpecΓFunctor.map (transport23 R S M e).hom
      (coord3 R S t • mappedUnit (CommRingCat.ofHom (pair12 R S).toRingHom) _
        (comparison (right R S) (pair12 R S).toRingHom
          (coord2 R S) (pair12_right R S) M).hom (secondSections R S M (a ⊗ₜ[R] n))) =
      sections R S M (a ⊗ₜ[R] (AffineGeometricOverlap.tensorEquiv R S M e x)) :=
  let hb := AffineDirectTripleMiddleBalance.middleLift_balance R S M n a t
  let hn := outer_smul R S
    ((pullback (Spec.map (CommRingCat.ofHom (coord2 R S)))).obj M) a
    (mappedUnit (CommRingCat.ofHom (pair23 R S).toRingHom) _
      (comparison (left R S) (pair23 R S).toRingHom
        (coord2 R S) (pair23_left R S) M).hom (firstSections R S M (n ⊗ₜ[R] t)))
  (congrArg (fun y ↦ moduleSpecΓFunctor.map
    (transport R S M (pair23 R S) (coord2 R S) (coord3 R S)
      (pair23_left R S) (pair23_right R S) e).hom y) (hb.trans hn)).trans
    (transport23_outer R S M e a (n ⊗ₜ[R] t))

end FLT.Mazur.AffineDirectTripleTransport
