/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineDirectTripleAdditivity
public import FLT.Mazur.AffineScaledTripleTransport

/-!
# Last-pair transport in direct triple coordinates

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
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
variable (e : AffineGeometricOverlap.Overlap R S M)

/-- Scalar multiples of a last-pair lift transport to the direct chart.
The explicit scalar action keeps the tensor-ring and pullback instances aligned. -/
theorem transport23_outer (a : S) (x : coefficients S M ⊗[R] S) :
    moduleSpecΓFunctor.map (transport R S M (pair23 R S) (coord2 R S) (coord3 R S)
      (pair23_left R S) (pair23_right R S) e).hom
      (@HSMul.hSMul (Triple R S) _
        (moduleSpecΓFunctor.obj ((pullback
          (Spec.map (CommRingCat.ofHom (coord2 R S)))).obj M)) _ (a ⊗ₜ[R] (1 : S ⊗[R] S))
        (mappedUnit (CommRingCat.ofHom (pair23 R S).toRingHom) _
          (comparison (left R S) (pair23 R S).toRingHom
            (coord2 R S) (pair23_left R S) M).hom (firstSections R S M x))) =
      sections R S M (a ⊗ₜ[R] AffineGeometricOverlap.tensorEquiv R S M e x) := by
  have h := AffineScaledTripleTransport.transport_smul_sections R S M e
    (pair23 R S) (coord2 R S) (coord3 R S) (pair23_left R S) (pair23_right R S)
    (a ⊗ₜ[R] (1 : S ⊗[R] S)) x
  have h' := (directSections_outer R S M a (AffineGeometricOverlap.tensorEquiv R S M e x)).symm
  have hfinal := h.trans h'
  exact hfinal

end FLT.Mazur.AffineDirectTripleTransport
