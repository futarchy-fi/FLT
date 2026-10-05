/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGeometricTensorDatum
public import FLT.Mazur.AffineReverseOverlapCocycle
public import FLT.Mazur.AffineReverseOverlapDiagonal

/-!
# Exact comparison of geometric and tensor overlap data

Tensor descent data reconstruct an actual sheaf overlap with diagonal and
cocycle identities. The geometric and tensor constructions are mutually inverse.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricOverlap
open AffineOverlapPullback AffineOverlapDiagonal AffineTripleOverlapPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
variable (D : AffineTensorCocycle.Datum R S (coefficients S M))

/-- Reconstruct the actual overlap of a tensor descent datum. -/
def fromDatum : Overlap R S M := fromTensor R S M D.overlap D.other_smul

/-- Reconstruction preserves the specified tensor isomorphism exactly. -/
theorem tensorEquiv_fromDatum : tensorEquiv R S M (fromDatum R S M D) = D.overlap :=
  tensorEquiv_fromTensor R S M D.overlap D.other_smul

/-- The tensor diagonal law gives the actual geometric diagonal equation. -/
theorem fromDatum_diagonal : DiagonalCompatible R S M (fromDatum R S M D) := by
  apply diagonalCompatible_of_tensor R S M
  rw [tensorEquiv_fromDatum]
  exact D.diagonal

/-- The tensor cocycle law gives the actual geometric cocycle equation. -/
theorem fromDatum_cocycle : CocycleCompatible R S M (fromDatum R S M D) := by
  apply AffineDirectTripleTransport.cocycleCompatible_of_tensor_unit R S M
  rw [tensorEquiv_fromDatum]
  exact fun n ↦ D.cocycle n 1 1

omit [M.IsQuasicoherent] in
/-- Tensor data are determined by their overlap; all other fields are equations. -/
theorem datum_ext_overlap {D E : AffineTensorCocycle.Datum R S (coefficients S M)}
    (h : D.overlap = E.overlap) : D = E := by
  cases D
  cases E
  cases h
  rfl

/-- Forward conversion of the reconstructed geometry returns the specified tensor datum. -/
theorem toDatum_fromDatum :
    toDatum R S M (fromDatum R S M D) (fromDatum_diagonal R S M D)
      (fromDatum_cocycle R S M D) = D :=
  datum_ext_overlap R S M (tensorEquiv_fromDatum R S M D)

/-- The reverse conversion of an actual geometric datum returns its overlap exactly. -/
theorem fromDatum_toDatum (e : Overlap R S M)
    (hd : DiagonalCompatible R S M e) (hc : CocycleCompatible R S M e) :
    fromDatum R S M (toDatum R S M e hd hc) = e :=
  fromTensor_tensorEquiv R S M e

end FLT.Mazur.AffineGeometricOverlap
