/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGeometricTensorCocycle
public import FLT.Mazur.AffineOverlapDiagonal

/-!
# From a geometric overlap to a tensor descent datum

The actual sheaf overlap determines the tensor isomorphism. Its geometric
diagonal and cocycle identities supply the corresponding tensor equations;
the second scalar law follows from sheaf linearity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricOverlap
open AffineOverlapPullback AffineTripleOverlapPullback AffineOverlapDiagonal
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
variable (e : Overlap R S M)
variable (hd : DiagonalCompatible R S M e) (hc : CocycleCompatible R S M e)

-- Align the concrete coefficient instances when filling the cocycle field.
set_option maxRecDepth 2048 in
/-- Convert the geometric overlap, with its diagonal and cocycle, to tensor descent data. -/
def toDatum : AffineTensorCocycle.Datum R S (coefficients S M) where
  overlap := tensorEquiv R S M e
  other_smul := tensorEquiv_other_smul R S M e
  diagonal := tensorEquiv_diagonal R S M e hd
  cocycle := AffineDirectTripleTransport.tensorEquiv_cocycle R S M e hc

/-- The constructed datum retains the specified coefficient isomorphism. -/
theorem toDatum_overlap : (toDatum R S M e hd hc).overlap = tensorEquiv R S M e := rfl

/-- The datum reconstructs the original sheaf overlap on coefficient sections. -/
theorem toDatum_overlap_sections (x : coefficients S M ⊗[R] S) :
    secondSections R S M ((toDatum R S M e hd hc).overlap x) =
      moduleSpecΓFunctor.map e.hom (firstSections R S M x) :=
  tensorEquiv_sections R S M e x

/-- The associated coaction is the original overlap evaluated at the unit factor. -/
theorem toDatum_coaction_apply (n : coefficients S M) :
    (toDatum R S M e hd hc).coaction n = tensorEquiv R S M e
      (n ⊗ₜ[R] (1 : S) : coefficients S M ⊗[R] S) := rfl

end FLT.Mazur.AffineGeometricOverlap
