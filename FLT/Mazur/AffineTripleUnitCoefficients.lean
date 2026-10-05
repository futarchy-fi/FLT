/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGeometricTensorCocycle
public import FLT.Mazur.AffinePullbackHomExt

/-!
# Unit-factor triple coefficient transport

Specialize the scalar ring while the source sheaf remains abstract.
This keeps scalar normalization from expanding concrete pullback modules.
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
private theorem map_unit_smul {A B : Type u} [CommRing A] [CommRing B]
    {P Q : ModuleCat B} (i : A →+* B) (f : P ⟶ Q)
    (x : P) (y : Q) (h : f (i 1 • x) = y) : f x = y := by
  simpa only [map_one, one_smul] using h

private theorem unit_smul_eq {A B : Type u} [CommRing A] [CommRing B]
    {P : ModuleCat B} (i : A →+* B)
    (x y : P) (h : x = i 1 • y) : x = y := by
  simpa only [map_one, one_smul] using h

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
private theorem remove_unit {P Q : (Spec (.of (Triple R S))).Modules}
    (F : P ⟶ Q) (x : moduleSpecΓFunctor.obj P) (y : moduleSpecΓFunctor.obj Q)
    (h : moduleSpecΓFunctor.map F (coord3 R S 1 • x) = y) :
    moduleSpecΓFunctor.map F x = y :=
  map_unit_smul (coord3 R S) (moduleSpecΓFunctor.map F) x y h

variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
variable (e : AffineGeometricOverlap.Overlap R S M)

/-- At the unit scalar the last-pair coefficient formula has no scalar prefactor. -/
theorem transport23_unit_coefficients (x : S ⊗[R] coefficients S M) :
    moduleSpecΓFunctor.map (transport23 R S M e).hom
      (mappedUnit (CommRingCat.ofHom (pair12 R S).toRingHom) _
        (comparison (right R S) (pair12 R S).toRingHom
          (coord2 R S) (pair12_right R S) M).hom (secondSections R S M x)) =
      sections R S M
        (((AffineGeometricOverlap.tensorEquiv R S M e).toLinearMap.restrictScalars R).lTensor S
          ((TensorProduct.assoc R S (coefficients S M) S) (x ⊗ₜ[R] (1 : S)))) :=
  remove_unit R S
    (P := ((pullback (Spec.map (CommRingCat.ofHom (coord2 R S)))).obj M))
    (transport23 R S M e).hom _ _ (transport23_coefficients R S M e 1 x)

/-- Inserting the unit middle factor gives the outer-pair coefficient lift. -/
theorem sections_insertMiddle_one (x : S ⊗[R] coefficients S M) :
    sections R S M (insertMiddle (R := R) (1 : S) x) =
      mappedUnit (CommRingCat.ofHom (pair13 R S).toRingHom) _
        (comparison (right R S) (pair13 R S).toRingHom
          (coord3 R S) (pair13_right R S) M).hom (secondSections R S M x) :=
  unit_smul_eq (coord2 R S) _ _ (directSections_insertMiddle R S M 1 x)

end FLT.Mazur.AffineDirectTripleTransport
