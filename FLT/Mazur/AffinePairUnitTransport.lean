/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGeometricTensorCocycle
public import FLT.Mazur.AffinePullbackHomExt

/-!
# Pair transport on unit sections

The pair pullback formula at the unit coefficient evaluates the actual
sheaf transport without expanding tensor-product constructions.
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

/-- Normalized pair transport on a unit section is the unit-factor tensor overlap. -/
theorem transport_unitSection (p : S ⊗[R] S →ₐ[R] Triple R S)
    (i j : S →+* Triple R S)
    (hi : p.toRingHom.comp (left R S) = i) (hj : p.toRingHom.comp (right R S) = j)
    (n : coefficients S M) :
    moduleSpecΓFunctor.map (transport R S M p i j hi hj e).hom (unitSection R S M i n) =
      mappedUnit (CommRingCat.ofHom p.toRingHom) _
        (comparison (right R S) p.toRingHom j hj M).hom
        (secondSections R S M (AffineGeometricOverlap.tensorEquiv R S M e
          (n ⊗ₜ[R] (1 : S) : coefficients S M ⊗[R] S))) := by
  have h := transport_sections R S M p i j hi hj e
    (n ⊗ₜ[R] (1 : S) : coefficients S M ⊗[R] S)
  have hf := first_normalized R S M p.toRingHom i hi n 1
  have hs : p.toRingHom ((1 : S) ⊗ₜ[R] (1 : S)) = 1 := map_one p.toRingHom
  have hu := (congrArg
    (fun c : Triple R S ↦ c • unitSection R S M i n) hs).trans
    (one_smul (Triple R S) (unitSection R S M i n))
  have hm := congrArg (moduleSpecΓFunctor.map (transport R S M p i j hi hj e).hom)
    (hf.trans hu).symm
  exact hm.trans h

end FLT.Mazur.AffineDirectTripleTransport
