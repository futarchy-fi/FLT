/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTripleOverlapPullback
public import FLT.Mazur.AffineScaledPullbackSections

/-!
# Scalar transport on the normalized triple overlap

Transport of a scaled pair section follows from the conjugated pullback law.
The tensor-ring specialization keeps the scalar instances consistent before
substituting concrete coordinate pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineScaledTripleTransport
open AffineOverlapTensor AffineOverlapPullback AffineTripleOverlapMaps
open AffineTripleOverlapPullback
open AffineIteratedPullbackSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
variable (e : AffineGeometricOverlap.Overlap R S M)

/-- Scalar multiples of normalized pair sections respect transport. -/
theorem transport_smul_comparison (p : S ⊗[R] S →ₐ[R] Triple R S)
    (i j : S →+* Triple R S)
    (hi : p.toRingHom.comp (left R S) = i) (hj : p.toRingHom.comp (right R S) = j)
    (c : Triple R S) (x : coefficients S M ⊗[R] S) :
    moduleSpecΓFunctor.map (transport R S M p i j hi hj e).hom
      (c • mappedUnit (CommRingCat.ofHom p.toRingHom) _
        (comparison (left R S) p.toRingHom i hi M).hom (firstSections R S M x)) =
      c • mappedUnit (CommRingCat.ofHom p.toRingHom) _
        (comparison (right R S) p.toRingHom j hj M).hom
          (moduleSpecΓFunctor.map e.hom (firstSections R S M x)) := by
  rw [transport_hom]
  exact AffineScaledPullbackSections.mappedUnit_map_smul_triple R S
    (CommRingCat.ofHom p.toRingHom)
    (comparison (left R S) p.toRingHom i hi M)
    (comparison (right R S) p.toRingHom j hj M) e.hom c (firstSections R S M x)
/-- Normalized pair transport is the tensor overlap after arbitrary scaling. -/
theorem transport_smul_sections (p : S ⊗[R] S →ₐ[R] Triple R S)
    (i j : S →+* Triple R S)
    (hi : p.toRingHom.comp (left R S) = i) (hj : p.toRingHom.comp (right R S) = j)
    (c : Triple R S) (x : coefficients S M ⊗[R] S) :
    moduleSpecΓFunctor.map (transport R S M p i j hi hj e).hom
      (c • mappedUnit (CommRingCat.ofHom p.toRingHom) _
        (comparison (left R S) p.toRingHom i hi M).hom (firstSections R S M x)) =
      c • mappedUnit (CommRingCat.ofHom p.toRingHom) _
        (comparison (right R S) p.toRingHom j hj M).hom
          (secondSections R S M (AffineGeometricOverlap.tensorEquiv R S M e x)) := by
  rw [AffineGeometricOverlap.tensorEquiv_sections]
  exact transport_smul_comparison R S M e p i j hi hj c x


end FLT.Mazur.AffineScaledTripleTransport
