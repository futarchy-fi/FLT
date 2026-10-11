/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineAlgebraDescentRelativeRelation
public import FLT.Mazur.RelativeRelationFpqcInvariantQuotient

/-!
# The constructed affine descent scheme is the original invariant quotient

Apply faithful-flat regular-function descent to the unchanged multiplicative
coaction overlap. The explicit invariant orbit quotient is Spec of the fixed
coordinate algebra, including its structure sheaf and original relative base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineAlgebraDescent
open RelativeRelationOrbit
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  (D : Data R S B) [Module.FaithfullyFlat R S]

instance relativeProjection_flat : Flat (relativeProjection D).left :=
  inferInstanceAs (Flat (schemeProjection D))

instance relativeProjection_quasiCompact : QuasiCompact (relativeProjection D).left :=
  inferInstanceAs (QuasiCompact (schemeProjection D))

instance relativeProjection_surjective : Surjective (relativeProjection D).left :=
  inferInstanceAs (Surjective (schemeProjection D))

/-- The fixed-algebra spectrum is the original invariant locally ringed quotient. -/
def invariantQuotientIso : invariantLocallyRingedSpace (relativeEquivalenceRelation D) ≅
    (descendedScheme D).toLocallyRingedSpace :=
  fpqcInvariantQuotientIso (relativeEquivalenceRelation D)
    (relativeProjection D) (relative_isPullback D)

/-- The quotient identification retains the actual coefficient-inclusion projection. -/
@[reassoc]
theorem invariantQuotientIso_projection :
    invariantLocallyRingedProjection (relativeEquivalenceRelation D) ≫
      (invariantQuotientIso D).hom = (schemeProjection D).toLRSHom :=
  fpqcInvariantQuotientIso_projection (relativeEquivalenceRelation D)
    (relativeProjection D) (relative_isPullback D)

/-- The quotient identification retains the original map to Spec R. -/
theorem invariantQuotientIso_baseMap :
    (invariantQuotientIso D).hom ≫ (schemeBase D).toLRSHom =
      invariantLocallyRingedBaseMap (relativeEquivalenceRelation D) :=
  fpqcInvariantQuotientIso_baseMap (relativeEquivalenceRelation D)
    (relativeProjection D) (relative_isPullback D)

/-- Every original coefficient point has its actual invariant-coordinate image. -/
theorem invariantQuotientIso_apply (x : Spec (.of B)) :
    (invariantQuotientIso D).hom.base (projection (relativeEquivalenceRelation D) x) =
      schemeProjection D x :=
  kernelQuotientComparison_apply (relativeEquivalenceRelation D)
    (relativeProjection D) (relative_isPullback D) x

/-- The original orbit quotient is homeomorphic to the constructed invariant spectrum. -/
def invariantOrbitHomeomorph : Orbit (relativeEquivalenceRelation D) ≃ₜ descendedScheme D :=
  TopCat.homeoOfIso (LocallyRingedSpace.forgetToTop.mapIso (invariantQuotientIso D))

end FLT.Mazur.AffineAlgebraDescent
