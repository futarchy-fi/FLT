/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOpenSelectorRelativeKernel
public import FLT.Mazur.RelativeRelationFppfInvariantQuotient

/-!
# The assembled scheme represents the original restricted invariant quotient

The proved full scheme kernel and the constructed etale surjection identify
the invariant locally ringed quotient, including all its regular functions.
This represents precisely the original source union; coverage of the whole
original parameter scheme remains an additional construction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationOpenSelector
open RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] sourceOpen projection glued
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) [Etale q.left]

/-- The original restricted invariant quotient is the constructed glued scheme. -/
def invariantIso : invariantLocallyRingedSpace (relativeEquivalence e) ≅
    (glued e).toLocallyRingedSpace := by
  let _ : Etale (relativeProjection e).left := projection_etale e
  let _ : Surjective (relativeProjection e).left := projection_surjective e
  exact fppfInvariantQuotientIso (relativeEquivalence e) (relativeProjection e)
    (relative_isPullback e)

/-- The structure-sheaf comparison retains the actual original source projection. -/
@[reassoc]
theorem invariantIso_projection :
    invariantLocallyRingedProjection (relativeEquivalence e) ≫ (invariantIso e).hom =
      (projection e).toLRSHom := by
  let _ : Etale (relativeProjection e).left := projection_etale e
  let _ : Surjective (relativeProjection e).left := projection_surjective e
  exact fppfInvariantQuotientIso_projection (relativeEquivalence e) (relativeProjection e)
    (relative_isPullback e)

/-- The invariant-quotient identification preserves the unchanged ground map. -/
theorem invariantIso_ground : (invariantIso e).hom ≫ (ground e).toLRSHom =
    invariantLocallyRingedBaseMap (relativeEquivalence e) := by
  let _ : Etale (relativeProjection e).left := projection_etale e
  let _ : Surjective (relativeProjection e).left := projection_surjective e
  exact fppfInvariantQuotientIso_baseMap (relativeEquivalence e) (relativeProjection e)
    (relative_isPullback e)

end FLT.Mazur.SchemeRelationOpenSelector
