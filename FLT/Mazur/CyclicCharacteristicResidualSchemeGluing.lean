/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicResidualOverlapGraph

/-!
# Gluing the actual full residual affine quotient charts

The graph overlaps give scheme gluing data and the full triple cocycle.
Gluing recovers the original orbit scheme and retains each residual chart map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Scheme gluing data on the actual full residual spectra and their graph overlaps. -/
def residualSchemeGlueData : Scheme.GlueData :=
  (affineResidualSchemeCover n).gluedCover

/-- The gluing overlap is exactly the proved actual residual scheme overlap. -/
theorem residualSchemeGlueData_overlap (i j : InvariantAffineIndex n) :
    (residualSchemeGlueData n).V (i, j) = residualSchemeOverlap n i j := rfl

/-- The overlap's first gluing map retains its original left projection. -/
theorem residualSchemeGlueData_left (i j : InvariantAffineIndex n) :
    (residualSchemeGlueData n).f i j = residualSchemeOverlapLeft n i j := rfl

/-- The transition followed by inclusion retains the original right graph projection. -/
@[reassoc] theorem residualSchemeGlueData_right (i j : InvariantAffineIndex n) :
    (residualSchemeGlueData n).t i j ≫ (residualSchemeGlueData n).f j i =
      residualSchemeOverlapRight n i j :=
  pullbackSymmetry_hom_comp_fst _ _

/-- The actual full residual overlap transitions satisfy the scheme triple cocycle. -/
theorem residualSchemeGlueData_cocycle (i j k : InvariantAffineIndex n) :
    (residualSchemeGlueData n).t' i j k ≫ (residualSchemeGlueData n).t' j k i ≫
      (residualSchemeGlueData n).t' k i j = 𝟙 _ :=
  (residualSchemeGlueData n).cocycle i j k

/-- Gluing the full residual spectra recovers the original invariant orbit scheme. -/
def residualSchemeGluingIso :
    (residualSchemeGlueData n).glued ≅ invariantOrbitScheme n :=
  asIso (affineResidualSchemeCover n).fromGlued

/-- The gluing isomorphism preserves every original full residual chart inclusion. -/
@[reassoc] theorem residualSchemeGluingIso_chart (i : InvariantAffineIndex n) :
    (residualSchemeGlueData n).ι i ≫ (residualSchemeGluingIso n).hom =
      affineResidualInclusion n i :=
  (affineResidualSchemeCover n).ι_fromGlued i

end FLT.Mazur.CyclicCharacteristicOrbit
