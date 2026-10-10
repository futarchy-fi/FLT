/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeAffineProjection
public import FLT.Mazur.IdealAdicRelativeProjectionSections
public import FLT.Mazur.IdealAdicRelativePushforwardOpens

/-!
# Canonical coefficient recovery on affine refinements

Every affine refinement recovers its original coefficient sheaf from the
actual descended module. The recovery is independent of the ambient chart,
using the original coefficient restriction map, and is an isomorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local instance] relativeTensorChart_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback relativeChartCoefficientSheaf
attribute [local irreducible] relativeDescendedCoefficientSheaf

/-- A chart projection remains invertible after pullback to any affine subchart. -/
lemma relativeDescendedCoefficientProjection_pullback_isIso {U W : X.affineOpens}
    (i : W.1 ⟶ U.1) :
    IsIso ((pullback (relativeTensorChart J f W)).map
      (relativeDescendedCoefficientProjection J f U)) := by
  apply (NatIso.isIso_map_iff
    (restrictFunctorIsoPullback (relativeTensorChart J f W)) _).mp
  rw [Hom.isIso_iff_isIso_app]
  intro T
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact relativeDescendedCoefficientProjection_bijective J f U _
    (((relativeTensorChart J f W).image_le_opensRange T).trans
      (relativeTensorImageOpen_mono J f i))

/-- The coordinate form of the descended affine projection is invertible. -/
instance relativeDescendedAffineProjection_isIso {U W : X.affineOpens} (i : W.1 ⟶ U.1) :
    IsIso (relativeDescendedAffineProjection J f i) := by
  let _ := relativeDescendedCoefficientProjection_pullback_isIso J f i
  unfold relativeDescendedAffineProjection
  infer_instance

/-- Recover the coefficient module through an ambient chart and its actual restriction map. -/
def relativeDescendedAffineRecoveryIso {U W : X.affineOpens} (i : W.1 ⟶ U.1) :
    (pullback (relativeTensorChart J f W)).obj (relativeDescendedCoefficientSheaf J f) ≅
      relativeChartCoefficientSheaf J f W := by
  let _ := relativeCoefficientSheafMap_isIso J f i
  exact asIso (relativeDescendedAffineProjection J f i ≫ relativeCoefficientSheafMap J f i)

/-- Recovery is independent of the ambient chart used to compute the affine restriction. -/
lemma relativeDescendedAffineRecoveryIso_eq {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    relativeDescendedAffineRecoveryIso J f i = relativeDescendedAffineRecoveryIso J f j := by
  apply Iso.ext
  exact relativeDescendedAffineProjection_restriction J f i j

/-- Every ambient chart recovers the same isomorphism as the affine chart itself. -/
lemma relativeDescendedAffineRecoveryIso_eq_self {U W : X.affineOpens} (i : W.1 ⟶ U.1) :
    relativeDescendedAffineRecoveryIso J f i = relativeDescendedAffineRecoveryIso J f (𝟙 W.1) :=
  relativeDescendedAffineRecoveryIso_eq J f i (𝟙 W.1)

end FLT.Mazur.IdealAdicGradedPullback
