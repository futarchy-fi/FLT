/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryLineComparison
public import FLT.Mazur.PolygonCompleteCoefficientReconstruction

/-!
# Adic quotients of the coefficient line are original boundary powers

Combine the actual closed-stage quotient comparison with the isomorphism
constructed from original boundary sections. Projection retains the
adjunction map of that explicit isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family completeCoefficientBoundaryIso

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual positive adic quotient is the pushforward of the original boundary power. -/
def completeCoefficientBoundaryQuotientIso (m : ℕ) :
    quotient (compatibleProjAdicIdeal K n h) (completeCoefficientLine K n h) (m + 1) ≅
      (pushforward (originalStageToCompatibleProj K n h m)).obj
        (tensorPower (boundaryLine K m n h) (completeCoefficientBoundaryExponent K n h)) :=
  completeCoefficientQuotientStageIso K n h m ≪≫
    (pushforward (originalStageToCompatibleProj K n h m)).mapIso
      (completeCoefficientBoundaryIso K n h m)

/-- Restriction to the original boundary power uses the constructed coefficient comparison. -/
def completeCoefficientBoundaryRestriction (m : ℕ) :
    completeCoefficientLine K n h ⟶
      (pushforward (originalStageToCompatibleProj K n h m)).obj
        (tensorPower (boundaryLine K m n h) (completeCoefficientBoundaryExponent K n h)) :=
  (pullbackPushforwardAdjunction (originalStageToCompatibleProj K n h m)).homEquiv _ _
    (completeCoefficientBoundaryIso K n h m).hom

/-- The original quotient projection is exactly this boundary restriction. -/
@[reassoc] theorem projection_completeCoefficientBoundaryQuotientIso (m : ℕ) :
    projection (compatibleProjAdicIdeal K n h) (completeCoefficientLine K n h) (m + 1) ≫
      (completeCoefficientBoundaryQuotientIso K n h m).hom =
        completeCoefficientBoundaryRestriction K n h m := by
  rw [completeCoefficientBoundaryQuotientIso, Iso.trans_hom, ← Category.assoc,
    projection_completeCoefficientQuotientStageIso]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
