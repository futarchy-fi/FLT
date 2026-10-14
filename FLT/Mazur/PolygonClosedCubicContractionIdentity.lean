/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonClosedCubicContractionFactorization
public import FLT.Mazur.PolygonPinchingFlatBaseChange
public import FLT.Mazur.ReducedSurjectiveIsoCancellation

/-!
# The global one-gon comparison is unchanged over the full cubic identity open

The original polygon map is an isomorphism over its actual cubic identity
neighborhood. Schematic cancellation through the proper surjective contraction
descends this property to the global one-gon comparison, with the full inverse image.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "d" => closedPointContraction K n h i
local notation "a" => Over.Hom.left (closedPointContractionComparison K n h i)
local notation "U" => completePointIdentityBaseChangeOpen K n h (completeClosedBase K) i

/-- The whole inverse image of the original cubic identity neighborhood is unchanged. -/
theorem closedPointContractionComparison_identity_isIso : IsIso ((a) ∣_ (U)) := by
  let _ : Surjective (d) := PolygonOneGonContraction.contraction_surjective K n (by omega)
    (PolygonCyclicAtlas.normalization K n h) (PolygonCyclicAtlas.nodes K n h)
    (PolygonCyclicPushout.isPushout K n h (by omega)) i
  let _ : IsProper (d) := PolygonOneGonContraction.contraction_proper K n (by omega)
    (PolygonCyclicAtlas.normalization K n h) (PolygonCyclicAtlas.nodes K n h)
    (PolygonCyclicPushout.isPushout K n h (by omega)) i
  let _ : IsIso (((d) ≫ (a)) ∣_ (U)) := by
    rw [closedPointContractionComparison_fac]
    exact closedPointToCubic_identity_isIso K n h i
  exact ReducedSurjectiveIsoCancellation.isIso_restrict (d) (a) (U)

/-- The inverse over the actual target open, without replacing its full source preimage. -/
def closedPointContractionComparisonIdentityIso :
    ((a) ⁻¹ᵁ (U)).toScheme ≅ (U).toScheme := by
  let _ := closedPointContractionComparison_identity_isIso K n h i
  exact asIso ((a) ∣_ (U))

/-- The inverse retains the actual global comparison on the full open preimage. -/
@[reassoc] theorem closedPointContractionComparisonIdentityIso_inv :
    (closedPointContractionComparisonIdentityIso K n h i).inv ≫
      ((a) ⁻¹ᵁ (U)).ι ≫ (a) = (U).ι := by
  let _ := closedPointContractionComparison_identity_isIso K n h i
  rw [← morphismRestrict_ι, ← Category.assoc]
  change ((closedPointContractionComparisonIdentityIso K n h i).inv ≫
    (closedPointContractionComparisonIdentityIso K n h i).hom) ≫ (U).ι = _
  rw [Iso.inv_hom_id, Category.id_comp]

end FLT.Mazur.PolygonInfinitesimalStages
