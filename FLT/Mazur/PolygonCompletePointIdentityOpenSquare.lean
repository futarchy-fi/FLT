/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointIdentityNeighborhoodIso
public import FLT.Mazur.CartesianOpenIsoRestriction

/-!
# The identity isomorphism as an open square on the original cubic

Compose the two affine restrictions and the original origin-neighborhood
square. The resulting square uses the original complete family and its cubic,
and is Cartesian on the entire family, including the collapsed fiber.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointIdentityAffineOpen completePointToOrigin completePointOriginOpen
  completePointWeierstrassCurve completePointIdentityIsoOpen

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "V" => completePointOriginOpen K n h i
local notation "q" => completePointToOrigin K n h i
local notation "U" => completePointIdentityAffineOpen K n h i
local notation "f" => completePointIdentityAffineMap K n h i
local notation "B" => completePointIdentityIsoOpen K n h i

/-- The identity chart's inclusion into the original integral cubic. -/
def completePointIdentityTargetInclusion : (B).toScheme ⟶ integralCurve (W) :=
  (B).ι ≫ (U).ι ≫ originNeighborhoodInclusion (W)

/-- The identity chart's inclusion into the original complete family. -/
def completePointIdentitySourceInclusion :
    ((f) ⁻¹ᵁ (B)).toScheme ⟶ exactVeroneseProj K n h :=
  ((f) ⁻¹ᵁ (B)).ι ≫ ((q) ⁻¹ᵁ (U)).ι ≫ (V).ι

instance completePointIdentityTargetInclusion_open :
    IsOpenImmersion (completePointIdentityTargetInclusion K n h i) := by
  unfold completePointIdentityTargetInclusion
  infer_instance

instance completePointIdentitySourceInclusion_open :
    IsOpenImmersion (completePointIdentitySourceInclusion K n h i) := by
  unfold completePointIdentitySourceInclusion
  infer_instance

/-- The original identity isomorphism gives a Cartesian square over the full cubic map. -/
theorem completePointIdentityNeighborhood_isPullback :
    IsPullback (completePointIdentityNeighborhoodIso K n h i).hom
      (completePointIdentitySourceInclusion K n h i)
      (completePointIdentityTargetInclusion K n h i) (g) := by
  have H : IsPullback (f) ((q) ⁻¹ᵁ (U)).ι (U).ι (q) := by
    rw [completePointIdentityAffineMap]
    exact isPullback_morphismRestrict (q) (U)
  exact (isPullback_morphismRestrict (f) (B)).paste_vert
    (H.paste_vert (completePointToOrigin_isPullback K n h i))

/-- Flatten the chosen identity chart to an actual open of the original cubic. -/
def completePointIdentityCubicOpen : (integralCurve (W)).Opens :=
  (completePointIdentityTargetInclusion K n h i).opensRange

/-- The original cubic map is an isomorphism over this actual target neighborhood. -/
theorem completePointIdentityCubicOpen_isIso :
    IsIso ((g) ∣_ completePointIdentityCubicOpen K n h i) :=
  CartesianOpenIsoRestriction.isIso_restrict
    (completePointIdentityNeighborhoodIso K n h i).hom
    (completePointIdentitySourceInclusion K n h i)
    (completePointIdentityTargetInclusion K n h i) (g)
    (completePointIdentityNeighborhood_isPullback K n h i)

end FLT.Mazur.PolygonInfinitesimalStages
