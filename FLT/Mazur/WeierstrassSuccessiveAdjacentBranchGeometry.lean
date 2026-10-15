/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveLaurentSlopeGeometry

/-!
# Factoring the original adjacent overlap through a polygon branch

The original horizontal transition followed by the inverse original divided
transition factors through the older branch with the atlas edge inversion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (r₀ r₁ : SuccessiveIncidence.Coordinate π)
  (h₀ : r₀ ^ 2 + nodeSlopeLinear W π (π * b3) * r₀ =
    nodeSlopeConstant W s π (π * b4) (π ^ 2 * b6))
  (h₁ : r₁ ^ 2 + nodeSlopeLinear W π b3 * r₁ =
    nodeSlopeConstant W (s * π) π b4 b6)
  (h : inverseLeftIncidenceLaurent π r₀ = rightIncidenceLaurent π r₁)
local notation "L₀" => inverseLeftSlopeLaurent W s π (π * b3) (π * b4) (π ^ 2 * b6) r₀ h₀
local notation "U₁" => rightSlopeLaurent W (s * π) π b3 b4 b6 r₁ h₁
local notation "A" => overlapIso W s π (π * b3) (π * b4) (π ^ 2 * b6)
local notation "B" => horizontalIso W (s * π) π b3 b4 b6

include h in
/-- The two original localized transitions induce exactly the inverse-coordinate branch map. -/
@[reassoc] theorem adjacentSlopeLaurent_spec :
    Spec.map (CommRingCat.ofHom (U₁).toRingHom) ≫ (B).hom ≫ (A).inv =
      Spec.map (CommRingCat.ofHom (L₀).toRingHom) := by
  have he : Spec.map (CommRingCat.ofHom (U₁).toRingHom) ≫ (B).hom =
      Spec.map (CommRingCat.ofHom (L₀).toRingHom) ≫ (A).hom := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    simp only [← Spec.map_comp]
    exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f.toRingHom))
      (adjacentSlopeLaurent_overlap W s π b3 b4 b6 r₀ r₁ h₀ h₁ h).symm
  rw [← Category.assoc, he, Category.assoc, Iso.hom_inv_id, Category.comp_id]

include h in
/-- The whole original adjacent boundary factors through the correctly oriented older branch. -/
@[reassoc] theorem adjacentSlopeLaurent_branch_factorization :
    Spec.map (CommRingCat.ofHom (U₁).toRingHom) ≫ (B).hom ≫ (A).inv ≫
      xOpenInclusion W s π (π * b3) (π * b4) (π ^ 2 * b6) =
    (PolygonSmoothing.edgeInversion R).hom ≫ PolygonSmoothing.leftBranchOpen R π ≫
      simpleSlopePolygonChart W s π (π * b3) (π * b4) (π ^ 2 * b6) r₀ h₀ := by
  rw [adjacentSlopeLaurent_spec_assoc W s π b3 b4 b6 r₀ r₁ h₀ h₁ h,
    inverseLeftSlopeLaurent_spec_inclusion]

end FLT.Mazur.WeierstrassSuccessiveX
