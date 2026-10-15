/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantMap

/-!
# Open maps between invariant orbit spaces

An open source comparison induces an open map of orbit spaces when the
original relation is open. Its image saturates under the entire original
relation, including arrows absent from the new relation. This asserts
openness of the underlying map, not an open immersion of ringed spaces.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S S' : Scheme.{u}} {A U : Over S} {A' U' : Over S'}
  {p q : A ⟶ U} {p' q' : A' ⟶ U'}
  (e : CategoryTheory.EquivalenceRelation p q)
  (e' : CategoryTheory.EquivalenceRelation p' q')
  (g : U'.left ⟶ U.left) (r : A'.left ⟶ A.left)
  (hp : r ≫ p.left = p'.left ≫ g) (hq : r ≫ q.left = q'.left ≫ g)
local notation "m" => invariantMap e e' g r hp hq

/-- Images are computed using the full original orbit projection. -/
theorem invariantMap_image (O : Set (Orbit e')) :
    (m).base '' O = projection e '' (g '' (projection e' ⁻¹' O)) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := projection_surjective e' y
    exact ⟨g x, ⟨x, hy, rfl⟩, (invariantMap_projection_apply e e' g r hp hq x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨projection e' x, hx, invariantMap_projection_apply e e' g r hp hq x⟩

/-- Open source maps give open quotient maps without requiring equality of the two relations. -/
theorem invariantMap_isOpenMap (hg : IsOpenMap g) (hopen : IsOpenMap q.left) :
    IsOpenMap (m).base := by
  intro O hO
  rw [invariantMap_image e e' g r hp hq]
  exact projection_isOpenMap e hopen _ (hg _ (hO.preimage (projection_continuous e')))

/-- The image preimage is saturation by all original arrows, with independent new bases allowed. -/
theorem invariantMap_image_saturation (O : Set (Orbit e')) :
    projection e ⁻¹' ((m).base '' O) =
      q.left '' (p.left ⁻¹' (g '' (projection e' ⁻¹' O))) := by
  rw [invariantMap_image e e' g r hp hq, saturation_eq]

/-- The saturated original source image is invariant for the entire original relation. -/
theorem invariantMap_image_invariant (O : Set (Orbit e')) :
    p.left ⁻¹' (projection e ⁻¹' ((m).base '' O)) =
      q.left ⁻¹' (projection e ⁻¹' ((m).base '' O)) := by
  ext x
  change projection e (p.left x) ∈ (m).base '' O ↔
    projection e (q.left x) ∈ (m).base '' O
  rw [projection_pair e x]

end FLT.Mazur.RelativeRelationOrbit
