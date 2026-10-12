/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationOpenSaturation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The original endpoint cover of a saturated open

The second endpoint maps the first endpoint's inverse image of a source open
surjectively onto its saturation. For an etale relation this is an actual
etale scheme cover, retaining every arrow with first endpoint in the open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeRelationOrbit
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (hq : IsOpenMap q.left)
  (W : U.left.Opens)

/-- Every original arrow starting in the open ends in its full saturation. -/
theorem saturationCover_domain_le : p.left ⁻¹ᵁ W ≤ q.left ⁻¹ᵁ (saturateOpen e hq W).val := by
  intro a ha
  exact ⟨p.left a, ha, projection_pair e a⟩

/-- The original second endpoint, with its exact source and target domains. -/
def saturationCover : (p.left ⁻¹ᵁ W).toScheme ⟶ (saturateOpen e hq W).val.toScheme :=
  q.left.resLE _ _ (saturationCover_domain_le e hq W)

/-- The cover recovers the unchanged second endpoint on the original arrow domain. -/
@[reassoc]
theorem saturationCover_comp_ι :
    saturationCover e hq W ≫ (saturateOpen e hq W).val.ι =
      (p.left ⁻¹ᵁ W).ι ≫ q.left :=
  q.left.resLE_comp_ι _

instance saturationCover_surjective : Surjective (saturationCover e hq W) where
  surj x := by
    have hx : x.val ∈ q.left '' (p.left ⁻¹' W) := by
      rw [← saturateOpen_coe e hq W]
      exact x.property
    obtain ⟨a, ha, hx⟩ := hx
    refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
    exact (q.left.coe_resLE_apply _ _).trans hx

instance saturationCover_etale [Etale q.left] : Etale (saturationCover e hq W) := by
  unfold saturationCover
  infer_instance

/-- The quotient image of an affine source open is compact. -/
theorem orbitImageOpen_isCompact (hW : IsAffineOpen W) :
    IsCompact ((orbitImageOpen e hq W : TopologicalSpace.Opens (Orbit e)) : Set (Orbit e)) :=
  hW.isCompact.image (projection_continuous e)

/-- Every orbit in this quotient neighborhood has an original representative in the affine open. -/
theorem orbitImageOpen_representative (z : Orbit e) (hz : z ∈ orbitImageOpen e hq W) :
    ∃ x ∈ W, projection e x = z := hz

end FLT.Mazur.RelativeRelationOrbit
