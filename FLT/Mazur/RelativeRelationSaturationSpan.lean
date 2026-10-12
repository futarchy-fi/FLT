/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationSaturationCover

/-!
# The original common-source span for a generating open and its saturation

The full arrow domain maps to the generating open by the first endpoint and
to its saturation by the second. Reflexivity splits the first map and recovers
the original inclusion through the second map. Both maps are etale covers when
the original endpoints are etale.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (hq : IsOpenMap q.left)
  (W : U.left.Opens)

/-- The first endpoint of the original arrow domain lands in the generating open. -/
def saturationGeneratorProjection : (p.left ⁻¹ᵁ W).toScheme ⟶ W.toScheme :=
  p.left.resLE W _ le_rfl

/-- Reflexivity takes the generating open into the original first-endpoint arrow domain. -/
theorem saturationGeneratorSection_le : W ≤ e.r.left ⁻¹ᵁ (p.left ⁻¹ᵁ W) := by
  intro x hx
  change p.left (e.r.left x) ∈ W
  have h := congrArg (fun g ↦ g.left x) e.reflexivity₁
  exact h.symm ▸ hx

/-- The actual reflexive arrows over the generating open. -/
def saturationGeneratorSection : W.toScheme ⟶ (p.left ⁻¹ᵁ W).toScheme :=
  e.r.left.resLE _ _ (saturationGeneratorSection_le e W)

/-- Reflexivity splits the first endpoint on the unchanged generating open. -/
theorem saturationGeneratorSection_projection :
    saturationGeneratorSection e W ≫ saturationGeneratorProjection (p := p) W = 𝟙 _ := by
  apply (cancel_mono W.ι).mp
  simp only [Category.assoc, saturationGeneratorProjection, Scheme.Hom.resLE_comp_ι,
    Category.id_comp]
  rw [← Category.assoc, saturationGeneratorSection, Scheme.Hom.resLE_comp_ι, Category.assoc]
  have h : e.r.left ≫ p.left = 𝟙 U.left := congrArg Over.Hom.left e.reflexivity₁
  rw [h, Category.comp_id]

/-- The second endpoint on reflexive arrows is exactly inclusion into the saturation. -/
theorem saturationGeneratorSection_cover :
    saturationGeneratorSection e W ≫ saturationCover e hq W =
      Scheme.homOfLE _ (le_saturateOpen e hq W) := by
  apply (cancel_mono (saturateOpen e hq W).val.ι).mp
  rw [Category.assoc, saturationCover_comp_ι, Scheme.homOfLE_ι, ← Category.assoc,
    saturationGeneratorSection, Scheme.Hom.resLE_comp_ι, Category.assoc]
  have h : e.r.left ≫ q.left = 𝟙 U.left := congrArg Over.Hom.left e.reflexivity₂
  rw [h, Category.comp_id]

include e in
/-- The reflexive section proves the first endpoint cover is surjective. -/
theorem saturationGeneratorProjection_surjective :
    Surjective (saturationGeneratorProjection (p := p) W) where
  surj x := ⟨saturationGeneratorSection e W x,
    congrArg (fun g ↦ g x) (saturationGeneratorSection_projection e W)⟩

instance saturationGeneratorProjection_etale [Etale p.left] :
    Etale (saturationGeneratorProjection (p := p) W) := by
  unfold saturationGeneratorProjection
  infer_instance

end FLT.Mazur.RelativeRelationOrbit
