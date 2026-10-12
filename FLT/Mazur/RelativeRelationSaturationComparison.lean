/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationSaturationAction

/-!
# Original relation comparisons for the generating open

The full generator relation maps to the saturated relation. The original cover
arrow domain does too, retaining both its generating and saturated endpoints.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (hq : IsOpenMap q.left)
  (W : U.left.Opens)
local notation "Z" => Subtype.val (saturateOpen e hq W)
local notation "j" => Scheme.homOfLE _ (le_saturateOpen e hq W)
local notation "P" => saturatedRelationFst e hq W
local notation "Q" => saturatedRelationSnd e hq W
local notation "r" => SchemeRelationRestriction.fst p.left q.left W.ι
local notation "s" => SchemeRelationRestriction.snd p.left q.left W.ι

/-- The saturated relation domain is the original first-endpoint pullback. -/
theorem saturatedRelation_isPullback :
    IsPullback (p.left ⁻¹ᵁ Z).ι P p.left (Z).ι :=
  saturationGenerator_isPullback Z

/-- The original generator relation maps to the original saturated relation. -/
def saturationRestrictionRelation : SchemeRelationRestriction.doubleDomain p.left q.left W.ι ⟶
    (p.left ⁻¹ᵁ Z).toScheme :=
  (saturatedRelation_isPullback e hq W).lift
    (SchemeRelationRestriction.arrow p.left q.left W.ι) (r ≫ j) (by
      rw [Category.assoc, Scheme.homOfLE_ι, SchemeRelationRestriction.arrow_fst])

@[reassoc]
theorem saturationRestrictionRelation_original :
    saturationRestrictionRelation e hq W ≫ (p.left ⁻¹ᵁ Z).ι =
      SchemeRelationRestriction.arrow p.left q.left W.ι :=
  (saturatedRelation_isPullback e hq W).lift_fst _ _ _

@[reassoc]
theorem saturationRestrictionRelation_fst :
    saturationRestrictionRelation e hq W ≫ P = r ≫ j :=
  (saturatedRelation_isPullback e hq W).lift_snd _ _ _

@[reassoc]
theorem saturationRestrictionRelation_snd :
    saturationRestrictionRelation e hq W ≫ Q = s ≫ j := by
  apply (cancel_mono (Z).ι).mp
  rw [Category.assoc, saturatedRelationSnd, Scheme.Hom.resLE_comp_ι,
    ← Category.assoc, saturationRestrictionRelation_original,
    SchemeRelationRestriction.arrow_snd, Category.assoc, Scheme.homOfLE_ι]

/-- Inclusion of the original cover arrow domain in the saturated relation domain. -/
def saturationSpanRelation : (p.left ⁻¹ᵁ W).toScheme ⟶ (p.left ⁻¹ᵁ Z).toScheme :=
  Scheme.homOfLE _ (p.left.preimage_mono (le_saturateOpen e hq W))

@[reassoc]
theorem saturationSpanRelation_fst : saturationSpanRelation e hq W ≫ P =
    saturationGeneratorProjection (p := p) W ≫ j := by
  apply (cancel_mono (Z).ι).mp
  rw [Category.assoc, saturatedRelationFst, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    saturationSpanRelation, Scheme.homOfLE_ι, Category.assoc, Scheme.homOfLE_ι,
    saturationGeneratorProjection, Scheme.Hom.resLE_comp_ι]

@[reassoc]
theorem saturationSpanRelation_snd : saturationSpanRelation e hq W ≫ Q =
    saturationCover e hq W := by
  apply (cancel_mono (Z).ι).mp
  rw [Category.assoc, saturatedRelationSnd, Scheme.Hom.resLE_comp_ι,
    ← Category.assoc, saturationSpanRelation, Scheme.homOfLE_ι, saturationCover_comp_ι]

end FLT.Mazur.RelativeRelationOrbit
