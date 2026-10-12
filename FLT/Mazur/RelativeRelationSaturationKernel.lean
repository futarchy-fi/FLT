/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationArrowCalculus
public import FLT.Mazur.SchemeRelationDoubleRestriction
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Original relation witnesses for the saturation cover's kernel pair

Dividing two arrows with the same saturated endpoint produces a full restricted
relation arrow between their generating endpoints. Compatible generator functions
therefore descend through the original etale cover of the saturation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeRelationOrbit
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (hq : IsOpenMap q.left)
  (W : U.left.Opens)
local notation "g" => saturationCover e hq W
local notation "h" => saturationGeneratorProjection (p := p) W

/-- The original arrows of a saturation kernel pair have the same second endpoint. -/
theorem saturationKernel_endpoint :
    (pullback.fst g g ≫ (p.left ⁻¹ᵁ W).ι) ≫ q.left =
      (pullback.snd g g ≫ (p.left ⁻¹ᵁ W).ι) ≫ q.left := by
  rw [Category.assoc, Category.assoc, ← saturationCover_comp_ι e hq W,
    ← Category.assoc, ← Category.assoc, pullback.condition]

/-- The kernel pair maps to the full two-endpoint restriction of the original relation. -/
def saturationKernelRelation : pullback g g ⟶
    SchemeRelationRestriction.doubleDomain p.left q.left W.ι :=
  SchemeRelationRestriction.lift p.left q.left W.ι
    (divideOriginal e (pullback.fst g g ≫ (p.left ⁻¹ᵁ W).ι) (pullback.snd g g ≫ (p.left ⁻¹ᵁ W).ι)
      (saturationKernel_endpoint e hq W))
    (pullback.fst g g ≫ h) (pullback.snd g g ≫ h)
    (by rw [divideOriginal_fst, Category.assoc, Category.assoc,
          saturationGeneratorProjection, Scheme.Hom.resLE_comp_ι])
    (by rw [divideOriginal_snd, Category.assoc, Category.assoc,
          saturationGeneratorProjection, Scheme.Hom.resLE_comp_ι])

@[reassoc]
theorem saturationKernelRelation_fst : saturationKernelRelation e hq W ≫
    SchemeRelationRestriction.fst p.left q.left W.ι = pullback.fst g g ≫ h :=
  SchemeRelationRestriction.lift_fst _ _ _ _ _ _ _ _

@[reassoc]
theorem saturationKernelRelation_snd : saturationKernelRelation e hq W ≫
    SchemeRelationRestriction.snd p.left q.left W.ι = pullback.snd g g ≫ h :=
  SchemeRelationRestriction.lift_snd _ _ _ _ _ _ _ _

/-- Full original relation compatibility implies compatibility on the actual cover kernel pair. -/
theorem saturationGenerator_kernel_compatible
    (s : compatibleFunctions (SchemeRelationRestriction.fst p.left q.left W.ι)
      (SchemeRelationRestriction.snd p.left q.left W.ι)) :
    (pullback.fst g g).appTop ((h).appTop s.val) =
      (pullback.snd g g).appTop ((h).appTop s.val) := by
  have hs := congrArg (saturationKernelRelation e hq W).appTop s.property
  change (saturationKernelRelation e hq W ≫ _).appTop s.val =
    (saturationKernelRelation e hq W ≫ _).appTop s.val at hs
  rw [saturationKernelRelation_fst, saturationKernelRelation_snd] at hs
  exact hs

/-- Every original compatible generator function has a unique descent along the endpoint cover. -/
theorem saturationGenerator_descends [Etale q.left]
    (s : compatibleFunctions (SchemeRelationRestriction.fst p.left q.left W.ι)
      (SchemeRelationRestriction.snd p.left q.left W.ι)) :
    ∃! t : Γ((saturateOpen e hq W).val.toScheme, ⊤), (g).appTop t = (h).appTop s.val :=
  sections_existsUnique (IsPullback.of_hasPullback g g) ((h).appTop s.val)
    (saturationGenerator_kernel_compatible e hq W s)

/-- The descended function restricts to the original generator function via reflexivity. -/
theorem saturationGenerator_recovers (s : Γ(W.toScheme, ⊤))
    (t : Γ((saturateOpen e hq W).val.toScheme, ⊤)) (ht : (g).appTop t = (h).appTop s) :
    (Scheme.homOfLE _ (le_saturateOpen e hq W)).appTop t = s := by
  have hs := congrArg (saturationGeneratorSection e W).appTop ht
  change (saturationGeneratorSection e W ≫ g).appTop t =
    (saturationGeneratorSection e W ≫ h).appTop s at hs
  rw [saturationGeneratorSection_cover, saturationGeneratorSection_projection] at hs
  simpa only [Scheme.Hom.id_appTop, ConcreteCategory.id_apply] using hs

end FLT.Mazur.RelativeRelationOrbit
