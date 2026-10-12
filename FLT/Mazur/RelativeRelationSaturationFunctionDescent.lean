/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationSaturationComparison

/-!
# Effective descent from a generating open to its invariant saturation

Original compatible functions on the generator extend uniquely to invariant
functions on the saturation. The multiplicative comparison is actual restriction;
no affineness of the saturation or quotient is assumed or concluded.
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
local notation "Z" => Subtype.val (saturateOpen e hq W)
local notation "g" => saturationCover e hq W
local notation "h" => saturationGeneratorProjection (p := p) W
local notation "j" => Scheme.homOfLE _ (le_saturateOpen e hq W)
local notation "P" => saturatedRelationFst e hq W
local notation "Q" => saturatedRelationSnd e hq W
local notation "r" => SchemeRelationRestriction.fst p.left q.left W.ι
local notation "s" => SchemeRelationRestriction.snd p.left q.left W.ι

/-- A descended function is invariant under every original arrow in the saturation. -/
theorem saturationDescended_invariant [Etale q.left]
    (v : Γ(W.toScheme, ⊤)) (t : Γ((Z).toScheme, ⊤))
    (ht : (g).appTop t = (h).appTop v) : t ∈ compatibleFunctions P Q := by
  apply appTop_injective (pullback.snd g P)
  change (pullback.snd g P ≫ P).appTop t = (pullback.snd g P ≫ Q).appTop t
  rw [← pullback.condition, ← saturationAction_cover]
  change (pullback.fst g P).appTop ((g).appTop t) =
    (saturationAction e hq W).appTop ((g).appTop t)
  rw [ht]
  change (pullback.fst g P ≫ h).appTop v = (saturationAction e hq W ≫ h).appTop v
  rw [saturationAction_generator]

/-- The original invariant equation computes cover pullback from the generator restriction. -/
theorem saturationInvariant_cover (v : compatibleFunctions P Q) :
    (g).appTop v.val = (h).appTop ((j).appTop v.val) := by
  have hv := congrArg (saturationSpanRelation e hq W).appTop v.property
  change (saturationSpanRelation e hq W ≫ P).appTop v.val =
    (saturationSpanRelation e hq W ≫ Q).appTop v.val at hv
  rw [saturationSpanRelation_fst, saturationSpanRelation_snd] at hv
  exact hv.symm

/-- Actual restriction of original invariant functions to the full generator relation. -/
def saturationFunctionRestriction : compatibleFunctions P Q →+* compatibleFunctions r s :=
  relationFunctionPullback j (saturationRestrictionRelation e hq W)
    (saturationRestrictionRelation_fst e hq W) (saturationRestrictionRelation_snd e hq W)

/-- Generator restriction detects invariant functions through the original endpoint cover. -/
theorem saturationFunctionRestriction_injective [Etale q.left] :
    Function.Injective (saturationFunctionRestriction e hq W) := by
  intro v w hvw
  apply Subtype.ext
  apply appTop_injective g
  rw [saturationInvariant_cover, saturationInvariant_cover]
  exact congrArg (h).appTop (congrArg Subtype.val hvw)

/-- Every compatible generator function is the restriction of an invariant function. -/
theorem saturationFunctionRestriction_surjective [Etale q.left] :
    Function.Surjective (saturationFunctionRestriction e hq W) := by
  intro v
  obtain ⟨t, ht, _⟩ := saturationGenerator_descends e hq W v
  exact ⟨⟨t, saturationDescended_invariant e hq W v.val t ht⟩,
    Subtype.ext (saturationGenerator_recovers e hq W v.val t ht)⟩

/-- Effective descent identifies the actual invariant rings multiplicatively. -/
def saturationFunctionRingEquiv [Etale q.left] :
    compatibleFunctions P Q ≃+* compatibleFunctions r s :=
  RingEquiv.ofBijective (saturationFunctionRestriction e hq W)
    ⟨saturationFunctionRestriction_injective e hq W,
      saturationFunctionRestriction_surjective e hq W⟩

/-- The equivalence retains the original inclusion, rather than choosing coordinates. -/
theorem saturationFunctionRingEquiv_val [Etale q.left] (v : compatibleFunctions P Q) :
    (saturationFunctionRingEquiv e hq W v).val = (j).appTop v.val := rfl

end FLT.Mazur.RelativeRelationOrbit
