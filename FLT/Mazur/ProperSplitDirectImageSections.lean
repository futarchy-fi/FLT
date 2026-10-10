/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperSectionSplittingCriterion

/-!
# Relative Cartier sections and retained split direct-image maps

A locally split map from the dual of a retained base line constructs a
relative Cartier section by the proved affine-base criterion. For proper
surjective families the constructions are inverse on the original data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve SplitLineAffineNeighborhood
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)

/-- A base line and an actual locally split map from its dual to the direct image. -/
structure SplitDirectImageSection where
  /-- The retained twisting line. -/
  baseLine : SchemePicard.LineBundle S
  /-- Its actual dual-line inclusion. -/
  map : moduleSheafDual baseLine.val ⟶ (pushforward f).obj L
  /-- Local retractions on the base. -/
  locallySplit : LocallySplit map

variable [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsProper f] [Flat f]
  [GeometricallyIntegral f] (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (LineSectionBaseChange.residueAlgebraFiberLine f L z) (n + 1)))

/-- Inverting tensor duality constructs the original relative Cartier section. -/
def SplitDirectImageSection.toRelative (a : SplitDirectImageSection f L) :
    RelativeSection f L hL :=
  ProperSectionSplittingCriterion.relativeSection f L hL hV a.baseLine.property
    ((twistedSectionPushforwardEquiv f L a.baseLine.property).symm a.map)
    (by simpa only [Equiv.apply_symm_apply] using a.locallySplit)

/-- The recovered original tensor section corresponds to the original direct-image map. -/
lemma SplitDirectImageSection.toRelative_map (a : SplitDirectImageSection f L) :
    ((a.toRelative f L hL hV).val.toDirectImage f L).map = a.map :=
  (twistedSectionPushforwardEquiv f L a.baseLine.property).apply_symm_apply a.map

variable [Surjective f]

/-- Relative Cartier regularity supplies local retractions of the retained dual-line map. -/
def RelativeSection.toSplitDirectImage (s : RelativeSection f L hL) :
    SplitDirectImageSection f L where
  baseLine := s.val.baseLine
  map := (s.val.toDirectImage f L).map
  locallySplit := relativeSection_proper_directImage_locallySplit f L hL hV s

/-- Both conversions preserve the entire original relative section. -/
lemma toRelative_toSplitDirectImage (s : RelativeSection f L hL) :
    (s.toSplitDirectImage f L hL hV).toRelative f L hL hV = s := by
  apply Subtype.ext
  rcases s with ⟨⟨B, s, hm⟩, hflat⟩
  change (⟨B, (twistedSectionPushforwardEquiv f L B.property).symm
    (twistedSectionPushforwardEquiv f L B.property s), _⟩ : TwistedSection f L) = _
  simp only [Equiv.symm_apply_apply]

/-- Both conversions preserve the base line and its original direct-image inclusion. -/
lemma toSplitDirectImage_toRelative (a : SplitDirectImageSection f L) :
    (a.toRelative f L hL hV).toSplitDirectImage f L hL hV = a := by
  rcases a with ⟨B, a, ha⟩
  change (⟨B, twistedSectionPushforwardEquiv f L B.property
    ((twistedSectionPushforwardEquiv f L B.property).symm a), _⟩ :
      SplitDirectImageSection f L) = _
  simp only [Equiv.apply_symm_apply]

/-- The equivalence retains the twisting line and the actual section, before any quotient. -/
def relativeSplitDirectImageEquiv :
    RelativeSection f L hL ≃ SplitDirectImageSection f L where
  toFun := RelativeSection.toSplitDirectImage f L hL hV
  invFun := SplitDirectImageSection.toRelative f L hL hV
  left_inv := toRelative_toSplitDirectImage f L hL hV
  right_inv := toSplitDirectImage_toRelative f L hL hV

end FLT.Mazur.CartierAbel
