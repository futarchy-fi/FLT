/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperUniversalDirectImageLine
public import FLT.Mazur.ProperChangedBaseCartierSections
public import FLT.Mazur.ProperRelativeCartierAtlas
public import FLT.Mazur.DualProjectiveAtlasNoetherian

/-!
# The actual universal relative Cartier section

The universal retained line is transported by the actual proper direct-image
mate. Intrinsic duality supplies its twist, and the proved chartwise criterion
constructs a regular tensor section with flat full zero divisor on the atlas.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ProperUniversalDirectImage
open FCurve LineSectionBaseChange CartierAbel LocallyFreeDualProjectiveAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyIntegral f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

local notation "M" => Functor.obj (pushforward f) L
local notation "hM" => properLinePushforward_locallyFiniteFree f L hL hV
local notation "A" => space M hM
local notation "π" => projection M hM
local notation "p" => Limits.pullback.fst f π
local notation "q" => Limits.pullback.snd f π

omit [GeometricallyIntegral f] in
/-- The original universal atlas is locally Noetherian under the family hypotheses. -/
lemma atlas_locallyNoetherian : IsLocallyNoetherian A := by
  let _ : IsLocallyNoetherian S := isLocallyNoetherian_of_isOpenImmersion S.isoSpec.hom
  exact space_isLocallyNoetherian M hM

/-- The original universal inclusion constructs an actual relative Cartier section. -/
@[irreducible] def universalRelativeSection :
    RelativeSection q ((pullback p).obj L) (hL.pullback p) := by
  letI := atlas_locallyNoetherian f L hL hV
  exact (splitDirectImageOfLine q _ (line f L hL hV)).toChangedBaseRelative
    (IsPullback.of_hasPullback f π) L hL hV

/-- The universal twist is the intrinsic dual of the retained universal source line. -/
lemma universalRelativeSection_baseLine :
    (universalRelativeSection f L hL hV).val.baseLine =
      (splitDirectImageOfLine q _ (line f L hL hV)).baseLine := by
  let _ := atlas_locallyNoetherian f L hL hV
  unfold universalRelativeSection
  exact (splitDirectImageOfLine q _ (line f L hL hV)).toChangedBaseRelative_baseLine
    (IsPullback.of_hasPullback f π) L hL hV

/-- The recovered section has the original universal map, normalized by canonical biduality. -/
lemma universalRelativeSection_map :
    HEq (twistedSectionPushforwardEquiv q ((pullback p).obj L)
      (universalRelativeSection f L hL hV).val.baseLine.property
      (universalRelativeSection f L hL hV).val.section_)
      ((lineSheafBidualIso (line f L hL hV).rankOne).inv ≫
        (line f L hL hV).inclusion) := by
  let _ := atlas_locallyNoetherian f L hL hV
  unfold universalRelativeSection
  exact (splitDirectImageOfLine q _ (line f L hL hV)).toChangedBaseRelative_map
    (IsPullback.of_hasPullback f π) L hL hV

/-- The full universal zero ideal on the actual total space over the atlas. -/
@[irreducible] def universalIdeal : (Limits.pullback f π).IdealSheafData :=
  lineSectionZeroIdeal
    (twist_rankOne q ((pullback p).obj L) (hL.pullback p)
      (universalRelativeSection f L hL hV).val.baseLine)
    (universalRelativeSection f L hL hV).val.section_

/-- The constructed full zero divisor is effective Cartier and flat over the atlas. -/
theorem universalIdeal_relativeCartier :
    RelativeEffectiveCartier q (universalIdeal f L hL hV) := by
  unfold universalIdeal
  exact relativeSection_cartier q _ _ (universalRelativeSection f L hL hV)

/-- The universal tensor section is regular on the actual total space. -/
theorem universalSection_regular :
    Mono (globalSectionHom _ (universalRelativeSection f L hL hV).val.section_) :=
  (universalRelativeSection f L hL hV).val.regular

/-- The full universal divisor stays relative Cartier on every test scheme over the atlas. -/
theorem universalIdeal_baseChange {T : Scheme.{0}} (a : T ⟶ A) :
    RelativeEffectiveCartier (Limits.pullback.snd q a)
      ((universalIdeal f L hL hV).comap (Limits.pullback.fst q a)) :=
  relativeCartierBaseChange q a _ (universalIdeal_relativeCartier f L hL hV)

end FLT.Mazur.ProperUniversalDirectImage
