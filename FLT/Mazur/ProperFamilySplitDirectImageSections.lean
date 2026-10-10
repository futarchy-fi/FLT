/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyOriginalZeroIdeal

/-!
# Split direct-image sections on unrestricted test families

Geometric recovery of the universal divisor constructs the original relative
section without a Noetherian assumption on the test base. The construction
retains the independently supplied twist and the actual direct-image map.
The arbitrary-base mate supplies finite local freeness for the converse.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve LineSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
variable {P X T S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] [GeometricallyIntegral f]
  (h : IsPullback p q f g) (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

/-- A locally split original map constructs a relative section on any test base. -/
@[irreducible] def SplitDirectImageSection.toFamilyRelative
    (a : SplitDirectImageSection q ((pullback p).obj L)) :
    RelativeSection q ((pullback p).obj L) (hL.pullback p) := by
  let s := (twistedSectionPushforwardEquiv q ((pullback p).obj L) a.baseLine.property).symm
    a.map
  have hs : SplitLineAffineNeighborhood.LocallySplit
      (twistedSectionPushforwardEquiv q ((pullback p).obj L) a.baseLine.property s) := by
    simpa only [s, Equiv.apply_symm_apply] using a.locallySplit
  exact ⟨⟨a.baseLine, s,
    ProperFamilyAtlas.originalSection_regular h L hL hV a.baseLine s hs⟩,
      (ProperFamilyAtlas.originalSection_relativeCartier h L hL hV a.baseLine s hs).2⟩

/-- Reconstruction retains the independently supplied original twisting line. -/
lemma SplitDirectImageSection.toFamilyRelative_baseLine
    (a : SplitDirectImageSection q ((pullback p).obj L)) :
    (a.toFamilyRelative h L hL hV).val.baseLine = a.baseLine := by
  unfold SplitDirectImageSection.toFamilyRelative
  rfl

/-- Reconstruction retains the actual map from the original dual twisting line. -/
lemma SplitDirectImageSection.toFamilyRelative_map
    (a : SplitDirectImageSection q ((pullback p).obj L)) :
    HEq (twistedSectionPushforwardEquiv q ((pullback p).obj L)
      (a.toFamilyRelative h L hL hV).val.baseLine.property
      (a.toFamilyRelative h L hL hV).val.section_) a.map := by
  unfold SplitDirectImageSection.toFamilyRelative
  exact heq_of_eq
    ((twistedSectionPushforwardEquiv q _ a.baseLine.property).apply_symm_apply a.map)

omit [GeometricallyIntegral f] in
include h hL hV in
/-- The actual direct image on the arbitrary test base is locally finite free. -/
lemma familyDirectImage_locallyFiniteFree :
    LocallyFiniteFree ((pushforward q).obj ((pullback p).obj L)) := by
  exact ((properLinePushforward_locallyFiniteFree f L hL hV).pullback g).of_iso
    (properLineArbitraryBaseChangeIso h L hL hV)

/-- A relative section yields its original locally split direct-image map on any test base. -/
def RelativeSection.toFamilySplitDirectImage
    (s : RelativeSection q ((pullback p).obj L) (hL.pullback p)) :
    SplitDirectImageSection q ((pullback p).obj L) where
  baseLine := s.val.baseLine
  map := (s.val.toDirectImage q ((pullback p).obj L)).map
  locallySplit := by
    let _ : Surjective q := MorphismProperty.of_isPullback h inferInstance
    exact relativeSection_directImage_locallySplit q ((pullback p).obj L) (hL.pullback p)
      (familyDirectImage_locallyFiniteFree h L hL hV) s

/-- The round trip preserves the full original relative section, including its twist. -/
lemma toFamilyRelative_toFamilySplitDirectImage
    (s : RelativeSection q ((pullback p).obj L) (hL.pullback p)) :
    (s.toFamilySplitDirectImage h L hL hV).toFamilyRelative h L hL hV = s := by
  apply Subtype.ext
  rcases s with ⟨⟨B, s, hm⟩, hflat⟩
  unfold SplitDirectImageSection.toFamilyRelative RelativeSection.toFamilySplitDirectImage
  change (⟨B, (twistedSectionPushforwardEquiv q ((pullback p).obj L) B.property).symm
    (twistedSectionPushforwardEquiv q ((pullback p).obj L) B.property s), _⟩ :
      TwistedSection q ((pullback p).obj L)) = _
  simp only [Equiv.symm_apply_apply]

/-- The round trip preserves the full original split direct-image datum. -/
lemma toFamilySplitDirectImage_toFamilyRelative
    (a : SplitDirectImageSection q ((pullback p).obj L)) :
    (a.toFamilyRelative h L hL hV).toFamilySplitDirectImage h L hL hV = a := by
  rcases a with ⟨B, a, ha⟩
  unfold RelativeSection.toFamilySplitDirectImage SplitDirectImageSection.toFamilyRelative
  change (⟨B, twistedSectionPushforwardEquiv q ((pullback p).obj L) B.property
    ((twistedSectionPushforwardEquiv q ((pullback p).obj L) B.property).symm a), _⟩ :
      SplitDirectImageSection q ((pullback p).obj L)) = _
  simp only [Equiv.apply_symm_apply]

/-- Relative sections and actual split dual-line maps agree on unrestricted test bases. -/
def familyRelativeSplitDirectImageEquiv :
    RelativeSection q ((pullback p).obj L) (hL.pullback p) ≃
      SplitDirectImageSection q ((pullback p).obj L) where
  toFun := RelativeSection.toFamilySplitDirectImage h L hL hV
  invFun := SplitDirectImageSection.toFamilyRelative h L hL hV
  left_inv := toFamilyRelative_toFamilySplitDirectImage h L hL hV
  right_inv := toFamilySplitDirectImage_toFamilyRelative h L hL hV

include h hL hV in
/-- Local splitting is exactly the original regular relative Cartier condition. -/
theorem familySection_locallySplit_iff (B : SchemePicard.LineBundle T)
    (s : Γ(twist q ((pullback p).obj L) B, ⊤)) :
    SplitLineAffineNeighborhood.LocallySplit
        (twistedSectionPushforwardEquiv q ((pullback p).obj L) B.property s) ↔
      Mono (globalSectionHom _ s) ∧ RelativeEffectiveCartier q
        (lineSectionZeroIdeal (twist_rankOne q ((pullback p).obj L) (hL.pullback p) B) s) := by
  constructor
  · intro hs
    exact ⟨ProperFamilyAtlas.originalSection_regular h L hL hV B s hs,
      ProperFamilyAtlas.originalSection_relativeCartier h L hL hV B s hs⟩
  · rintro ⟨hm, hC⟩
    let t : RelativeSection q ((pullback p).obj L) (hL.pullback p) := ⟨⟨B, s, hm⟩, hC.2⟩
    exact (t.toFamilySplitDirectImage h L hL hV).locallySplit

end FLT.Mazur.CartierAbel
