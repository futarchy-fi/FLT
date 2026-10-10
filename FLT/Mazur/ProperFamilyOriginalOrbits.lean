/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilySectionOrbits

/-!
# Original twisting-line meaning of the represented family orbits

The retained-source relation of the actual representing atlas agrees with
isomorphisms of the original base twists carrying the original sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open ProperFamilyAtlas FCurve LineSectionBaseChange DualAtlasLineQuotient
open LocallyFreeDualProjectiveAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
attribute [local irreducible] ProperFamilyAtlas.morphism
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.space
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.projection
variable {P X T S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] [GeometricallyIntegral f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

local notation "M" => Functor.obj (pushforward f) L
local notation "hM" => properLinePushforward_locallyFiniteFree f L hL hV
local notation "N" => Functor.obj (pushforward q) (Functor.obj (pullback p) L)
local notation "e" => properLineArbitraryBaseChangeIso h L hL hV


local notation "R" => RelativeSection q (Functor.obj (pullback p) L) (hL.pullback p)

include h hV in
/-- The original relative section has its original locally split direct-image map. -/
lemma familyOriginalSection_locallySplit (s : R) :
    SplitLineAffineNeighborhood.LocallySplit
      (twistedSectionPushforwardEquiv q ((pullback p).obj L)
        s.val.baseLine.property s.val.section_) :=
  (s.toFamilySplitDirectImage h L hL hV).locallySplit

/-- The retained family line is the original dual twisting line with its original map. -/
lemma familyLine_eq_original (s : R) :
    s.familyLine h L hL hV = originalTwistLine q ((pullback p).obj L)
      s.val.baseLine s.val.section_ (familyOriginalSection_locallySplit h L hL hV s) := rfl

/-- The family retained-line relation uses precisely the original twisting lines and sections. -/
lemma familyBaseLineSetoid_iff_iso (s t : R) :
    (familyBaseLineSetoid h L hL hV).r s t ↔
      originalTwistIsoRelation q ((pullback p).obj L) s.val t.val := by
  change (lineSetoid N).r (s.familyLine h L hL hV) (t.familyLine h L hL hV) ↔ _
  have he := congrArg₂ (fun a b : Line N ↦ (lineSetoid N).r a b)
    (familyLine_eq_original h L hL hV s) (familyLine_eq_original h L hL hV t)
  exact (Iff.of_eq he).trans (originalTwistLine_rel_iff q ((pullback p).obj L) s.val t.val
    (familyOriginalSection_locallySplit h L hL hV s)
    (familyOriginalSection_locallySplit h L hL hV t))

end FLT.Mazur.CartierAbel
