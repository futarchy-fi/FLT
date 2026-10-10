/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierAbelSquareComparison
public import FLT.Mazur.TwistedSectionBaseChange

/-!
# Base change of the actual Cartier direct-image representative

The direct image of the independently pulled Cartier section is the original
map pulled along the base and composed with the actual Beck-Chevalley mate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.CartierAbel
open FCurve
attribute [local irreducible] ModuleSheafTensor.tensor ModuleLineBundleTensorPullback.tensorIso
attribute [local irreducible] twistedSectionPushforwardEquiv lineHomSectionEquiv
  moduleSheafDualPullbackIso
variable {X S T : Scheme.{0}} (f : X ⟶ S) (g : T ⟶ S)
  (L : X.Modules) (hL : LocallyFreeRankOne L)

/-- The actual pulled Cartier section represents base change of its original direct-image map. -/
lemma pulledTwistedSection_directImage_baseChange (s : RelativeSection f L hL) :
    ((pulledTwistedSection f g L hL s).toDirectImage (Limits.pullback.snd f g) _).map =
      (moduleSheafDualPullbackIso g s.val.baseLine.property).inv ≫
        (pullback g).map (s.val.toDirectImage f L).map ≫
          DirectImageBaseChange.comparison (Limits.pullback.fst f g)
            (Limits.pullback.snd f g) f g Limits.pullback.condition.symm L := by
  change twistedSectionPushforwardEquiv (Limits.pullback.snd f g)
    ((pullback (Limits.pullback.fst f g)).obj L) (s.val.baseLine.property.pullback g)
    (pulledTwistedSection f g L hL s).section_ = _
  rw [pulledTwistedSection_square_section]
  exact twistedSectionPushforwardEquiv_baseChange (Limits.pullback.fst f g)
    (Limits.pullback.snd f g) f g Limits.pullback.condition.symm L
    s.val.baseLine.property s.val.section_

/-- The pulled original direct-image map is nonzero on every nonempty fiber. -/
theorem relativeSection_pullback_directImage_ne_zero
    [Nonempty (Limits.pullback f g : Scheme)] (s : RelativeSection f L hL) :
    (pullback g).map (s.val.toDirectImage f L).map ≠ 0 := by
  intro h
  have hn := relativeSection_pulled_directImage_ne_zero f L hL g s
  apply hn
  rw [pulledTwistedSection_directImage_baseChange, h, Limits.zero_comp, Limits.comp_zero]

end FLT.Mazur.CartierAbel
