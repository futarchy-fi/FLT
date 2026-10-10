/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierAbelDirectImageSections
public import FLT.Mazur.CartierAbelTwistBaseChange
public import FLT.Mazur.TwistedSectionIntegralCriterion

/-!
# Nonvanishing on the actual fibers of relative Cartier sections

Every nonempty base change of a relative Cartier section has a nonzero
corresponding direct-image morphism. In particular this applies to integral
geometric fibers. The section is the independent geometric pullback from the
Cartier construction, including the actual tensor and cartesian-square maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve
variable {X S T : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)

/-- A regular twisted section on a nonempty space gives a nonzero actual direct-image map. -/
theorem TwistedSection.directImage_ne_zero [Nonempty X] (s : TwistedSection f L) :
    (s.toDirectImage f L).map ≠ 0 := by
  exact (twistedSectionPushforwardEquiv_ne_zero_iff f L
    s.baseLine.property s.section_).mpr (globalSection_ne_zero_of_mono _ s.section_)

variable (hL : LocallyFreeRankOne L) (g : T ⟶ S)

/-- On any nonempty base change, the independently pulled section gives a nonzero map. -/
theorem relativeSection_pulled_directImage_ne_zero
    [Nonempty (Limits.pullback f g : Scheme)]
    (s : RelativeSection f L hL) :
    ((pulledTwistedSection f g L hL s).toDirectImage (Limits.pullback.snd f g) _).map ≠ 0 :=
  TwistedSection.directImage_ne_zero _ _ _

include hL in
/-- The actual pulled section and its direct-image morphism satisfy the integral criterion. -/
theorem integral_pulledSection_regular_iff [IsIntegral (Limits.pullback f g)]
    (B : SchemePicard.LineBundle S)
    (s : Γ(twist (Limits.pullback.snd f g) ((pullback (Limits.pullback.fst f g)).obj L)
      (pulledBaseLine g B), ⊤)) :
    Mono (globalSectionHom _ s) ↔
      twistedSectionPushforwardEquiv (Limits.pullback.snd f g)
        ((pullback (Limits.pullback.fst f g)).obj L) (B.property.pullback g) s ≠ 0 :=
  integral_twistedSection_regular_iff _ _ (hL.pullback (Limits.pullback.fst f g))
    (B.property.pullback g) s

/-- The direct-image representative after base change cuts out the original pulled ideal. -/
lemma pulledDirectImage_zero (s : RelativeSection f L hL) :
    (DirectImageSection.toFiber (Limits.pullback.snd f g) _
      (hL.pullback (Limits.pullback.fst f g))
      ((pulledTwistedSection f g L hL s).toDirectImage (Limits.pullback.snd f g) _)).val.val =
    (lineSectionZeroIdeal (twist_rankOne f L hL s.val.baseLine) s.val.section_).comap
      (Limits.pullback.fst f g) := by
  rw [toDirectImage_toFiber]
  exact pulledTwistedSection_zero f g L hL s

end FLT.Mazur.CartierAbel
