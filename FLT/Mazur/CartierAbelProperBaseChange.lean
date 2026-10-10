/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierAbelDirectImageBaseChange
public import FLT.Mazur.ProperLinePushforwardMate

/-!
# Proper base change of Cartier direct-image sections

Under residue-cohomology vanishing, the compatibility for the independently
pulled Cartier section uses the original proper direct-image isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.CartierAbel
open FCurve LineSectionBaseChange Chow
attribute [local irreducible] twistedSectionPushforwardEquiv lineHomSectionEquiv
  moduleSheafDualPullbackIso
variable {X S T : Scheme.{0}} [IsAffine S] [IsAffine T]
  [IsNoetherianRing Γ(S, ⊤)] (f : X ⟶ S) (g : T ⟶ S)
  [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

/-- The actual pulled Cartier map uses the independently constructed proper base-change iso. -/
lemma pulledTwistedSection_directImage_proper (s : RelativeSection f L hL) :
    ((pulledTwistedSection f g L hL s).toDirectImage (Limits.pullback.snd f g) _).map =
      (moduleSheafDualPullbackIso g s.val.baseLine.property).inv ≫
        (pullback g).map (s.val.toDirectImage f L).map ≫
          (properLinePushforwardBaseChangeIso (IsPullback.of_hasPullback f g) L hL hV).hom := by
  rw [properLinePushforwardBaseChangeIso_eq_mate]
  exact pulledTwistedSection_directImage_baseChange f g L hL s

/-- Inverting the actual comparisons recovers the pullback of the original Cartier map. -/
lemma pullback_directImage_eq_pulled (s : RelativeSection f L hL) :
    (pullback g).map (s.val.toDirectImage f L).map =
      (moduleSheafDualPullbackIso g s.val.baseLine.property).hom ≫
        ((pulledTwistedSection f g L hL s).toDirectImage (Limits.pullback.snd f g) _).map ≫
          (properLinePushforwardBaseChangeIso (IsPullback.of_hasPullback f g) L hL hV).inv := by
  rw [pulledTwistedSection_directImage_proper f g L hL hV]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.CartierAbel
