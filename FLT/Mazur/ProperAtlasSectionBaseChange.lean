/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperAtlasAbelEquivalence
public import FLT.Mazur.DualAtlasSectionTransport
public import FLT.Mazur.CartierAbelProperBaseChange

/-!
# Geometric base change of proper direct-image atlas sections

Pull back the geometric atlas section using its cartesian square, then
transport along the independently constructed proper direct-image comparison.
The original Cartier direct-image inclusions satisfy the corresponding
comparison square. Full naturality of the Abel equivalence is separate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve LineSectionBaseChange DualAtlasLineQuotient
attribute [local irreducible] twistedSectionPushforwardEquiv moduleSheafDualPullbackIso
  properLinePushforwardBaseChangeIso
  LocallySplitLineAtlasSection.morphism sectionChangeAmbient
  DualAtlasLineQuotient.sectionBaseChange toSection
variable {X S T : Scheme.{0}} (f : X ⟶ S) (g : T ⟶ S) (L : X.Modules)
  [IsAffine S] [IsAffine T] [IsNoetherianRing Γ(S, ⊤)] [IsNoetherianRing Γ(T, ⊤)]
  [IsProper f] [Flat f] [Surjective f] [GeometricallyIntegral f]
  (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))
  (hW : ∀ (z : PrimeSpectrum Γ(T, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine (Limits.pullback.snd f g)
      ((pullback (Limits.pullback.fst f g)).obj L) z) (n + 1)))

/-- Geometric atlas pullback followed by the actual direct-image ambient-bundle comparison. -/
@[irreducible] def properAtlasBaseChange (p : DirectImageAtlasSection f L hL hV) :
    DirectImageAtlasSection (Limits.pullback.snd f g) _
      (hL.pullback (Limits.pullback.fst f g)) hW :=
  sectionChangeAmbient
    (properLinePushforwardBaseChangeIso (IsPullback.of_hasPullback f g) L hL hV)
    ((properLinePushforward_locallyFiniteFree f L hL hV).pullback g)
    (properLinePushforward_locallyFiniteFree (Limits.pullback.snd f g) _
      (hL.pullback (Limits.pullback.fst f g)) hW)
    (DualAtlasLineQuotient.sectionBaseChange g
      (properLinePushforward_locallyFiniteFree f L hL hV) p)

omit [Surjective f] [GeometricallyIntegral f] in
/-- Geometric base change on any retained original line inclusion. -/
lemma properAtlasBaseChange_toSection
    (a : Line ((pushforward f).obj L)) :
    properAtlasBaseChange f g L hL hV hW
        (toSection _ (properLinePushforward_locallyFiniteFree f L hL hV) a) =
      toSection _ (properLinePushforward_locallyFiniteFree (Limits.pullback.snd f g) _
        (hL.pullback (Limits.pullback.fst f g)) hW)
        ((a.baseChange g).changeAmbient
          (properLinePushforwardBaseChangeIso (IsPullback.of_hasPullback f g) L hL hV)) := by
  unfold properAtlasBaseChange
  rw [sectionBaseChange_toSection, sectionChangeAmbient_toSection]

omit [Surjective f] [GeometricallyIntegral f] [IsNoetherianRing Γ(T, ⊤)] in
/-- The original dual-pullback comparison preserves the transported direct-image inclusion. -/
lemma properAtlasBaseChange_inclusion (s : RelativeSection f L hL) :
    (moduleSheafDualPullbackIso g s.val.baseLine.property).hom ≫
      ((pulledTwistedSection f g L hL s).toDirectImage (Limits.pullback.snd f g) _).map =
        (pullback g).map (s.val.toDirectImage f L).map ≫
          (properLinePushforwardBaseChangeIso (IsPullback.of_hasPullback f g) L hL hV).hom := by
  rw [pulledTwistedSection_directImage_proper f g L hL hV]
  simp only [Iso.hom_inv_id_assoc]


end FLT.Mazur.CartierAbel
