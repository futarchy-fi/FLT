/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasSectionTransport
public import FLT.Mazur.RetainedLineTwistedSection

/-!
# Twisted sections retain coefficient transport

Changing the coefficient sheaf postcomposes the original direct-image map.
For retained lines this transports the actual tensor section and its full ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve DualAtlasLineQuotient ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{0}} (f : X ⟶ S) {L N : X.Modules}

/-- An actual coefficient isomorphism transports the retained tensor section. -/
lemma retainedLineSection_coefficient (c : L ≅ N) (a : Line ((pushforward f).obj L)) :
    (map c.hom (𝟙 _)).app ⊤ (retainedLineSection f L a) =
      retainedLineSection f N (a.changeAmbient ((pushforward f).mapIso c)) := by
  apply (twistedSectionPushforwardEquiv f N
    (a.changeAmbient ((pushforward f).mapIso c)).rankOne.dual).injective
  rw [retainedLineSection_map]
  change twistedSectionPushforwardEquiv f N a.rankOne.dual _ = _
  rw [twistedSectionPushforwardEquiv_naturality, retainedLineSection_map]
  change ((lineSheafBidualIso a.rankOne).inv ≫ a.inclusion) ≫ _ =
    (lineSheafBidualIso a.rankOne).inv ≫ (a.inclusion ≫ (pushforward f).map c.hom)
  exact Category.assoc _ _ _

/-- Coefficient transport preserves the full ideal of a retained section. -/
lemma retainedLineSection_coefficient_zeroIdeal (hL : LocallyFreeRankOne L)
    (hN : LocallyFreeRankOne N) (c : L ≅ N) (a : Line ((pushforward f).obj L)) :
    lineSectionZeroIdeal (hL.tensor (a.rankOne.dual.pullback f))
        (retainedLineSection f L a) =
      lineSectionZeroIdeal (hN.tensor (a.rankOne.dual.pullback f))
        (retainedLineSection f N (a.changeAmbient ((pushforward f).mapIso c))) :=
  lineSectionZeroIdeal_eq_of_iso _ _ (congr c (Iso.refl _)) _ _
    (retainedLineSection_coefficient f c a)

end FLT.Mazur.CartierAbel
