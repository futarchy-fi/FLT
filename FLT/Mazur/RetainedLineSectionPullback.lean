/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasSectionTransport
public import FLT.Mazur.RetainedLineTwistedSection
public import FLT.Mazur.LineSheafBidualPullback
public import FLT.Mazur.TwistedSectionBaseChangeRegularity

/-!
# Geometric pullback of retained line sections

The actual tensor pullback, square comparison and canonical dual comparison
transport the retained section to the section of the base-changed inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve DualAtlasLineQuotient ModuleSheafTensor DirectImageBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
  moduleSheafDualPullbackIso ModuleLineBundleTensorPullback.tensorIso
variable {P X T S : Scheme.{0}}
  (p : P ⟶ X) (q : P ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (w : q ≫ g = p ≫ f) (L : X.Modules)

/-- Pulling a retained section agrees with pulling its original direct-image inclusion. -/
lemma retainedLineSection_pullback (a : Line ((pushforward f).obj L))
    (e : (pullback g).obj ((pushforward f).obj L) ≅
      (pushforward q).obj ((pullback p).obj L))
    (he : e.hom = comparison p q f g w L) :
    (map (𝟙 ((pullback p).obj L)) 
      ((pullback q).map (moduleSheafDualPullbackIso g a.rankOne).hom)).app ⊤
        (TwistedSectionBaseChangeRegularity.section_ p q f g w L
          (retainedLineSection f L a)) =
      retainedLineSection q ((pullback p).obj L) ((a.baseChange g).changeAmbient e) := by
  apply (twistedSectionPushforwardEquiv q _
    ((a.baseChange g).changeAmbient e).rankOne.dual).injective
  rw [retainedLineSection_map]
  change twistedSectionPushforwardEquiv q _ (a.rankOne.pullback g).dual _ = _
  rw [twistedSectionPushforwardEquiv_baseLineIso q _
    (moduleSheafDualPullbackIso g a.rankOne)
    (a.rankOne.dual.pullback g) (a.rankOne.pullback g).dual,
    TwistedSectionBaseChangeRegularity.section_map p q f g w L a.rankOne.dual,
    retainedLineSection_map, Functor.map_comp]
  change _ = (lineSheafBidualIso (a.rankOne.pullback g)).inv ≫
    (pullback g).map a.inclusion ≫ e.hom
  rw [he]
  have hn := lineBidual_pullback_inv_normalized g a.rankOne
  simp only [moduleSheafDualIso, ← Category.assoc] at hn ⊢
  rw [hn]

end FLT.Mazur.CartierAbel
